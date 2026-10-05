#!/usr/bin/env python3
# Copyright 2026 Pierre Senellart
# SPDX-License-Identifier: Apache-2.0
"""lax-export: publish theorems of a Lean library on the Lax Archive.

The Lax Lean Archive (https://laxarchive.org/) admits no requirement beyond
Mathlib and other Lax packages, so a submission whose proofs rest on a
library must carry a copy of what it uses. This tool carries exactly that:
the declarations in the proof-term closure of the submitted theorems, not
the modules around them, rewritten into a Lax proofs package.

Pipeline (the Lean half is Slice.lean, run with the library's own toolchain
and its built oleans):

  1. closure: the proof-term closure of the targets, every constant with its
     module and source range; generated constants (no range) are attributed
     to the declaration that generated them by stripping name components.
     The constants the library's notation-defining commands mention are fed
     back as targets, since a notation leaves no constant in a term; this
     iterates to a fixed point.
  2. commands: each module of the import closure is elaborated against its
     own imports and its commands listed with kinds and ranges; a command a
     library-defined elaborator produced is captured from the info trees.
  3. slice: a command is kept when it is scaffolding (namespace, section,
     variable, open, universe, options, notation, module docstrings) or
     declares a selected constant, or is an instance or an attributed lemma
     tactics use silently and that still elaborates; a scaffolding command
     mentioning an unselected library constant is dropped.
  4. rename: the library's namespace moves under `LaxNProofs` by a
     whole-name rewrite; constants the library declares in foreign
     namespaces are renamed per usage from the `.ilean` records, rooted
     under `LaxNProofs.Foreign.…`, with an `export` alias at the old name for
     generalized field notation; unnamed instances are named after the name
     the library's build gave them; `deriving` clauses are re-derived in a
     jump namespace.
  5. imports: an import of a dropped module is replaced by the vendored
     modules and Mathlib modules below it.
  6. layout: lakefiles, toolchain, root modules, manifest, license.

Concept files and bridge proofs are hand-written and copied in from
`--concepts` and `--bridges` (each file's `LaxN`/`LaxNProofs` placeholders
are substituted).

Usage:
  lax_export.py --library DIR --prefix NS --id N --title T --out DIR
                 --target C [--target C …] [--ref TAG]
                 [--set-option "name value"]… [--whole-modules]
                 [--concepts DIR] [--bridges DIR] [--author NAME]…

`--library` is a checkout with a completed `lake build`; `--ref` takes the
sources from that git ref instead of the working tree, which must be what
the build compiled. The `.ilean` files of that build are the parser the
rewrite relies on, so a build of other sources gives wrong positions, which
the tool detects and refuses.
"""
import argparse
import glob
import json
import os
import re
import subprocess
import sys
import tempfile
import time

import yaml
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))

MATHLIB_URL = "https://github.com/leanprover-community/mathlib4"


def git(*args, cwd=None, check=True):
    r = subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True)
    if check and r.returncode:
        sys.exit(f"git {' '.join(args)} failed in {cwd or os.getcwd()}:\n{r.stderr.strip()}")
    return r.stdout.strip()


def is_url(library):
    return bool(re.match(r"^(https?://|ssh://|git@|git://)", library)) or library.endswith(".git")


def fully_built(checkout, prefix):
    """Every module of the prefix has an olean and an ilean no older than its
    source, and Mathlib's build is there."""
    root = os.path.join(checkout, prefix)
    build = os.path.join(checkout, ".lake", "build", "lib", "lean")
    if not os.path.isdir(root) or not os.path.isdir(build):
        return False
    if not glob.glob(os.path.join(checkout, ".lake", "packages", "mathlib", ".lake", "build", "lib", "lean", "Mathlib.olean")):
        return False
    for dirpath, _, files in os.walk(root):
        for f in files:
            if not f.endswith(".lean"):
                continue
            src = os.path.join(dirpath, f)
            rel = os.path.relpath(src, checkout)[:-5]
            olean = os.path.join(build, rel + ".olean")
            ilean = os.path.join(build, rel + ".ilean")
            if not (os.path.isfile(olean) and os.path.isfile(ilean)):
                return False
            if os.path.getmtime(olean) < os.path.getmtime(src):
                return False
    return True


def resolve_library(library, ref, prefix, cache):
    """The checkout whose sources are exported and whose build is read.

    A local checkout is used as it stands when the ref (default HEAD) is its
    HEAD and it is fully built: the .ilean files are then a build of exactly
    what is exported. Otherwise the ref is cloned and built under the cache,
    at a name made of the library and the ref, so that a second export of the
    same pair finds the build in place."""
    subdir = ""
    if not is_url(library):
        library = os.path.abspath(library)
        top = git("rev-parse", "--show-toplevel", cwd=library, check=False)
        if not top:
            sys.exit(f"{library} is not inside a git checkout")
        subdir = os.path.relpath(library, top)          # the library may be a folder of a repository
        head = git("rev-parse", "--verify", "HEAD", cwd=library, check=False)
        if not head:
            # a repository without a commit yet: only its working tree exists
            if ref:
                sys.exit(f"{top} has no commit, so there is no {ref} to export")
            if fully_built(library, prefix):
                print(f"using the build in {library} (no commit yet)", file=sys.stderr)
                return library
            sys.exit(f"{library} has no commit and no complete build: build it")
        want = git("rev-parse", "--verify", f"{ref}^{{commit}}", cwd=library) if ref else head
        dirty = git("status", "--porcelain", "--", ".", cwd=library)
        if want == head and not (ref and dirty) and fully_built(library, prefix):
            print(f"using the build in {library} ({'HEAD' if not ref else ref} = {head[:10]})", file=sys.stderr)
            return library
        if not ref and dirty:
            sys.exit(f"{library} has uncommitted changes and no complete build: commit them, or build it")
        reason = ("not fully built" if want == head else f"HEAD is {head[:10]}, {ref} is {want[:10]}")
        print(f"local build not usable ({reason}): building {ref or 'HEAD'} under {cache}", file=sys.stderr)
        source, commit = top, want
    else:
        if not ref:
            sym = git("ls-remote", "--symref", library, "HEAD")
            m = re.search(r"ref: refs/heads/(\S+)\s+HEAD", sym)
            ref = m.group(1) if m else "HEAD"
        source, commit = library, None
    name = re.sub(r"[^A-Za-z0-9._-]+", "_", library.rstrip("/")) + "@" + re.sub(r"[^A-Za-z0-9._-]+", "_", ref or "HEAD")
    checkout = os.path.join(cache, name)
    if not os.path.isdir(os.path.join(checkout, ".git")):
        os.makedirs(cache, exist_ok=True)
        print(f"cloning {source} into {checkout}", file=sys.stderr)
        git("clone", "--quiet", source, checkout)
    else:
        git("fetch", "--quiet", "origin", cwd=checkout)
    target = commit or git("rev-parse", "--verify", f"origin/{ref}^{{commit}}", cwd=checkout, check=False) \
        or git("rev-parse", "--verify", f"{ref}^{{commit}}", cwd=checkout)
    if git("rev-parse", "HEAD", cwd=checkout) != target:
        git("checkout", "--quiet", "--detach", target, cwd=checkout)
    if subdir and subdir != ".":
        checkout = os.path.join(checkout, subdir)
    stamp = os.path.join(checkout, ".lake", f"lax-export-built-{target}")
    if os.path.isfile(stamp) and fully_built(checkout, prefix):
        print(f"using the cached build in {checkout} ({target[:10]})", file=sys.stderr)
        return checkout
    toolchain = open(os.path.join(checkout, "lean-toolchain"), encoding="utf-8").read().strip()
    check_environment(toolchain, mathlib_pin(checkout), None, before_build=True)
    log = os.path.join(checkout, ".lake-export-build.log")
    print(f"building {checkout} at {target[:10]} (log: {log})", file=sys.stderr)
    # No credential prompt (an anonymous clone GitHub answers with a
    # challenge would otherwise hang), and a retry for the fetch, which clones
    # Mathlib and its dependencies and fails on a transient refusal.
    build_env = dict(os.environ, GIT_TERMINAL_PROMPT="0")
    with open(log, "w", encoding="utf-8") as fh:
        for cmd, tries in ((["lake", "exe", "cache", "get"], 3), (["lake", "build"], 1)):
            for attempt in range(tries):
                r = subprocess.run(cmd, cwd=checkout, stdout=fh, stderr=subprocess.STDOUT,
                                   text=True, env=build_env)
                if r.returncode == 0:
                    break
                print(f"{' '.join(cmd)} failed (attempt {attempt + 1} of {tries})", file=sys.stderr)
                if attempt + 1 < tries:
                    time.sleep(60 * (attempt + 1))        # GitHub throttles anonymous clones
            if r.returncode:
                sys.exit(f"{' '.join(cmd)} failed in {checkout}; see {log}")
    open(stamp, "w").close()
    return checkout


def mathlib_pin(checkout):
    """Mathlib's commit in the checkout's lake manifest."""
    path = os.path.join(checkout, "lake-manifest.json")
    if not os.path.isfile(path):
        sys.exit(f"{checkout} has no lake-manifest.json")
    for p in json.load(open(path, encoding="utf-8")).get("packages", []):
        if p.get("name") == "mathlib":
            return p.get("rev")
    sys.exit(f"{checkout} does not require mathlib")


_ENVIRONMENTS = None


def archive_environments():
    """The Lax archive's environments: its epoch and the listed ids, from
    https://laxarchive.org/environments.json."""
    global _ENVIRONMENTS
    if _ENVIRONMENTS is None:
        import urllib.request
        try:
            with urllib.request.urlopen("https://laxarchive.org/environments.json", timeout=20) as r:
                _ENVIRONMENTS = json.load(r)
        except Exception as e:                      # noqa: BLE001
            sys.exit(f"cannot read the Lax archive's environments ({e}); pass --no-environment-check to go on")
    return _ENVIRONMENTS


def check_environment(toolchain, mathlib_rev, env_id, before_build=False):
    """The library's Lean version must be an archive environment, the epoch
    unless --env names another listed one, and its Mathlib pin must be the
    commit of Mathlib's tag of that version, which is what the environment
    records."""
    envs = archive_environments()
    epoch = envs["epoch"]
    ids = {e["id"] for e in envs["environments"]}
    version = toolchain.split(":")[-1]
    want = env_id or epoch
    if version != want:
        if version in ids and not env_id:
            sys.exit(f"the library is on Lean {version}, the Lax archive's epoch is {epoch}: "
                     f"export a ref on {epoch}, or pass --env {version} (a submission there can only "
                     f"cite and be cited within that environment)")
        sys.exit(f"the library is on Lean {version}, which is not the Lax archive environment {want} "
                 f"(listed: {', '.join(sorted(ids))})")
    tag = git("ls-remote", "https://github.com/leanprover-community/mathlib4", f"refs/tags/{version}")
    expected = tag.split()[0] if tag else None
    if expected and expected != mathlib_rev:
        sys.exit(f"the library pins Mathlib {mathlib_rev[:10]}, the environment {version} is Mathlib's "
                 f"tag {version} = {expected[:10]}")
    print(f"environment {version}{' (epoch)' if version == epoch else ''}, Mathlib {mathlib_rev[:10]}",
          file=sys.stderr)


def outside_comments(text, fn):
    """`fn` applied to the code of `text`, its comments left as they are:
    `--` line comments and (nested) `/- … -/` block comments, docstrings
    included, since prose mentioning a library's root name is not a
    reference to it."""
    out = []
    i, n, code_start = 0, len(text), 0
    while i < n:
        if text.startswith("--", i):
            out.append(fn(text[code_start:i]))
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(text[i:j])
            i = code_start = j
        elif text.startswith("/-", i):
            out.append(fn(text[code_start:i]))
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            out.append(text[i:j])
            i = code_start = j
        else:
            i += 1
    out.append(fn(text[code_start:]))
    return "".join(out)


def rewriter(prefix, new_prefix):
    # The prefix as a whole name component: not preceded by a name character
    # or a dot, except the explicit root marker `_root_.`, and followed by a
    # dot or a non-name character; comments are left alone.
    pat = re.compile(r"(?:(?<=_root_\.)|(?<![\w.']))" + re.escape(prefix) + r"(?![\w'])")
    return lambda text: outside_comments(text, lambda code: pat.sub(new_prefix, code))


LAKEFILE = """name = "{name}"
defaultTargets = ["{name}"]

[leanOptions]
autoImplicit = false

[[require]]
name = "mathlib"
git = "{mathlib}"
rev = "{rev}"
{extra}
[[lean_lib]]
name = "{name}"
"""


PERMISSIVE = {
    "MIT": r"Permission is hereby granted, free of charge",
    "BSD": r"Redistribution and use in source and binary forms",
    "ISC": r"Permission to use, copy, modify, and/or distribute this software for any",
    "0BSD": r"Permission to use, copy, modify, and/or distribute this software for any",
    "Unlicense": r"This is free and unencumbered software released into the public domain",
    "CC0": r"CC0 1\.0 Universal",
}


def write_licenses(src, out, copyright_line, force, notice=None):
    """The Lax accepts exactly one license for a submission, Apache 2.0,
    with at most one trailing copyright line. The vendored code keeps its
    own headers; when the library's license is a permissive one that
    permits sublicensing, its text goes into NOTICE beside the Apache text;
    a library under any other license is refused unless forced. `notice`
    is a paragraph of the author's for NOTICE, say the terms of a paper
    carried in the submission."""
    apache = open(os.path.join(HERE, "LICENSE"), encoding="utf-8").read()
    text = apache + (f"\nCopyright {copyright_line}\n" if copyright_line else "")
    write(os.path.join(out, "LICENSE"), text)
    notice_path = os.path.join(out, "NOTICE")
    path = os.path.join(src, "LICENSE")
    if not os.path.isfile(path):
        print("warning: the library has no LICENSE file; the submission's NOTICE cannot name its terms",
              file=sys.stderr)
        if notice:
            write(notice_path, notice.strip() + "\n")
        return
    lib = open(path, encoding="utf-8").read()
    if re.search(r"Apache License\s+Version 2\.0", lib):
        if notice:
            write(notice_path, notice.strip() + "\n")
        return                                                         # same license, nothing to add
    kind = next((k for k, pat in PERMISSIVE.items() if re.search(pat, lib)), None)
    if kind is None and not force:
        sys.exit("the library's LICENSE is neither Apache 2.0 nor a permissive license that permits "
                 "sublicensing (MIT, BSD, ISC, 0BSD, Unlicense, CC0): the Lax archive requires Apache 2.0 "
                 "for the submission, so it cannot be built from this library; --force-license overrides")
    write(notice_path,
          (notice.strip() + "\n\n" if notice else "")
          + "The Lean code under proofs/ is derived from a library distributed under the "
          f"following license{' (' + kind + ')' if kind else ''}, whose notices the vendored "
          "files retain. This submission is distributed under the Apache License 2.0, see LICENSE.\n\n"
          + lib)


MANIFEST_KEYS = {"id", "title", "authors", "bibEntries", "supersedes", "unlisted", "anonymous",
                 "issue", "paper", "initialOwners"}
CONFIG_KEYS = {"library", "ref", "prefix", "targets", "options", "whole_modules",
               "copyright", "force_license", "notice", "env", "manifest", "out", "restated", "requires"}
REQUIRE_KEYS = {"package", "repository", "commit", "folder", "restated_from"}


def load_config(path):
    """The export's description. Paths are relative to the file."""
    path = os.path.abspath(path)
    base = os.path.dirname(path)
    with open(path, encoding="utf-8") as fh:
        raw = yaml.safe_load(fh) or {}
    unknown = set(raw) - CONFIG_KEYS
    if unknown:
        sys.exit(f"{path}: unknown keys {sorted(unknown)}")
    for key in ("library", "prefix", "targets", "manifest"):
        if key not in raw:
            sys.exit(f"{path}: `{key}` is required")
    manifest = raw["manifest"]
    bad = set(manifest) - MANIFEST_KEYS
    if bad:
        sys.exit(f"{path}: manifest keys {sorted(bad)} are not in the Lax archive's schema")
    if "id" in manifest and not re.fullmatch(r"lax-[1-9][0-9]*", str(manifest["id"])):
        sys.exit(f"{path}: manifest.id must be `lax-N`")
    if "title" not in manifest:
        sys.exit(f"{path}: manifest.title is required")
    for a in manifest.get("authors", []):
        if not isinstance(a, dict) or "name" not in a or set(a) - {"name", "orcid", "github"}:
            sys.exit(f"{path}: each author is a mapping with `name` and optional `orcid`, `github`")
    def rel(p):
        if p is None or is_url(str(p)):
            return p
        return os.path.normpath(os.path.join(base, os.path.expanduser(str(p))))
    restated = raw.get("restated") or {}
    if not isinstance(restated, dict) or not all(isinstance(k, str) and isinstance(v, str)
                                                 for k, v in restated.items()):
        sys.exit(f"{path}: `restated` maps library declarations to concept declarations")
    requires = []
    for r in raw.get("requires") or []:
        if not isinstance(r, dict) or set(r) - REQUIRE_KEYS or not {"package", "repository",
                                                                      "commit", "folder"} <= set(r):
            sys.exit(f"{path}: each entry of `requires` is a mapping with `package`, `repository`, "
                     "`commit`, `folder` and optionally `restated_from`")
        if not re.fullmatch(r"Lax[1-9][0-9]*", str(r["package"])):
            sys.exit(f"{path}: requires.package must be a concept package `LaxN`")
        if not re.fullmatch(r"[0-9a-f]{40}", str(r["commit"])):
            sys.exit(f"{path}: requires.commit must be the full 40-character commit of the "
                     "registered submission")
        if not str(r["repository"]).startswith("https://"):
            sys.exit(f"{path}: requires.repository must be the submission's canonical https URL")
        entry = {k: str(r[k]) for k in ("package", "repository", "commit", "folder")}
        entry["folder"] = entry["folder"].strip("/")
        if "restated_from" in r:
            other = rel(r["restated_from"])
            with open(other, encoding="utf-8") as fh:
                theirs = (yaml.safe_load(fh) or {}).get("restated") or {}
            # their relative names are relative to *their* package
            for lib, con in theirs.items():
                qualified = con if re.match(r"Lax\d+\.", con) else f"{entry['package']}.{con}"
                restated.setdefault(lib, qualified)
        requires.append(entry)
    return {
        "restated": restated,
        "requires": requires,
        "library": raw["library"] if is_url(str(raw["library"])) else rel(raw["library"]),
        "ref": raw.get("ref"),
        "prefix": raw["prefix"],
        "target": list(raw["targets"]),
        "set_option": list(raw.get("options", [])),
        "whole_modules": bool(raw.get("whole_modules", False)),
        "copyright": raw.get("copyright"),
        "force_license": bool(raw.get("force_license", False)),
        "notice": raw.get("notice"),
        "env": raw.get("env"),
        "manifest": manifest,
        "out": rel(raw.get("out", ".")),
    }


class _Quoted(str):
    """A scalar written in double quotes, as the Lax archive's examples write
    every string field (a commit hash or an ORCID left plain could read as
    a number)."""


class _Literal(str):
    """A multi-line scalar written as a `|` block, for BibTeX entries."""


def _represent(dumper, data):
    if isinstance(data, _Literal):
        return dumper.represent_scalar("tag:yaml.org,2002:str", str(data), style="|")
    return dumper.represent_scalar("tag:yaml.org,2002:str", str(data), style='"')


yaml.add_representer(_Quoted, _represent, Dumper=yaml.SafeDumper)
yaml.add_representer(_Literal, _represent, Dumper=yaml.SafeDumper)


def _mark(value):
    if isinstance(value, dict):
        return {k: _mark(v) for k, v in value.items()}
    if isinstance(value, list):
        return [_mark(v) for v in value]
    if isinstance(value, str):
        return _Literal(value) if "\n" in value else _Quoted(value)
    return value                     # booleans and the issue numbers stay as they are


class _Dumper(yaml.SafeDumper):
    """PyYAML writes a list under a key flush with the key; the Lax CLI, which
    rewrites the manifest at `lax submit`, indents its items. Match it, so
    that a re-export after a submit leaves the manifest unchanged."""
    def increase_indent(self, flow=False, indentless=False):
        return super().increase_indent(flow, False)


def dump_manifest(manifest):
    return yaml.dump(_mark(manifest), Dumper=_Dumper, sort_keys=False, allow_unicode=True,
                     default_flow_style=False, width=1000)


def existing_manifest(out):
    """The manifest already in the submission folder, written by `lax init`
    and later `lax submit`, when there is one."""
    path = os.path.join(out, "manifest.yaml")
    if not os.path.isfile(path):
        return {}
    with open(path, encoding="utf-8") as fh:
        return yaml.safe_load(fh) or {}


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(text)


SCAFFOLD = {
    "header", "Lean.Parser.Command.moduleDoc", "Lean.Parser.Command.namespace",
    "Lean.Parser.Command.section", "Lean.Parser.Command.end",
    "Lean.Parser.Command.noncomputableSection", "Lean.Parser.Command.variable",
    "Lean.Parser.Command.universe", "Lean.Parser.Command.open",
    "Lean.Parser.Command.set_option", "Lean.Parser.Command.notation",
    "Lean.Parser.Command.mixfix", "Lean.Parser.Command.macro",
    "Lean.Parser.Command.macro_rules", "Lean.Parser.Command.syntax",
    "Lean.Parser.Command.elab", "Lean.Parser.Command.attribute",
    "Lean.Parser.Command.omit", "Lean.Parser.Command.include",
    "Lean.Parser.Command.export", "Lean.Parser.Command.eoi",
}
# commands that declare syntax, named in the current namespace
NOTATION_KINDS = {"Lean.Parser.Command.notation", "Lean.Parser.Command.mixfix",
                  "Lean.Parser.Command.macro", "Lean.Parser.Command.macro_rules",
                  "Lean.Parser.Command.syntax"}
# scaffolding whose references to library constants must all be selected
CHECKED = {"Lean.Parser.Command.variable", "Lean.Parser.Command.attribute",
           "Lean.Parser.Command.omit", "Lean.Parser.Command.include",
           "Lean.Parser.Command.notation", "Lean.Parser.Command.macro_rules"}


def run(cmd, cwd, env):
    r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    if r.returncode:
        sys.exit(f"failed: {' '.join(cmd)}\n{r.stdout[-2000:]}\n{r.stderr[-2000:]}")
    return r


def module_path(src, mod):
    return os.path.join(src, *mod.split(".")) + ".lean"


LIB_PREFIX = None       # the library's namespace, set once the configuration is read
RESTATED_LIB = set()    # the library declarations the concepts restate, likewise
MANGLED = {}            # written name -> mangled name, of the private declarations demangled


def demangle(name):
    """A private declaration outside the library's namespace by the name it
    is written with: Lean mangles `private def Why.zsf` of module `M` into
    `_private.M.0.Why.zsf`, and a vendored copy, rooted under the package
    like every other library name, is no longer private. A private
    declaration under the library's namespace keeps its mangled name and
    stays private: its vendored copy is under the package already, and two
    modules may each have their own `private def Lib.aux`. The exception is
    a private declaration under a restated one, `private def Lib.Spec.pad`
    used as `spec.pad`: field notation on the concept's type finds it only
    through an alias, which a private name cannot have."""
    m = re.match(r"^_private\..*?\.0\.(.*)$", name)
    if not m:
        return name
    inner = m.group(1)
    parts = inner.split(".")
    if not any(".".join(parts[:i]) in RESTATED_LIB for i in range(1, len(parts))):
        if LIB_PREFIX and (inner == LIB_PREFIX or inner.startswith(LIB_PREFIX + ".")):
            return name
    MANGLED[inner] = name
    return inner


def ilean(build, mod):
    p = os.path.join(build, *mod.split(".")) + ".ilean"
    if not os.path.isfile(p):
        return {}
    d = json.load(open(p, encoding="utf-8"))
    out = {}
    for k, v in d["references"].items():
        c = json.loads(k)["c"]
        out[demangle(c["n"])] = {"module": c["m"], "definition": v.get("definition"),
                                 "usages": v.get("usages", []),
                                 "unprivate": demangle(c["n"]) != c["n"]}
    return out


def attribute_generated(name, ranged):
    """The ranged declaration a generated constant belongs to, by stripping
    name components (`Foo.rec`, `Foo.match_1`, `Foo.proof_1`, `Foo.eq_1`…)."""
    parts = name.split(".")
    while len(parts) > 1:
        parts = parts[:-1]
        cand = ".".join(parts)
        if cand in ranged:
            return cand
    return None


ATTRIBUTE_SUBSTITUTES = {"instance_reducible": "reducible"}

# the last component of a constant Lean generates beside a declaration
GENERATED_SUFFIX = re.compile(
    r"\.(rec|recOn|casesOn|noConfusion|noConfusionType|below|brecOn|binductionOn|ibelow|inj|injEq|"
    r"sizeOf_spec|match_\d+|proof_\d+|eq_\d+|_sunfold|_unsafe_rec|ctorIdx|toCtorIdx|ofNat|_aux_\d+|_f|"
    r"splitter|mk\.inj|mk\.injEq)$")

# attributes whose generated lemmas the ilean records at the attribute's own
# token rather than at an identifier
GENERATING_ATTRIBUTES = {"simps", "simps!", "simps?", "to_additive", "ext"}


def printed_forms(lib, pfx):
    """The spellings a pretty-printer may use for the constant `lib`: in full,
    or relative to the library's root or to Mathlib's `FirstOrder.Language`,
    which the library opens."""
    out = [lib]
    for root in (pfx + ".", "FirstOrder.", "FirstOrder.Language."):
        if lib.startswith(root):
            out.append(lib[len(root):])
    return out
DERIVING_WHITELIST = {"Repr", "DecidableEq", "Inhabited", "Fintype", "BEq", "Hashable"}


def write_skeletons(args, cname, pfx, restated, restated_cmds, decisions, commands, imports_of, below,
                    expanded_listing):
    """Draft concept modules under <out>/skeleton/<cname>/: for each concept
    module named by a `restated` value of this package, the library's
    defining commands of the declarations it restates, in library order,
    with their docstrings, renamed to the concept's names, every use of a
    restated declaration patched, the sections and nested namespaces they
    were declared in replayed with their `variable` and `open` lines, and
    attributes the concept dialect refuses substituted. A starting point,
    never a result: the module docstring is a stub, and nothing here is
    read back by the export."""
    out_dir = os.path.join(args.out, "skeleton", cname)
    own = {lib: con for lib, con in restated.items() if con.startswith(cname + ".")}
    def concept_of(n):
        """The concept name of a library constant, by the longest restated prefix."""
        best = None
        for lib in restated:
            if (n == lib or n.startswith(lib + ".")) and (best is None or len(lib) > len(best)):
                best = lib
        return restated[best] + n[len(best):] if best else None
    by_concept = {}             # concept module -> [(source module, command)]
    for mod in sorted(restated_cmds):
        for cmd in restated_cmds[mod]:
            targets = {v for v in cmd["restated_defs"].values() if v.startswith(cname + ".")}
            if targets:
                by_concept.setdefault(".".join(sorted(targets)[0].split(".")[:2]), []).append((mod, cmd))
    def import_order(mods):
        """`mods` sorted so that a module follows the ones it imports."""
        order, seen = [], set()
        def visit(m):
            if m in seen:
                return
            seen.add(m)
            for i in imports_of(m):
                if i in mods:
                    visit(i)
            order.append(m)
        for m in sorted(mods):
            visit(m)
        return order
    written = []
    for cm, items in sorted(by_concept.items()):
        rank = {m: i for i, m in enumerate(import_order({m for m, _ in items}))}
        items = sorted(items, key=lambda it: (rank[it[0]], it[1]["start"]))
        pieces, imports, notes, opens = [], [], [], set()
        emitted = [["namespace", cm, {}]]      # open levels: kind, name, scaffolding emitted per library level
        pieces.append(f"namespace {cm}")
        def substitute_printed(txt):
            """Restated names in a pretty-printed expansion, which writes a
            name in full or relative to an open namespace, rewritten to the
            concept's; docstrings are left alone."""
            def forms(lib):
                return printed_forms(lib, pfx)
            def in_code(seg):
                for lib, con in sorted(restated.items(), key=lambda kv: -len(kv[0])):
                    module = ".".join(con.split(".")[:2])
                    new = relative(con) if con.startswith(cm + ".") else con[len(module) + 1:]
                    for form in forms(lib):
                        seg, n = re.subn(r"(?<![\w.'])" + re.escape(form) + r"(?![\w'])", new, seg)
                        if n and not con.startswith(cm + "."):
                            opens.add(module)
                return seg
            parts = re.split(r"(/--.*?-/)", txt, flags=re.S)
            return "".join(p if p.startswith("/--") else in_code(p) for p in parts)
        def relative(con):
            """A concept name as written inside the module namespace and the
            nested namespaces currently open."""
            inner = ".".join(n for k, n, _ in emitted[1:] if k == "namespace")
            base = cm + ("." + inner if inner else "")
            if con.startswith(base + "."):
                return con[len(base) + 1:]
            if con.startswith(cm + "."):
                return con[len(cm) + 1:]
            return con
        current_source = None
        for mod, cmd in items:
            text, byte_to_char, refs, _ = decisions[mod]
            if mod != current_source:
                current_source = mod
                lib_depth = []             # [kind, name, scaffolding (kind, chunk) list]
                walked = 0
                all_cmds = commands[mod]["commands"]
                notation_uses = {c["start"]: c.get("macros", []) for c in expanded_listing(mod)["commands"]}
                for level in emitted:
                    level[2] = {}
                # every Mathlib module the source module reaches: a concept
                # has no library module to inherit imports from
                stack, seen_mods = [mod], set()
                while stack:
                    m = stack.pop()
                    if m in seen_mods:
                        continue
                    seen_mods.add(m)
                    for imp in imports_of(m):
                        if imp.startswith(pfx + "."):
                            stack.append(imp)
                        elif f"import {imp}" not in imports:
                            imports.append(f"import {imp}")
                line_starts = [0] + [i + 1 for i, ch in enumerate(text) if ch == "\n"]
                def at(l, c16):
                    pos, units = line_starts[l], 0
                    while units < c16:
                        units += 2 if ord(text[pos]) > 0xFFFF else 1
                        pos += 1
                    return pos
                def patched(a, b, own_defs, macros=()):
                    """The text of [a, b) with uses of restated declarations
                    written as the concept's names, the ids of `own_defs`
                    (library name -> concept name) renamed, and the library's
                    notations (`macros`, outermost uses first) expanded."""
                    spans = sorted(((byte_to_char[m["start"]], byte_to_char[m["end"]], m["text"])
                                    for m in macros), key=lambda m: (m[0], -m[1]))
                    outer, last_end = [], -1
                    for ma, mb, mt in spans:
                        if ma >= last_end and a <= ma and mb <= b:
                            outer.append((ma, mb, mt)); last_end = mb
                    def in_expansion(pos):
                        return any(ma <= pos < mb for ma, mb, _ in outer)
                    edits = []
                    for ma, mb, mt in outer:
                        edits.append((ma, mb, substitute_printed(mt)))
                    for n, r in refs.items():
                        d = r.get("definition")
                        if n in own_defs and d and d[0] == d[2]:
                            da, db = at(d[0], d[1]), at(d[2], d[3])
                            if a <= da and db <= b and re.fullmatch(r"[\w.'«»]+", text[da:db]) \
                                    and text[da:db] != "instance":
                                parent = n.rpartition(".")[0]
                                # a field or constructor is named by its parent's command
                                new_id = (own_defs[n].rpartition(".")[2] if parent in own_defs
                                          else relative(own_defs[n]))
                                edits.append((da, db, new_id))
                            continue
                        con = concept_of(n)
                        if con is None:
                            if n.startswith(pfx + ".") and n not in own_defs and not n.startswith("_private."):
                                for u in r["usages"]:
                                    if u[0] == u[2] and a <= at(u[0], u[1]) and at(u[2], u[3]) <= b:
                                        notes.append(f"{cm}: mentions `{n}`, which is not restated "
                                                     "(a theorem cannot be; a concept must prove or state it)")
                                        break
                            continue
                        if n in own_defs:
                            continue
                        for u in r["usages"]:
                            if u[0] != u[2]:
                                continue
                            ua, ub = at(u[0], u[1]), at(u[2], u[3])
                            if not (a <= ua and ub <= b) or in_expansion(ua):
                                continue
                            tok = text[ua:ub]
                            if not (n == tok or n.endswith("." + tok)) or (ua > 0 and text[ua - 1] == "."):
                                continue
                            before = text[text.rfind("\n", 0, ua) + 1:ua]
                            nl = text.find("\n", ub)
                            after = text[ub:nl if nl >= 0 else len(text)]
                            if "." not in tok and re.search(r"(?:^|[{,])\s*$", before) and ":=" in after:
                                continue
                            if con.startswith(cm + "."):
                                new = relative(con)
                            else:
                                opens.add(".".join(con.split(".")[:2]))
                                new = con[len(".".join(con.split(".")[:2])) + 1:]
                            edits.append((ua, ub, new))
                    out = text[a:b]
                    for ea, eb, new in sorted(edits, reverse=True):
                        out = out[:ea - a] + new + out[eb - a:]
                    return out
            idx = next(i for i, c in enumerate(all_cmds) if c["start"] == cmd["start"])
            def chunk_of(c):
                return text[byte_to_char[c["start"]]:byte_to_char[c["end"]]]
            def reopen_text(open_chunk):
                cur = ".".join(n for k, n, _ in lib_depth if k == "namespace")
                def sub(m):
                    name = m.group(0)
                    if name in ("in", "scoped", "hiding", "renaming"):
                        return name
                    for lib, con in restated.items():
                        if lib in (f"{cur}.{name}", f"{pfx}.{name}"):
                            return relative(con)
                    # a namespace of the library that nothing restated: the
                    # concept has nothing to open there, and an unknown
                    # namespace aborts the whole `open`
                    for full in (f"{cur}.{name}.", f"{pfx}.{name}."):
                        if any(n.startswith(full) for n in refs):
                            notes.append(f"{cm}: `open {name}` dropped, a library namespace the concepts lack")
                            return ""
                    return name
                head, _, rest = open_chunk.partition("open")
                rest = re.sub(r"(?<![\w.'])[A-Za-z_][\w'.]*(?![\w'])", sub, rest)
                rest = re.sub(r"[ \t]+", " ", rest).rstrip()
                return (head + "open" + rest) if rest.strip() not in ("", "in") else ""
            pending_attributes = []
            for c in all_cmds[walked:idx]:
                k = c["kind"]
                if k == "Lean.Parser.Command.namespace":
                    name = chunk_of(c).split()[1]
                    full = ".".join([n for kk, n, _ in lib_depth if kk == "namespace"] + [name])
                    scaffold = []
                    if not full.startswith(pfx) and name != pfx:
                        # a foreign namespace: its contents resolved relatively
                        # there, so the concept opens it instead
                        scaffold.append(("opentext", f"open {full}"))
                    lib_depth.append(["namespace", name, scaffold])
                elif k in ("Lean.Parser.Command.section", "Lean.Parser.Command.noncomputableSection"):
                    parts = chunk_of(c).split()
                    lib_depth.append(["section", parts[1] if len(parts) > 1 else "", []])
                elif k == "Lean.Parser.Command.end":
                    if lib_depth:
                        lib_depth.pop()
                elif k == "Lean.Parser.Command.open" and lib_depth:
                    lib_depth[-1][2].append(("open", c))
                elif k in ("Lean.Parser.Command.variable", "Lean.Parser.Command.universe") and lib_depth:
                    lib_depth[-1][2].append(("scaffold", c))
                elif k == "Lean.Parser.Command.attribute":
                    a, b = byte_to_char[c["start"]], byte_to_char[c["end"]]
                    if any(concept_of(n) and any(u[0] == u[2] and a <= at(u[0], u[1]) < b for u in r["usages"])
                           for n, r in refs.items()):
                        pending_attributes.append(c)
            walked = idx + 1
            # the chain of levels this declaration wants: the module namespace
            # (standing for the library's root and any foreign namespace), the
            # library's sections, and the nested namespaces the concept name
            # keeps below the module namespace
            first = sorted(v for v in cmd["restated_defs"].values() if v.startswith(cm + "."))[0]
            rel_parts = first[len(cm) + 1:].split(".")[:-1]
            desired = [["namespace", cm, []]]
            for li, (k, n, scs) in enumerate(lib_depth):
                if k == "section":
                    desired.append(["section", n, [li]])
                elif n in rel_parts:
                    desired.append(["namespace", n, [li]])
                else:
                    desired[0][2].append(li)
            common = 1
            while common < min(len(emitted), len(desired)) and emitted[common][:2] == desired[common][:2]:
                common += 1
            while len(emitted) > common:
                kind, name, _ = emitted.pop()
                pieces.append(f"end {name}" if name else "end")
            # open each missing level in turn, and after each level (open
            # already or just opened) the scaffolding of its library levels
            # not emitted yet: `variable` and `open` lines in library order
            for i, (kind, name, sources) in enumerate(desired):
                if i >= len(emitted):
                    pieces.append(f"{kind} {name}" if name else kind)
                    emitted.append([kind, name, {}])
                level = emitted[i]
                for li in sources:
                    key = id(lib_depth[li][2])
                    done = level[2].get(key, 0)
                    for skind, c in lib_depth[li][2][done:]:
                        if skind == "opentext":
                            pieces.append(c)
                            continue
                        a, b = byte_to_char[c["start"]], byte_to_char[c["end"]]
                        pieces.append(reopen_text(chunk_of(c)) if skind == "open" else patched(a, b, {}))
                    level[2][key] = len(lib_depth[li][2])
            for c in pending_attributes:
                pieces.append(patched(byte_to_char[c["start"]], byte_to_char[c["end"]], {}))
            # the command itself: the elaborated expansion of a library-defined
            # command, or the source with its ids renamed and its uses patched
            defs_here = cmd["restated_defs"]
            # an unnamed instance the command declares: its library name is
            # the build's, mapped under the command's namespace
            lib_ns = ".".join(n for k, n, _ in lib_depth if k == "namespace")
            inst_names = [con for lib, con in own.items()
                          if lib.rpartition(".")[2].startswith("inst") and con.startswith(cm + ".")
                          and (lib in defs_here or lib.rpartition(".")[0] == lib_ns)
                          and f"instance {relative(con)}" not in "\n".join(pieces)]
            expansion = cmd.get("expansion")
            if expansion and not cmd["kind"].startswith("Lean.Parser.Command."):
                body = "\n\n".join(re.sub(r"(?<!^)(?<!\n)(?<!\s)(/--)", r"\n\1", e) for e in expansion)
                body = body.replace("_root_.", "")
                body = re.sub(r"\(([A-Za-z_][\w'.]*)\)\.", r"\1.", body)
                body = substitute_printed(body)
                body = re.sub(r"^(\s*(?:@\[[^\]]*\]\s*)*)protected\s+", r"\1", body, flags=re.M)
                for lib, con in defs_here.items():
                    short_lib, short_con = lib.rpartition(".")[2], relative(con).rpartition(".")[2]
                    if short_lib != short_con and not short_lib.startswith("inst"):
                        notes.append(f"{cm}: the expansion declaring {lib} is renamed to {relative(con)} "
                                     "by a word-level substitution; check it")
                body = re.sub(r"-/\n\n(\s*\|)", r"-/\n\1", body)
            else:
                a, b = byte_to_char[cmd["start"]], byte_to_char[cmd["end"]]
                body = patched(a, b, defs_here, notation_uses.get(cmd["start"], []))
            body = re.sub(r"^(\s*(?:/-.*?-/\s*)?(?:@\[[^\]]*\]\s*)*)protected\s+", r"\1", body, count=1, flags=re.S)
            body = body.replace("_root_.", "")
            # the `instance` keyword at the head of a command line, never the
            # word inside a docstring ("a packaged instance: pages, ...")
            m = re.search(r"(?m)^(?P<pre>[ \t]*(?:@\[[^\]]*\][ \t]*)*"
                          r"(?:(?:noncomputable|protected|private|scoped|local)\s+)*)"
                          r"instance(?P<bind>\s*(?:\([^)]*\)\s*)?):\s*(?P<cls>[\w.]+)(?:\s+(?P<arg>[\w.]+))?", body)
            if m and inst_names:
                cls = m.group("cls").rpartition(".")[2].lower()
                arg = (m.group("arg") or "").rpartition(".")[2].lower()
                chosen = [c for c in inst_names if cls in c.lower() and (not arg or arg in c.lower())] \
                    or [c for c in inst_names if cls in c.lower()] or (inst_names if len(inst_names) == 1 else [])
                if chosen:
                    body = body[:m.start()] + m.group("pre") + f"instance {relative(chosen[0])}{m.group('bind')}:" \
                        + body[m.end("bind") + 1:]
            m = re.search(r"\n\s*deriving\s+([^\n]+)$", body)
            if m and not {c.strip() for c in m.group(1).split(",")} <= DERIVING_WHITELIST:
                notes.append(f"{cm}: `deriving {m.group(1).strip()}` is outside the concept dialect's "
                             "class list; write that instance by hand")
            for old, new in ATTRIBUTE_SUBSTITUTES.items():
                if re.search(r"@\[[^\]]*\b" + old + r"\b", body):
                    body = re.sub(r"(@\[[^\]]*)\b" + old + r"\b", r"\1" + new, body)
                    notes.append(f"{cm}: `@[{old}]` is not in the concept dialect; written as `@[{new}]`")
            pieces.append(body)
        while len(emitted) > 1:
            kind, name, _ = emitted.pop()
            pieces.append(f"end {name}" if name else "end")
        pieces.append(f"end {cm}")
        if opens:
            pieces.insert(1, "open " + " ".join(sorted(opens)))
            imports.extend(f"import {o}" for o in sorted(opens))
        imports = list(dict.fromkeys(imports))
        header = ("\n".join(imports) + "\n\n/-!\n---\ntitle: " + cm.split(".")[1] +
                  "\ntype: definition\n---\nTODO: describe the notions this module restates.\n-/\n\n")
        path = os.path.join(out_dir, cm.split(".")[1] + ".lean")
        write(path, header + "\n\n".join(pieces) + "\n")
        written.append(path)
        for note in dict.fromkeys(notes):
            print(f"skeleton note: {note}")
    print(f"{len(written)} skeleton modules written under {out_dir}")


def main():
    ap = argparse.ArgumentParser(description="export theorems of a Lean library as a Lax submission")
    ap.add_argument("config", help="the export's YAML description (see README)")
    ap.add_argument("--out", help="the submission folder to write (default: the config's `out`, "
                                  "else `submission/` beside the config)")
    ap.add_argument("--cache", default=os.environ.get("LAX_EXPORT_CACHE",
                                                      os.path.join(tempfile.gettempdir(), "lax-export")),
                    help="where clones are built when the local build cannot be used "
                         "(default: $LAX_EXPORT_CACHE, else lax-export/ under the temporary "
                         "directory, which TMPDIR, TEMP or TMP select)")
    ap.add_argument("--no-environment-check", action="store_true",
                    help="skip the check that the library's Lean and Mathlib are the environment's")
    ap.add_argument("--jobs", type=int, default=4, help="files elaborated in parallel (default 4)")
    ap.add_argument("--work", help="where the plans go (default: <out>/.plan)")
    ap.add_argument("--skeleton", action="store_true",
                    help="also write, under <out>/skeleton/, a draft concept module per module named in "
                         "`restated`: the library's defining commands, renamed and patched, to start from")
    args = ap.parse_args()

    cfg = load_config(args.config)
    args.out = os.path.abspath(args.out or cfg["out"])
    for key in ("prefix", "target", "set_option", "whole_modules",
                "copyright", "force_license", "notice", "env", "manifest", "library", "ref", "restated",
                "requires"):
        setattr(args, key, cfg[key])
    existing = existing_manifest(args.out)
    if "id" in args.manifest and "id" in existing and args.manifest["id"] != existing["id"]:
        sys.exit(f"the export file says {args.manifest['id']} but {args.out}/manifest.yaml says "
                 f"{existing['id']}: run lax-export in the folder `lax init` made for this submission")
    sub_id = args.manifest.get("id") or existing.get("id")
    if not sub_id:
        sys.exit("no submission id: run `lax init` in the output folder first, or set manifest.id")
    args.id = sub_id[len("lax-"):]
    pfx, cname, pname = args.prefix, f"Lax{args.id}", f"Lax{args.id}Proofs"
    global LIB_PREFIX
    LIB_PREFIX = pfx
    RESTATED_LIB.update(args.restated)
    work = args.work or os.path.join(args.cache, "plans", sub_id)
    os.makedirs(work, exist_ok=True)
    src = resolve_library(args.library, args.ref, args.prefix, args.cache)
    toolchain = open(os.path.join(src, "lean-toolchain"), encoding="utf-8").read().strip()
    mathlib_rev = mathlib_pin(src)
    if not args.no_environment_check:
        check_environment(toolchain, mathlib_rev, args.env)
    if existing.get("leanVersion") and existing["leanVersion"] != toolchain.split(":")[-1]:
        sys.exit(f"{args.out} was initialized for environment {existing['leanVersion']}, "
                 f"the library builds on {toolchain.split(':')[-1]}")
    build = os.path.join(src, ".lake", "build", "lib", "lean")
    lean_path = ":".join(sorted(d for d, _, _ in os.walk(os.path.join(src, ".lake"), followlinks=True)
                                if d.endswith(os.path.join("build", "lib", "lean"))))
    args.src, args.build, args.mathlib_rev = src, build, mathlib_rev
    env = dict(os.environ, LEAN_PATH=lean_path)
    slice_lean = os.path.join(HERE, "Slice.lean")

    # 1. closure, iterated: compile-time dependencies (notation modules and
    # the metaprograms behind them) are invisible to proof terms, so their
    # declarations are fed back as targets until nothing new appears.
    def run_closure(targets):
        plan = os.path.join(work, "closure.json")
        # the environment knows a private declaration by its mangled name
        run(["lean", "--run", slice_lean, "closure", pfx, plan] + sorted(MANGLED.get(t, t) for t in targets),
            args.src, env)
        cl = json.load(open(plan, encoding="utf-8"))
        for c in cl["constants"]:
            c["name"] = demangle(c["name"])
        return cl

    def imports_of(mod):
        path = module_path(args.src, mod)
        if not os.path.isfile(path):
            return []
        return re.findall(r"^import\s+(\S+)", open(path, encoding="utf-8").read(), re.M)

    def import_closure(mods):
        seen, stack = set(), list(mods)
        while stack:
            m = stack.pop()
            if m in seen or not m.startswith(pfx + "."):
                continue
            seen.add(m)
            stack.extend(imports_of(m))
        return seen

    def categories_of(mod):
        """The syntax categories a module declares: they can never carry the
        package prefix, so uses of them are expanded and their parsers dropped."""
        path = module_path(args.src, mod)
        if not os.path.isfile(path):
            return []
        return re.findall(r"^\s*declare_syntax_cat\s+([\w.']+)", open(path, encoding="utf-8").read(), re.M)

    def list_commands_expanded(mod, extra):
        """The command listing of `mod` with the uses of every notation the
        modules in `extra` declare expanded; for the skeleton, which cannot
        carry the library's notations."""
        out = os.path.join(work, mod + ".expanded.commands.json")
        if not os.path.isfile(out):
            run(["lean", "--run", slice_lean, "commands", module_path(args.src, mod), out]
                + sorted({f"mod:{m}" for m in extra}), args.src, env)
        return json.load(open(out, encoding="utf-8"))

    def list_commands(mod, categories):
        out = os.path.join(work, mod + ".commands.json")
        if os.path.isfile(out) and json.load(open(out, encoding="utf-8")).get("version") != 2:
            os.remove(out)
        if not os.path.isfile(out):
            run(["lean", "--run", slice_lean, "commands", module_path(args.src, mod), out] + categories,
                args.src, env)
        return mod, json.load(open(out, encoding="utf-8"))

    META = {"Lean.Parser.Command.syntax", "Lean.Parser.Command.macro", "Lean.Parser.Command.macro_rules",
            "Lean.Parser.Command.elab", "Lean.Parser.Command.elab_rules", "Lean.Parser.Command.notation",
            "Lean.Parser.Command.mixfix", "Lean.Parser.Command.declare_syntax_cat"}

    targets = set(args.target)
    commands = {}
    full = set()                    # modules vendored in full: only with --whole-modules
    for _outer in range(6):
        silent_cmds = []
        for round_ in range(4):
            cl = run_closure(targets)
            own = [c for c in cl["constants"] if c["own"]]
            ranged = {c["name"]: c for c in own if c["range"]}
            selected = set(ranged)
            unattributed = []
            for c in own:
                if c["range"]:
                    continue
                p = attribute_generated(c["name"], ranged)
                if p:
                    selected.add(p)
                else:
                    unattributed.append(c["name"])
            touched = set(cl["modules"]) | {c["module"] for c in own}
            all_mods = import_closure(touched)
            category_mods = {m: categories_of(m) for m in all_mods}
            categories = sorted({f"cat:{c}" for cs in category_mods.values() for c in cs}
                                | {f"mod:{m}" for m, cs in category_mods.items() if cs})
            with ThreadPoolExecutor(max_workers=args.jobs) as ex:
                for mod, d in ex.map(lambda m: list_commands(m, categories), sorted(all_mods - set(commands))):
                    commands[mod] = d
            # what the library's notations and macros rest on: the constants their
            # defining commands mention (helper functions a `macro_rules` body
            # calls, say) become targets, so that the closure brings them in; a
            # module declaring a category is left out, its parsers being dropped
            # and the uses expanded instead
            if args.whole_modules:
                full = set(all_mods)
            extra = set()
            for m in all_mods:
                if category_mods[m] or args.whole_modules:
                    continue
                meta = [c for c in commands[m]["commands"] if c["kind"] in META]
                if not meta:
                    continue
                d = ilean(args.build, m)
                for n, r in d.items():
                    if not r["module"].startswith(pfx) or n.startswith("_private."):
                        continue
                    for u in r["usages"]:
                        if any(c["line"] <= u[0] + 1 <= c["endLine"] for c in meta):
                            extra.add(n); break
            extra = {n for n in extra if n not in targets}
            if not extra:
                break
            print(f"round {round_ + 1}: {len(extra)} declarations the library's notations rest on added as targets",
                  file=sys.stderr)
            targets |= extra
        for a in cl["axioms"]:
            if a["target"] in args.target:
                print(f"{a['target']}: axioms {a['axioms']}", file=sys.stderr)
        if unattributed:
            print(f"warning: {len(unattributed)} generated constants without a parent declaration, "
                  f"e.g. {unattributed[:5]}", file=sys.stderr)
        by_mod = {}
        for n in selected:
            c = ranged[n]
            by_mod.setdefault(c["module"], []).append((c["range"]["line"], c["range"]["endLine"], n))
        print(f"{len(selected)} declarations selected; {len(all_mods)} modules in the import closure",
              file=sys.stderr)
        for mod, d in commands.items():
            if d["errors"]:
                print(f"warning: {mod}: {len(d['errors'])} elaboration errors, first: {d['errors'][0][:200]}", file=sys.stderr)

        prefix_rewrite = rewriter(pfx, f"{pname}.{pfx}")
        header_opts = "".join(f"set_option {o}\n" for o in args.set_option)

        # 2. decide, per module of the import closure, which commands to keep
        silent_re = re.compile(
            r"^\s*(?:/-[-!]?.*?-/\s*)?(?:(?:omit|include|open)\b[^\n]*?\bin\s+)*(?P<attrs>(?:@\[[^\]]*\]\s*)*)"
            r"(?:noncomputable\s+|protected\s+|private\s+|scoped\s+|local\s+|unsafe\s+)*"
            r"(?P<kw>instance|theorem|lemma|def|abbrev)\b", re.S)
        silent_attrs = re.compile(r"\b(simp|simps|ext|norm_cast|refl|trans|symm|aesop|coe|reducible|instance)\b")
        stats = {"kept": 0, "dropped": 0, "lines": 0, "patched": 0, "unpatched": [], "instances": 0, "expanded": 0}
        decisions = {}            # module -> (text, byte_to_char, refs, keep list)
        ilean_cache = {}
        for mod in sorted(all_mods):
            src_path = module_path(args.src, mod)
            data = open(src_path, "rb").read()
            text = data.decode("utf-8")
            byte_to_char = {}
            b = 0
            for i, ch in enumerate(text):
                byte_to_char[b] = i
                b += len(ch.encode("utf-8"))
            byte_to_char[b] = len(text)
            refs = ilean(args.build, mod)
            uses_by_line = {}
            for n, r in refs.items():
                if r["module"].startswith(pfx):
                    for u in r["usages"]:
                        uses_by_line.setdefault(u[0] + 1, []).append((n, u))
            wanted = by_mod.get(mod, [])
            def overlaps(cmd):
                return any(not (e < cmd["line"] or s > cmd["endLine"]) for s, e, _ in wanted)
            def declared_by_kept(n):
                """`n` is declared by a kept command although the closure never
                reached it: a field or constructor of a selected structure, say,
                whose projection a silent instance mentions."""
                m = refs[n]["module"]
                dfn = refs[n].get("definition") if m == mod else \
                    ilean_cache.setdefault(m, ilean(args.build, m)).get(n, {}).get("definition")
                if not dfn:
                    return False
                return any(s <= dfn[0] + 1 <= e for s, e, _ in by_mod.get(m, []))
            def mentions_unselected(cmd):
                for ln in range(cmd["line"], cmd["endLine"] + 1):
                    for n, _ in uses_by_line.get(ln, []):
                        if n not in selected and not declared_by_kept(n):
                            return True
                return False
            def is_silent(cmd):
                a, b = byte_to_char[cmd["start"]], byte_to_char[cmd["end"]]
                m = silent_re.match(text[a:b])
                if not m:
                    return False
                return m.group("kw") == "instance" or bool(silent_attrs.search(m.group("attrs") or ""))
            keep, content = [], False
            drops_syntax = bool(category_mods.get(mod))
            for cmd in commands[mod]["commands"]:
                k = cmd["kind"]
                if k == "header":
                    keep.append(cmd); continue
                if drops_syntax and (k in META or k == "Lean.Parser.Command.syntaxCat"):
                    stats["dropped"] += 1; continue
                if mod in full:
                    keep.append(cmd); content = True; continue
                if k in SCAFFOLD:
                    if k in CHECKED and mentions_unselected(cmd):
                        stats["dropped"] += 1; continue
                    keep.append(cmd); continue
                if overlaps(cmd):
                    keep.append(cmd); stats["kept"] += 1; content = True
                elif is_silent(cmd) and not mentions_unselected(cmd):
                    keep.append(cmd); stats["instances"] += 1; content = True
                    silent_cmds.append((mod, cmd))
                else:
                    stats["dropped"] += 1
            if content:
                decisions[mod] = (text, byte_to_char, refs, keep)
        # a silent instance kept by its shape may rest on declarations the
        # closure never reached (the instance for bounded formulas behind the
        # one for formulas, say): make them targets and select again
        extra = set()
        for mod, cmd in silent_cmds:
            refs = decisions[mod][2]
            for n, r in refs.items():
                d = r.get("definition")
                if (d and r["module"] == mod and cmd["line"] <= d[0] + 1 <= cmd["endLine"]
                        and n not in selected and n not in targets and not n.startswith("_private.")):
                    extra.add(n)
        # a kept command may name a declaration its proof term does not use
        # (a lemma in a `simp only` list that fired on nothing, say): the
        # module must still declare it
        for mod, (_, _, refs, keep) in decisions.items():
            for cmd in keep:
                if cmd["kind"] == "header" or cmd["kind"] in SCAFFOLD:
                    continue
                for n, r in refs.items():
                    if (not r["module"].startswith(pfx) or n in selected or n in targets
                            or n.startswith("_private.") or GENERATED_SUFFIX.search(n)):
                        continue
                    if any(cmd["line"] <= u[0] + 1 <= cmd["endLine"] for u in r["usages"]):
                        extra.add(n)
        if not extra:
            break
        print(f"{len(extra)} declarations kept commands rest on were never reached by the closure: "
              "selecting again", file=sys.stderr)
        targets |= extra
    vendored = set(decisions)

    # Declarations the concepts restate verbatim (`restated`): the library's
    # copy is dropped, every constant the declaring command generates is
    # renamed to the concept's, and every use is patched. A concept name is
    # relative to this submission's concept package unless it names another
    # Lax package outright.
    restated = {}
    required_pkgs = {r["package"] for r in args.requires}
    for k, v in args.restated.items():
        if re.match(r"Lax\d+\.", v):
            pkg = v.split(".")[0]
            if pkg != cname and pkg not in required_pkgs:
                sys.exit(f"restated: {v} is in package {pkg}, which is neither this submission's "
                         f"concept package {cname} nor one listed under `requires`")
            restated[k] = v
        else:
            restated[k] = f"{cname}.{v}"
    # a restated declaration under the namespace of a declaration another
    # package restates (`TMData.AcceptsU` here, `TMData` in the core): field
    # notation on the other package's type looks it up in that package's
    # namespace, so each vendored module using it gets an alias there
    cross_aliases = {}            # namespace to alias into -> {namespace aliased: shorts}
    _own_names = {c["name"] for c in own}
    for _n, _con in restated.items():
        if _n.startswith("_private."):
            continue              # private: never reached by field notation
        _parents = [l for l in restated if l != _n and _n.startswith(l + ".")]
        _con_ns, _short = _con.rpartition(".")[0], _con.rpartition(".")[2]
        if _parents:
            _lib = max(_parents, key=len)
            _rest = _n[len(_lib) + 1:]
            _expected = restated[_lib] + ("." + _rest.rpartition(".")[0] if "." in _rest else "")
        else:
            # a restated declaration under a namespace the library does not
            # restate: Mathlib's (`List.addKV`), where field notation looks
            # it up unchanged, or a vendored library type's, looked up under
            # the proofs package's name for that type
            _ns = _n.rpartition(".")[0]
            if not _ns:
                continue
            if _ns in _own_names:
                _expected = (f"{pname}.{_ns}" if _ns.startswith(args.prefix + ".")
                             else f"{pname}.Foreign.{_ns}")
            else:
                _expected = _ns
        if _con_ns != _expected:
            cross_aliases.setdefault(_expected, {}).setdefault(_con_ns, set()).add((_n, _short))
    def within(n, lib):
        return n == lib or n.startswith(lib + ".")
    def mapped_under(n):
        """The longest mapped declaration `n` is, or is a descendant of."""
        best = None
        for lib in restated:
            if within(n, lib) and (best is None or len(lib) > len(best)):
                best = lib
        return best
    def restated_name(n):
        lib = mapped_under(n)
        return restated[lib] + n[len(lib):] if lib else None
    GENERATED = re.compile(r"\.(rec|recOn|casesOn|noConfusion|noConfusionType|below|brecOn|ibelow|"
                           r"binductionOn|mk\.(inj|injEq|sizeOf_spec)|sizeOf_spec|match_\d+|proof_\d+|"
                           r"eq_\d+|eq_def|ext|ext_iff|inj|injEq|ctorIdx|ofNat_ctorIdx|toCtorIdx|ofNat)$")
    concept_modules = sorted({".".join(v.split(".")[:2]) for v in restated.values()})
    substituted = {}            # library constant -> concept constant
    restated_cmds = {}          # module -> the commands the concepts replace, in order
    EXPANDED_DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
                               r"(?:def|abbrev|inductive|structure|class|instance|theorem)\s+([\w.']+)", re.M)
    for mod, (text, byte_to_char, refs, keep) in list(decisions.items()):
        defined = {n: r["definition"] for n, r in refs.items()
                   if r["module"] == mod and r.get("definition") and not n.startswith("_private.")}
        def cmd_index(line0):
            for i, c in enumerate(keep):
                if c["kind"] != "header" and c["line"] <= line0 + 1 <= c["endLine"]:
                    return i
            return None
        # constants a library-defined command declares through its recorded
        # expansion carry no definition record of their own (`fo_predicates`
        # writes its shorthands without source positions): attribute them to
        # the command, under the namespace open at it
        declared_by = {}            # command index -> constants it declares
        for i, c in enumerate(keep):
            exp = c.get("expansion")
            if not exp or c["kind"].startswith("Lean.Parser.Command."):
                continue
            ns = []
            for d in keep[:i]:
                if d["kind"] == "Lean.Parser.Command.namespace":
                    ns.append(("namespace", text[byte_to_char[d["start"]]:byte_to_char[d["end"]]].split()[1]))
                elif d["kind"] in ("Lean.Parser.Command.section", "Lean.Parser.Command.noncomputableSection"):
                    ns.append(("section", ""))
                elif d["kind"] == "Lean.Parser.Command.end" and ns:
                    ns.pop()
            cur = ".".join(n for k, n in ns if k == "namespace")
            for e in exp:
                for m in EXPANDED_DECL.finditer(e):
                    name = m.group(1)
                    full = name[6:] if name.startswith("_root_.") else (f"{cur}.{name}" if cur else name)
                    declared_by.setdefault(i, set()).add(full)
        for n, d in defined.items():
            i = cmd_index(d[0])
            if i is not None:
                declared_by.setdefault(i, set()).add(n)
        to_drop = set()
        for i, names in declared_by.items():
            if not any(n in restated for n in names):
                continue
            n = next(n for n in names if n in restated)
            # the command is dropped whole, so every constant it declares
            # must have a concept counterpart: mapped itself, generated from
            # a mapped one (a constructor, a projection), or auto-generated
            siblings = sorted(names)
            missing = [m for m in siblings if restated_name(m) is None and not GENERATED.search(m)]
            if missing:
                sys.exit(f"restated: the command declaring {n} in {mod} also declares {missing}, which "
                         f"must be restated too (map them in `restated`)")
            to_drop.add(i)
            keep[i]["restated_defs"] = {m: restated_name(m) for m in siblings if restated_name(m)}
            for m in siblings:
                substituted[m] = restated_name(m) or m
        if to_drop:
            restated_cmds[mod] = [keep[i] for i in sorted(to_drop)]
            decisions[mod] = (text, byte_to_char, refs, [c for i, c in enumerate(keep) if i not in to_drop])
            stats["restated_dropped"] = stats.get("restated_dropped", 0) + len(to_drop)
    all_defined = {n for m, (_, _, refs, _) in decisions.items()
                   for n, r in refs.items() if r["module"] == m and r.get("definition")}
    def substitute(n):
        # a constant the dropped command generated without a definition
        # record of its own (`Config.mk.injEq`) follows its parent
        if n in substituted:
            return substituted[n]
        return restated_name(n) if n not in all_defined else None
    def case_alternative(a):
        """The token at `a` names an alternative of `cases … with | old => …`
        or a `match` arm, where only a constructor's short name is legal:
        left as written."""
        ls = text.rfind("\n", 0, a) + 1
        le = text.find("\n", a)
        le = len(text) if le == -1 else le
        return re.search(r"\|\s*@?\s*$", text[ls:a]) is not None and "=>" in text[a:le]

    def field_binder(a, b, n):
        """`state := …` or `relFormula R t := …` in a structure instance
        names a field, not a use: a bare field name opening its line (or
        following `{` or `,`), with `:=` later on the line."""
        tok = text[a:b]
        if "." in tok or not (n.rpartition(".")[0] in substituted or n.rpartition(".")[0] in foreign):
            return False
        before = text[text.rfind("\n", 0, a) + 1:a]
        nl = text.find("\n", b)
        after = text[b:nl if nl >= 0 else len(text)]
        if re.search(r"(?:^|[{,])\s*$", before) is None:
            return False
        if ":=" in after:
            return True
        # a field given by match alternatives: `arity` alone on its line,
        # the alternatives `| .elt => 1` following
        return after.strip() == "" and nl >= 0 and re.match(r"\s*\|", text[nl + 1:nl + 200]) is not None

    # foreign-namespace constants: declared by a kept command of a vendored
    # module, outside the prefix, not private; the earlier set from the
    # closure misses declarations kept by the silent rule.
    foreign = set()
    for mod, (text, byte_to_char, refs, keep) in decisions.items():
        kept_ranges = [(c["line"], c["endLine"]) for c in keep if c["kind"] != "header"]
        for n, r in refs.items():
            d = r.get("definition")
            if r["module"] != mod or not d or n.startswith(pfx + ".") or n.startswith("_private."):
                continue
            if any(a <= d[0] + 1 <= b for a, b in kept_ranges):
                foreign.add(n)
    # plus what the closure selected outside the prefix: constants a
    # library-defined command generated have no definition record of their own
    foreign |= {n for n in selected if not n.startswith(pfx + ".") and not n.startswith("_private.")}
    foreign = {n for n in foreign if substitute(n) is None}
    memo = {}
    def below(mod):
        if mod in memo:
            return memo[mod]
        memo[mod] = (set(), set())
        own_acc, ext_acc = set(), set()
        for i in imports_of(mod):
            if not i.startswith(pfx + "."):
                ext_acc.add(i)
            elif i in vendored:
                own_acc.add(i)
            else:
                o, e = below(i)
                own_acc |= o; ext_acc |= e
        memo[mod] = (own_acc, ext_acc)
        return memo[mod]

    # 3 - 5. rename, expand, rewrite imports, assemble; the vendored tree is
    # regenerated from scratch, so a module that left the closure disappears
    import shutil
    shutil.rmtree(os.path.join(args.out, "proofs", pname, pfx), ignore_errors=True)
    for stale in (os.path.join(args.out, "proofs", pname, pfx + ".lean"),):
        if os.path.isfile(stale):
            os.remove(stale)
    for mod, (text, byte_to_char, refs, keep) in decisions.items():
        line_starts = [0]
        for i, ch in enumerate(text):
            if ch == "\n":
                line_starts.append(i + 1)
        def at(line0, col16):
            i = line_starts[line0]
            units = 0
            while units < col16 and i < len(text) and text[i] != "\n":
                units += 2 if ord(text[i]) > 0xFFFF else 1
                i += 1
            return i
        def command_of(line0):
            for idx, c in enumerate(keep):
                if c["line"] <= line0 + 1 <= c["endLine"]:
                    return idx
            return None
        patches = []
        exports = {}
        aliases = {}          # concept namespace -> {short: (position, proofs namespace)}
        defs_here = {n: refs[n]["definition"] for n in foreign
                     if refs.get(n) and refs[n].get("definition")}
        # uses of restated constants: the concept's name, wherever written
        for n, r in refs.items():
            new = substitute(n)
            if new is None:
                continue
            for u in r["usages"]:
                if u[0] != u[2]:
                    continue
                a = at(u[0], u[1]); b = at(u[2], u[3])
                tok = text[a:b]
                if tok.startswith("_root_."):
                    tok = tok[len("_root_."):]      # `_root_.name`: patched whole
                    if n != tok:
                        continue
                elif not (n == tok or n.endswith("." + tok)) or (a > 0 and text[a - 1] == "."):
                    continue
                if field_binder(a, b, n) or case_alternative(a):
                    continue
                patches.append((a, b, new))
        # a kept library declaration under a restated namespace, a theorem about
        # the restated structure say: an alias at the concept's namespace, so
        # that field notation on the concept type finds it
        for n, r in refs.items():
            d = r.get("definition")
            if not d or r["module"] != mod or n.startswith("_private.") or substitute(n) is not None:
                continue
            lib = mapped_under(n)
            if lib and lib != n and d[0] == d[2]:
                con = restated[lib]
                rest = n[len(lib) + 1:]
                ns_concept = con + ("." + rest.rpartition(".")[0] if "." in rest else "")
                short = rest.rpartition(".")[2]
                proofs_ns = (f"{pname}.{n.rpartition('.')[0]}" if n.startswith(pfx + ".")
                             else f"{pname}.Foreign{'.' + n.rpartition('.')[0] if n.rpartition('.')[0] else ''}")
                aliases.setdefault(ns_concept, {})[short] = (at(d[0], d[1]), proofs_ns)
        for n in foreign:
            r = refs.get(n)
            if not r:
                continue
            new = f"{pname}.Foreign.{n}"
            for u in r["usages"]:
                l0, c0, l1, c1 = u[0], u[1], u[2], u[3]
                if l0 != l1:
                    continue
                a = at(l0, c0); b = at(l1, c1)
                tok = text[a:b]
                if not (n == tok or n.endswith("." + tok)) or (a > 0 and text[a - 1] == "."):
                    # a dot-identifier (`.isClause`), a token under some
                    # notation, or generalized field notation (`t.varOf`):
                    # left as written, resolved through the `export` alias
                    stats["aliased"] = stats.get("aliased", 0) + 1
                    continue
                if field_binder(a, b, n) or case_alternative(a):
                    continue
                patches.append((a, b, new))
            d = r.get("definition")
            if d and d[0] == d[2]:
                # A constructor, field or projection is declared inside its
                # parent's command and named after it: the parent's rooting
                # carries it, so it is not patched itself.
                parent = next((m for m, dm in defs_here.items()
                               if n.startswith(m + ".") and command_of(dm[0]) == command_of(d[0])), None)
                if parent:
                    continue
                a = at(d[0], d[1]); b = at(d[2], d[3])
                tok = text[a:b]
                if n == tok or n.endswith("." + tok):
                    patches.append((a, b, f"_root_.{new}"))
                    ns, _, short = n.rpartition(".")
                    exports.setdefault(ns, {})[short] = a
                elif tok == "instance" or tok in GENERATING_ATTRIBUTES or not re.fullmatch(r"[\w.'«»]+", tok):
                    # an unnamed instance (named below), a lemma an attribute
                    # generated (`@[simps]` records its lemmas at the
                    # attribute's token), or a declaration without an id of
                    # its own: nothing to patch
                    pass
                else:
                    # a declaration id that does not read as its constant's
                    # name means the build is of other sources
                    stats["mismatch"] = stats.get("mismatch", 0) + 1
                    stats["unpatched"].append((mod, n, "definition " + tok))
        patches.sort()
        pieces = []
        depth = []            # [kind, name, scaffolding chunks executed at that level]
        REPLAY = {"Lean.Parser.Command.open", "Lean.Parser.Command.variable", "Lean.Parser.Command.universe",
                  "Lean.Parser.Command.set_option", "Lean.Parser.Command.omit", "Lean.Parser.Command.include"}
        def current_ns():
            return ".".join(n for kind, n, _ in depth if kind == "namespace")
        def jump(body_text, derived=False, namespace=None, replay=False):
            """Declare `body_text` outside the current namespace chain: close
            every level, open a jump namespace, close it, reopen the levels
            and replay the scaffolding each had executed, which closing them
            discarded. The jump namespace is the package's foreign namespace
            for the chain, so that declarations inside get the names the
            usages were patched to; a derived instance only needs to be
            under the package, and its jump namespace is chosen so that
            relative names of the original block still resolve at the root
            (`{pname}.Foreign.FirstOrder` would capture `open FirstOrder`)."""
            cur = current_ns()
            closes = [f"end {name}" if name else "end" for kind, name, _ in reversed(depth)]
            reopens = []
            for kind, name, scaffold in depth:
                reopens.append(f"{kind} {name}" if name else kind)
                reopens.extend(scaffold)
            if namespace:
                # a declaration moved into the concept's namespace keeps the
                # scaffolding of the levels it was written under; an alias
                # needs none, and an `open` of a library namespace would not
                # resolve there
                ns_new = namespace
                inside = [c for _, _, sc in depth for c in sc] if replay else []
            elif derived:
                ns_new = f"{pname}.Derived"
                prefixes = [".".join(cur.split(".")[:i + 1]) for i in range(len(cur.split("."))) if cur]
                inside = ([f"open {' '.join(prefixes)}"] if prefixes else []) + \
                         [c for _, _, sc in depth for c in sc if c.startswith("open")]
            else:
                if cur == pfx or cur.startswith(pfx + "."):
                    ns_new = f"{pname}.{cur}"         # the library's own namespace, rewritten
                else:
                    ns_new = f"{pname}.Foreign.{cur}" if cur else f"{pname}.Foreign"
                inside = []
            return "\n\n".join(closes + [f"namespace {ns_new}"] + inside + [body_text, f"end {ns_new}"] + reopens)
        unprivate_lines = {r["definition"][0] + 1 for r in refs.values()
                           if r.get("unprivate") and r["module"] == mod and r.get("definition")}
        for cmd in keep:
            a, b = byte_to_char[cmd["start"]], byte_to_char[cmd["end"]]
            chunk = text[a:b]
            # uses of the library's syntax categories, replaced by the terms
            # they expanded to (outermost only), the ilean patches inside such
            # a range being replaced by a name-based rewrite of the expansion
            spans = sorted(((byte_to_char[m["start"]], byte_to_char[m["end"]], m["text"])
                            for m in cmd.get("macros", [])), key=lambda m: (m[0], -m[1]))
            outer, last_end = [], -1
            for ma, mb, mt in spans:
                if ma >= last_end:
                    outer.append((ma, mb, mt)); last_end = mb
            expanded = [(ma, mb) for ma, mb, _ in outer]
            def in_expansion(pos):
                return any(ma <= pos < mb for ma, mb in expanded)
            local = [p for p in patches if a <= p[0] and p[1] <= b and not in_expansion(p[0])]
            foreign_here = {n for n in foreign if refs.get(n)
                            for u in refs[n]["usages"] if u[0] == u[2] and in_expansion(at(u[0], u[1]))}
            edits = [(pa, pb, new) for pa, pb, new in local]
            for ma, mb, mt in outer:
                for n in foreign_here:
                    short = n.rpartition(".")[2]
                    mt = re.sub(r"(?<![\w.'])" + re.escape(short) + r"(?![\w'])", f"{pname}.Foreign.{n}", mt)
                # a restated declaration, printed in full or relative to an
                # open namespace: the concept's name
                for lib, con in sorted(restated.items(), key=lambda kv: -len(kv[0])):
                    for form in printed_forms(lib, pfx):
                        mt = re.sub(r"(?<![\w.'])" + re.escape(form) + r"(?![\w'])", con, mt)
                # a printed term may run over several lines; a continuation
                # at column 0 would end the enclosing block, so the whole
                # expansion is indented past the point it replaces
                col = ma - text.rfind("\n", 0, ma) - 1
                mt = mt.replace("\n", "\n" + " " * (col + 2))
                edits.append((ma, mb, mt))
                stats["expanded_uses"] = stats.get("expanded_uses", 0) + 1
            for pa, pb, new in sorted(edits, reverse=True):
                chunk = chunk[:pa - a] + new + chunk[pb - a:]
                stats["patched"] += 1
            k = cmd["kind"]
            open_in = re.match(r"(\s*)(open\b[^\n]*?\bin\b)", chunk)
            if k == "Lean.Parser.Command.open" or open_in:
                # a namespace opened by its library name: when it is the
                # namespace of a restated declaration, the concept's namespace
                # is what carries its contents now (the vendored package keeps
                # the name only if something of it stayed vendored)
                cur = current_ns()
                def reopen(m):
                    name = m.group(0)
                    for lib, con in restated.items():
                        if lib == f"{pfx}.{name}" or (cur and lib == f"{pfx}.{cur}.{name}") or lib == name:
                            vendored_too = any(n.startswith(lib + ".") and substitute(n) is None
                                               and refs.get(n, {}).get("definition") for n in refs)
                            stats["opens"] = stats.get("opens", 0) + 1
                            # what stayed vendored of a root-level namespace is rooted
                            # under the package's foreign names
                            vend = f"{pname}.Foreign.{name}" if lib == name else name
                            return f"{con} {vend}" if vendored_too else con
                    return name
                if open_in and k != "Lean.Parser.Command.open":
                    head, rest = open_in.group(1), open_in.group(2)[len("open"):]
                    tail = chunk[open_in.end():]
                else:
                    head, _, rest = chunk.partition("open")
                    tail = ""
                rest = re.sub(r"(?<![\w.'])[A-Za-z_][\w'.]*(?![\w'])",
                              lambda m: m.group(0) if m.group(0) in ("in", "scoped", "hiding", "renaming")
                              else reopen(m), rest)
                chunk = head + "open" + rest + tail
            if k == "Lean.Parser.Command.namespace":
                depth.append(["namespace", chunk.split()[1], []])
            elif k in ("Lean.Parser.Command.section", "Lean.Parser.Command.noncomputableSection"):
                parts = chunk.split()
                depth.append(["section", parts[1] if len(parts) > 1 and parts[0] == "section" else None, []])
            elif k == "Lean.Parser.Command.end" and depth:
                depth.pop()
            elif depth and (k in REPLAY or (k in ("Lean.Parser.Command.notation", "Lean.Parser.Command.macro",
                                                   "Lean.Parser.Command.mixfix")
                                             and re.match(r"\s*(local|scoped)\b", chunk))):
                depth[-1][2].append(chunk)
            # Foreign declarations this command makes, by the ilean records
            here = [n for n in foreign if refs.get(n) and refs[n].get("definition")
                    and a <= at(refs[n]["definition"][0], refs[n]["definition"][1]) < b]
            # `def Ns.f` opens `Ns` for its body, where constructor patterns and
            # sibling declarations are written by their short names; the
            # rooted copy opens what carries that namespace now, the concept's
            # for a restated type and the package's for what stayed vendored
            opens, inside = [], None
            for n in here:
                ns = n.rpartition(".")[0]
                if not ns:
                    continue
                if ns in restated and inside is None:
                    # inside the concept's namespace, not merely opening it: a
                    # constructor `Prod` must shadow the root's, as it did
                    inside = restated[ns]
                if ns in exports:
                    opens.append(f"{pname}.Foreign.{ns}")
            opens = [o for i, o in enumerate(opens) if o not in opens[:i]]
            if k not in SCAFFOLD:
                if opens:
                    chunk = f"open {' '.join(opens)} in\n" + chunk
                if inside:
                    chunk = jump(chunk, namespace=inside, replay=True)
            # An unnamed instance is named after the auto-generated name the
            # library's build gave it, rooted under the package.
            if here and re.search(r"\binstance\b(?:\s*(?:\([^)]*\)|\[[^\]]*\]|\{[^}]*\}))*\s*:", chunk):
                inst = [n for n in here if n.rpartition(".")[2].startswith("inst")]
                if inst:
                    def named(m):
                        # a priority stays before the name, binders go after it
                        binders = m.group(1).strip()
                        prio = re.match(r"\(\s*priority\s*:=[^)]*\)", binders)
                        if prio:
                            binders = binders[prio.end():].strip()
                        return (f"instance {prio.group(0) + ' ' if prio else ''}_root_.{pname}.Foreign.{inst[0]}"
                                f"{' ' + binders if binders else ''} :")
                    chunk = re.sub(r"\binstance((?:\s*(?:\([^)]*\)|\[[^\]]*\]|\{[^}]*\}))*\s*):", named, chunk, count=1)
            # A `deriving` clause on a rooted inductive would name its
            # instance in the enclosing namespace: it is derived under the
            # package's namespace instead.
            m = re.search(r"\n\s*deriving\s+([^\n]+)$", chunk)
            if m and here:
                rooted = [n for n in here if f"_root_.{pname}.Foreign.{n}" in chunk]
                if rooted:
                    chunk = chunk[:m.start()]
                    classes = [c.strip() for c in m.group(1).split(",")]
                    body_text = "\n".join(f"deriving instance {c} for {pname}.Foreign.{rooted[0]}" for c in classes)
                    chunk = chunk + "\n\n" + jump(body_text, derived=True)
            alias_lines = []
            for ns_concept, shorts in aliases.items():
                here = {sh: pns for sh, (pos, pns) in shorts.items() if a <= pos < b}
                if not here:
                    continue
                by_pns = {}
                for sh, pns in here.items():
                    by_pns.setdefault(pns, []).append(sh)
                body_text = "\n".join(f"export {pns} ({' '.join(sorted(shs))})" for pns, shs in by_pns.items())
                alias_lines.append(jump(body_text, namespace=ns_concept))
            for ns, shorts in exports.items():
                here = [sh for sh, pos in shorts.items() if a <= pos < b]
                if not here:
                    continue
                cur = current_ns()
                if ns == cur:
                    rel = None
                elif cur == "" or ns.startswith(cur + "."):
                    rel = ns[len(cur) + 1:] if cur else ns
                else:
                    stats["unpatched"].append((mod, ns, "export outside its namespace")); continue
                line = f"export {pname}.Foreign{'.' + ns if ns else ''} ({' '.join(sorted(here))})"
                alias_lines.append(line if rel is None else f"namespace {rel}\n{line}\nend {rel}")
            expansion = cmd.get("expansion")
            if (expansion and not k.startswith("Lean.Parser.Command.")
                    and all("<missing>" not in e for e in expansion)):
                texts = [re.sub(r"(?<!^)(?<!\n)(?<!\s)(/--)", r"\n\1", e) for e in expansion]
                body_exp = "\n\n".join(texts)
                def printed_code(seg):
                    # the elaborator printed names in full or relative to an
                    # open namespace: restated ones become the concept's,
                    # foreign ones are rooted
                    for lib, con in sorted(restated.items(), key=lambda kv: -len(kv[0])):
                        for form in printed_forms(lib, pfx):
                            seg = re.sub(r"(?<![\w.'])" + re.escape(form) + r"(?![\w'])", con, seg)
                    for n in sorted(foreign, key=len, reverse=True):
                        seg = seg.replace(f"_root_.{n}", f"_root_.{pname}.Foreign.{n}")
                        for form in printed_forms(n, pfx):
                            seg = re.sub(r"(?<![\w.'])" + re.escape(form) + r"(?![\w'])",
                                         f"_root_.{pname}.Foreign.{n}", seg)
                    return seg
                body_exp = "".join(part if part.startswith("/--") else printed_code(part)
                                   for part in re.split(r"(/--.*?-/)", body_exp, flags=re.S))
                chunk = jump(body_exp)
                stats["expanded"] += 1
            if k == "header":
                lines = []
                for line in chunk.split("\n"):
                    m = re.match(r"import\s+(\S+)", line)
                    if m and m.group(1).startswith(pfx + "."):
                        i = m.group(1)
                        if i in vendored:
                            lines.append(line)
                        else:
                            o, e = below(i)
                            for j in sorted(e) + sorted(o):
                                if f"import {j}" not in lines:
                                    lines.append(f"import {j}")
                        continue
                    if line not in lines or not line.startswith("import "):
                        lines.append(line)
                for cm in concept_modules:
                    if f"import {cm}" not in lines:
                        lines.append(f"import {cm}")
                chunk = "\n".join(lines)
                # `export` needs its source namespace registered, which a
                # `_root_`-named declaration does not do and which `namespace`
                # does only relative to the current one: register at the top,
                # where the module is still at the root
                register = {pns for shorts in aliases.values() for _, pns in shorts.values()}
                register |= {f"{pname}.Foreign.{ns}" if ns else f"{pname}.Foreign" for ns in exports}
                # the concept's namespace of a restated declaration, opened by
                # the rooted declarations under it, which a plain `def` has not
                register |= {restated[ns] for ns in exports if ns in restated}
                cross_blocks = []
                for _ns, _by in cross_aliases.items():
                    for _con_ns, _pairs in _by.items():
                        _used = sorted({sh for n, sh in _pairs if n in refs})
                        if _used:
                            register.add(_con_ns)
                            cross_blocks.append(f"namespace {_ns}\nexport {_con_ns} ({' '.join(_used)})\nend {_ns}")
                            stats["aliased"] = stats.get("aliased", 0) + len(_used)
                for r in sorted(register):
                    chunk += f"\n\nnamespace {r}\nend {r}"
                for blk in cross_blocks:
                    chunk += "\n\n" + blk
            if k != "header" and any(cmd["line"] <= ln <= cmd["endLine"] for ln in unprivate_lines):
                # the vendored copy of a private declaration written outside
                # the library's namespace is not private, and its name is
                # rooted under the package like every other
                chunk = re.sub(r"(^|\n)([ \t]*)private\s+", r"\1\2", chunk)
            if k in NOTATION_KINDS and not current_ns():
                # the syntax declarations a notation command makes are named
                # in the current namespace, which must be under the package:
                # at the root it is not
                chunk = f"namespace {pname}\n{chunk}\nend {pname}"
            pieces.append(chunk)
            pieces.extend(alias_lines)
        body = "\n\n".join(pieces)
        body = prefix_rewrite(body)
        if header_opts:
            lines = body.split("\n")
            last = max((i for i, l in enumerate(lines) if l.startswith("import ")), default=-1)
            body = "\n".join(lines[:last + 1]) + "\n\n" + header_opts + "\n".join(lines[last + 1:])
        new_mod = f"{pname}.{mod}"
        write(os.path.join(args.out, "proofs", *new_mod.split(".")) + ".lean", body + "\n")
        stats["lines"] += body.count("\n") + 1
    if args.skeleton:
        notation_mods = {m for m, d in commands.items()
                         if any(c["kind"] in META for c in d["commands"])}
        write_skeletons(args, cname, pfx, restated, restated_cmds, decisions, commands, imports_of, below,
                        lambda mod: list_commands_expanded(mod, notation_mods))
    modules = sorted(vendored)
    print(f"{len(modules)} modules written: kept {stats['kept']} declaration commands, dropped {stats['dropped']}, "
          f"{stats['lines']} lines, {stats['instances']} silent declarations kept, {stats['expanded']} commands expanded, "
          f"{stats['patched']} foreign-name patches, {stats.get('aliased', 0)} uses through aliases, "
          f"{stats.get('restated_dropped', 0)} restated declarations taken from the concepts",
          file=sys.stderr)
    for u in sorted(set(stats["unpatched"])):
        print("  not handled:", u, file=sys.stderr)
    if stats.get("mismatch", 0):
        sys.exit(f"{stats['mismatch']} declaration ids do not match their constants' names: the build under "
                 f"{args.library} is not a build of the sources exported (ref {args.ref or 'working tree'})")

    # 6. layout, in the folder `lax init` made: the generated files are
    # rewritten, the hand-written modules (concepts in concepts/LaxN/, bridge
    # proofs in proofs/LaxNProofs/ outside the vendored tree) are kept and
    # imported, and what `lax submit` wrote into the manifest is preserved
    concept_dir = os.path.join(args.out, "concepts", cname)
    concept_mods = sorted(f"{cname}." + os.path.relpath(f, concept_dir)[:-5].replace(os.sep, ".")
                          for f in glob.glob(os.path.join(concept_dir, "**", "*.lean"), recursive=True))
    write(os.path.join(args.out, "concepts", f"{cname}.lean"),
          "".join(f"import {m}\n" for m in concept_mods) or "-- the concept modules go in this folder\n")
    required = "".join(f'\n[[require]]\nname = "{r["package"]}"\ngit = "{r["repository"]}"\n'
                       f'rev = "{r["commit"]}"\nsubDir = "{r["folder"]}/concepts"\n'
                       for r in args.requires)
    write(os.path.join(args.out, "concepts", "lakefile.toml"),
          LAKEFILE.format(name=cname, mathlib=MATHLIB_URL, rev=args.mathlib_rev, extra=required))
    write(os.path.join(args.out, "concepts", "lean-toolchain"), toolchain + "\n")
    proofs_dir = os.path.join(args.out, "proofs", pname)
    vendored_mods = [f"{pname}.{m}" for m in modules]
    bridge_mods = sorted(f"{pname}." + os.path.relpath(f, proofs_dir)[:-5].replace(os.sep, ".")
                         for f in glob.glob(os.path.join(proofs_dir, "**", "*.lean"), recursive=True)
                         if not os.path.relpath(f, proofs_dir).startswith(pfx + os.sep)
                         and os.path.relpath(f, proofs_dir) != pfx + ".lean")
    extra = f'\n[[require]]\nname = "{cname}"\npath = "../concepts"\n' + required
    write(os.path.join(args.out, "proofs", "lakefile.toml"),
          LAKEFILE.format(name=pname, mathlib=MATHLIB_URL, rev=args.mathlib_rev, extra=extra))
    write(os.path.join(args.out, "proofs", "lean-toolchain"), toolchain + "\n")
    write(os.path.join(args.out, "proofs", f"{pname}.lean"),
          "".join(f"import {m}\n" for m in vendored_mods + bridge_mods))
    manifest = {"specVersion": "1", "id": sub_id,
                "leanVersion": toolchain.split(":")[-1], "mathlibVersion": mathlib_rev}
    for key in ("title", "authors", "bibEntries"):
        manifest[key] = args.manifest.get(key, existing.get(key, [] if key != "title" else sub_id))
    for key in ("supersedes", "unlisted", "anonymous", "paper", "issue", "initialOwners"):
        if key in args.manifest:
            manifest[key] = args.manifest[key]
        elif key in existing:                      # `issue` is what lax submit wrote
            manifest[key] = existing[key]
    write(os.path.join(args.out, "manifest.yaml"), dump_manifest(manifest))
    write_licenses(args.src, args.out, args.copyright, args.force_license, args.notice)
    if not os.path.isfile(os.path.join(args.out, ".gitignore")):
        write(os.path.join(args.out, ".gitignore"), "build-output.json\nlake-manifest.json\n.lake/\n")
    print(f"{len(concept_mods)} concept modules and {len(bridge_mods)} bridge modules found in place",
          file=sys.stderr)

if __name__ == "__main__":
    main()
