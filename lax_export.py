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


def rewriter(prefix, new_prefix):
    # The prefix as a whole name component: not preceded by a name character
    # or a dot, except the explicit root marker `_root_.`, and followed by a
    # dot or a non-name character.
    pat = re.compile(r"(?:(?<=_root_\.)|(?<![\w.']))" + re.escape(prefix) + r"(?![\w'])")
    return lambda text: pat.sub(new_prefix, text)


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


def write_licenses(src, out, copyright_line, force):
    """The Lax accepts exactly one license for a submission, Apache 2.0,
    with at most one trailing copyright line. The vendored code keeps its
    own headers; when the library's license is a permissive one that
    permits sublicensing, its text goes into NOTICE beside the Apache text;
    a library under any other license is refused unless forced."""
    apache = open(os.path.join(HERE, "LICENSE"), encoding="utf-8").read()
    text = apache + (f"\nCopyright {copyright_line}\n" if copyright_line else "")
    write(os.path.join(out, "LICENSE"), text)
    path = os.path.join(src, "LICENSE")
    if not os.path.isfile(path):
        print("warning: the library has no LICENSE file; the submission's NOTICE cannot name its terms",
              file=sys.stderr)
        return
    lib = open(path, encoding="utf-8").read()
    if re.search(r"Apache License\s+Version 2\.0", lib):
        return                                                         # same license, nothing to add
    kind = next((k for k, pat in PERMISSIVE.items() if re.search(pat, lib)), None)
    if kind is None and not force:
        sys.exit("the library's LICENSE is neither Apache 2.0 nor a permissive license that permits "
                 "sublicensing (MIT, BSD, ISC, 0BSD, Unlicense, CC0): the Lax archive requires Apache 2.0 "
                 "for the submission, so it cannot be built from this library; --force-license overrides")
    write(os.path.join(out, "NOTICE"),
          "The Lean code under proofs/ is derived from a library distributed under the "
          f"following license{' (' + kind + ')' if kind else ''}, whose notices the vendored "
          "files retain. This submission is distributed under the Apache License 2.0, see LICENSE.\n\n"
          + lib)


MANIFEST_KEYS = {"id", "title", "authors", "bibEntries", "supersedes", "unlisted", "anonymous",
                 "issue", "paper", "initialOwners"}
CONFIG_KEYS = {"library", "ref", "prefix", "targets", "options", "whole_modules",
               "copyright", "force_license", "env", "manifest", "out", "restated"}


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
    return {
        "restated": restated,
        "library": raw["library"] if is_url(str(raw["library"])) else rel(raw["library"]),
        "ref": raw.get("ref"),
        "prefix": raw["prefix"],
        "target": list(raw["targets"]),
        "set_option": list(raw.get("options", [])),
        "whole_modules": bool(raw.get("whole_modules", False)),
        "copyright": raw.get("copyright"),
        "force_license": bool(raw.get("force_license", False)),
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


def dump_manifest(manifest):
    return yaml.safe_dump(_mark(manifest), sort_keys=False, allow_unicode=True,
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


def ilean(build, mod):
    p = os.path.join(build, *mod.split(".")) + ".ilean"
    if not os.path.isfile(p):
        return {}
    d = json.load(open(p, encoding="utf-8"))
    out = {}
    for k, v in d["references"].items():
        c = json.loads(k)["c"]
        out[c["n"]] = {"module": c["m"], "definition": v.get("definition"),
                       "usages": v.get("usages", [])}
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
    args = ap.parse_args()

    cfg = load_config(args.config)
    args.out = os.path.abspath(args.out or cfg["out"])
    for key in ("prefix", "target", "set_option", "whole_modules",
                "copyright", "force_license", "env", "manifest", "library", "ref", "restated"):
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
        run(["lean", "--run", slice_lean, "closure", pfx, plan] + sorted(targets), args.src, env)
        return json.load(open(plan, encoding="utf-8"))

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
        r"^\s*(?:/-[-!]?.*?-/\s*)?(?P<attrs>(?:@\[[^\]]*\]\s*)*)"
        r"(?:noncomputable\s+|protected\s+|private\s+|scoped\s+|local\s+|unsafe\s+)*"
        r"(?P<kw>instance|theorem|lemma|def|abbrev)\b", re.S)
    silent_attrs = re.compile(r"\b(simp|simps|ext|norm_cast|refl|trans|symm|aesop|coe|reducible|instance)\b")
    stats = {"kept": 0, "dropped": 0, "lines": 0, "patched": 0, "unpatched": [], "instances": 0, "expanded": 0}
    decisions = {}            # module -> (text, byte_to_char, refs, keep list)
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
        def mentions_unselected(cmd):
            for ln in range(cmd["line"], cmd["endLine"] + 1):
                for n, _ in uses_by_line.get(ln, []):
                    if n not in selected:
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
            else:
                stats["dropped"] += 1
        if content:
            decisions[mod] = (text, byte_to_char, refs, keep)
    vendored = set(decisions)

    # Declarations the concepts restate verbatim (`restated`): the library's
    # copy is dropped, every constant the declaring command generates is
    # renamed to the concept's, and every use is patched. A concept name is
    # relative to this submission's concept package unless it names another
    # Lax package outright.
    restated = {}
    for k, v in args.restated.items():
        if re.match(r"Lax\d+\.", v):
            if not v.startswith(cname + "."):
                sys.exit(f"restated: {v} is not a declaration of the concept package {cname} "
                         "(concept dependencies are not supported yet)")
            restated[k] = v
        else:
            restated[k] = f"{cname}.{v}"
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
    for mod, (text, byte_to_char, refs, keep) in list(decisions.items()):
        defined = {n: r["definition"] for n, r in refs.items()
                   if r["module"] == mod and r.get("definition") and not n.startswith("_private.")}
        def cmd_index(line0):
            for i, c in enumerate(keep):
                if c["kind"] != "header" and c["line"] <= line0 + 1 <= c["endLine"]:
                    return i
            return None
        to_drop = set()
        for n, d in defined.items():
            if n not in restated:
                continue
            i = cmd_index(d[0])
            if i is None:
                continue
            # the command is dropped whole, so every constant it declares
            # must have a concept counterpart: mapped itself, generated from
            # a mapped one (a constructor, a projection), or auto-generated
            siblings = [m for m, dm in defined.items() if cmd_index(dm[0]) == i]
            missing = [m for m in siblings if restated_name(m) is None and not GENERATED.search(m)]
            if missing:
                sys.exit(f"restated: the command declaring {n} in {mod} also declares {missing}, which "
                         f"must be restated too (map them in `restated`)")
            to_drop.add(i)
            for m in siblings:
                substituted[m] = restated_name(m) or m
        if to_drop:
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
    def field_binder(a, b, n):
        """`state := …` or `relFormula R t := …` in a structure instance
        names a field, not a use: a bare field name opening its line (or
        following `{` or `,`), with `:=` later on the line."""
        tok = text[a:b]
        if "." in tok or not (n.rpartition(".")[0] in substituted or n.rpartition(".")[0] in foreign):
            return False
        before = text[text.rfind("\n", 0, a) + 1:a]
        after = text[b:text.find("\n", b) if text.find("\n", b) >= 0 else len(text)]
        return re.search(r"(?:^|[{,])\s*$", before) is not None and ":=" in after

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
                if not (n == tok or n.endswith("." + tok)) or (a > 0 and text[a - 1] == "."):
                    continue
                if field_binder(a, b, n):
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
                             else f"{pname}.Foreign.{n.rpartition('.')[0]}")
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
                if field_binder(a, b, n):
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
                elif tok == "instance" or not re.fullmatch(r"[\w.'«»]+", tok):
                    # an unnamed instance (named below) or a declaration
                    # without an id of its own: nothing to patch
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
        def jump(body_text, derived=False, namespace=None):
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
                ns_new = namespace
                inside = []
            elif derived:
                ns_new = f"{pname}.Derived"
                prefixes = [".".join(cur.split(".")[:i + 1]) for i in range(len(cur.split("."))) if cur]
                inside = ([f"open {' '.join(prefixes)}"] if prefixes else []) + \
                         [c for _, _, sc in depth for c in sc if c.startswith("open")]
            else:
                ns_new = f"{pname}.Foreign.{cur}" if cur else f"{pname}.Foreign"
                inside = []
            return "\n\n".join(closes + [f"namespace {ns_new}"] + inside + [body_text, f"end {ns_new}"] + reopens)
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
                edits.append((ma, mb, mt))
                stats["expanded_uses"] = stats.get("expanded_uses", 0) + 1
            for pa, pb, new in sorted(edits, reverse=True):
                chunk = chunk[:pa - a] + new + chunk[pb - a:]
                stats["patched"] += 1
            k = cmd["kind"]
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
            # An unnamed instance is named after the auto-generated name the
            # library's build gave it, rooted under the package.
            if here and re.search(r"\binstance\s*(?:\([^)]*\)\s*)?:", chunk):
                inst = [n for n in here if n.rpartition(".")[2].startswith("inst")]
                if inst:
                    def named(m):
                        prio = m.group(1).strip()
                        return f"instance {prio + ' ' if prio else ''}_root_.{pname}.Foreign.{inst[0]} :"
                    chunk = re.sub(r"\binstance(\s*(?:\([^)]*\)\s*)?):", named, chunk, count=1)
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
                line = f"export {pname}.Foreign.{ns} ({' '.join(sorted(here))})"
                alias_lines.append(line if rel is None else f"namespace {rel}\n{line}\nend {rel}")
            expansion = cmd.get("expansion")
            if (expansion and not k.startswith("Lean.Parser.Command.")
                    and all("<missing>" not in e for e in expansion)):
                texts = [re.sub(r"(?<!^)(?<!\n)(?<!\s)(/--)", r"\n\1", e) for e in expansion]
                body_exp = "\n\n".join(texts)
                for n in foreign:
                    body_exp = body_exp.replace(f"_root_.{n}", f"_root_.{pname}.Foreign.{n}")
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
    write(os.path.join(args.out, "concepts", "lakefile.toml"),
          LAKEFILE.format(name=cname, mathlib=MATHLIB_URL, rev=args.mathlib_rev, extra=""))
    write(os.path.join(args.out, "concepts", "lean-toolchain"), toolchain + "\n")
    proofs_dir = os.path.join(args.out, "proofs", pname)
    vendored_mods = [f"{pname}.{m}" for m in modules]
    bridge_mods = sorted(f"{pname}." + os.path.relpath(f, proofs_dir)[:-5].replace(os.sep, ".")
                         for f in glob.glob(os.path.join(proofs_dir, "**", "*.lean"), recursive=True)
                         if not os.path.relpath(f, proofs_dir).startswith(pfx + os.sep)
                         and os.path.relpath(f, proofs_dir) != pfx + ".lean")
    extra = f'\n[[require]]\nname = "{cname}"\npath = "../concepts"\n'
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
    write_licenses(args.src, args.out, args.copyright, args.force_license)
    if not os.path.isfile(os.path.join(args.out, ".gitignore")):
        write(os.path.join(args.out, ".gitignore"), "build-output.json\nlake-manifest.json\n.lake/\n")
    print(f"{len(concept_mods)} concept modules and {len(bridge_mods)} bridge modules found in place",
          file=sys.stderr)

if __name__ == "__main__":
    main()
