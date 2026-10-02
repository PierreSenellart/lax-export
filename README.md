# lax-export

Publish theorems of an existing Lean library on the [Lax Lean
Archive](https://laxarchive.org/).

Lax admits no requirement beyond Mathlib and other Lax packages, so a
submission whose proofs rest on a library must carry a copy of what it
uses. `lax-export` simplifies the process of creating such a submission
from an existing Lean libary, by packaging the declarations in the
proof-term closure of the submitted theorems rewritten into a Lax proofs
package under the submission's namespace. The hand-written parts of a
submission, the concept files stating the claims and the bridge proofs
discharging them from the vendored library, are copied in from
directories you provide.

## Requirements

- the Lax tool, `npm install -g lax-archive` with Node 20 or later, then
  `lax doctor` once per machine: it makes the submission folder and draws
  its id (`lax init`), validates the result as the archive will (`lax
  build`), previews it (`lax serve`) and submits it;
- the library's toolchain: `lean` and `lake` on `PATH` (the tool runs
  `Slice.lean` with `lean --run`, and builds with `lake` when it has to);
- Python 3.8 or later with PyYAML;
- network access, for the Lax archive's environment list, Mathlib's tag
  and, when a build is needed, `lake exe cache get`.

## Usage

The submission folder is the one the Lax tool makes, and `lax-export` works
inside it:

```
lax init my-submission                 # draws the id, writes the scaffold
cp …/export.yaml my-submission/        # the export's description, see below
lax_export.py my-submission/export.yaml
```

The tool reads the id from the folder's `manifest.yaml`, rewrites the
generated files (lakefiles, toolchain files, root modules, manifest,
abstract, license), and writes the vendored library under
`proofs/LaxNProofs/<prefix>/`. Everything hand-written lives in the same
folder and is left alone: the concept modules in `concepts/LaxN/`, the
bridge proofs anywhere in `proofs/LaxNProofs/` outside the vendored tree;
the root modules import whatever is there. Running the tool again replaces
the vendored tree and nothing else. Whatever `lax submit` adds to the
manifest, the `issue` binding above all, is preserved.

Then, with the Lax tool: `lax build` to validate as the archive will, `lax
serve` to read the pages, `lax submit` for a draft, `lax register` when
final. The export file can stay in the folder: the archive allows extra
root-level files.

### The export file

Paths are relative to the file. `examples/np-core.yaml` is a complete one.

The library and what to export:

- `library` (required): a local git checkout of the library, or any URL
  `git clone` accepts.
- `ref`: the git ref to export, a tag, branch or commit. Default: HEAD of a
  local checkout, the default branch of a repository URL.
- `prefix` (required): the library's top-level namespace, which is also its
  module root (`MyLib` for modules `MyLib.…`). Every declaration of the
  library is expected under it, foreign-namespace declarations aside.
- `targets` (required): the fully qualified theorems or definitions to
  export. The package carries the proof-term closure of all of them.
- `options`: elaboration options to prepend to every vendored file as
  `set_option` lines, since a Lax lakefile carries only
  `autoImplicit = false`. Lake options do not propagate from a dependency,
  so a library compiled under options its own lakefile sets (Mathlib's
  `maxSynthPendingDepth 3` is the usual one, copied from Mathlib's own
  lakefile) may contain code that elaborates only under them; list such an
  option here when the package fails to build without it. The
  descriptive-complexity example needs none.
- `whole_modules`: vendor every module of the import closure in full
  instead of slicing. The fallback when slicing misses something.

The submission:

- `manifest` (required): the fields of the Lax manifest that are yours to
  write: `title` (required), `authors`, `bibEntries`, and the optional
  `supersedes`, `unlisted`, `anonymous`, `paper` and `initialOwners`. The
  tool fills in `specVersion`, `leanVersion` and `mathlibVersion` from the
  build, takes `id` from the manifest `lax init` wrote (an `id` here must
  agree with it), and preserves the `issue` that `lax submit` adds. The
  archive calls the submission `lax-N` and its packages `LaxN` (concepts)
  and `LaxNProofs` (proofs), a hyphen being impossible in a Lean name; those
  are also their module roots and the namespaces of their declarations.
  Each author is a mapping with `name` and optional `orcid` and `github`;
  names are free-form, which is how the archive's entries credit the
  generative models used, and the identifiers are for credit only,
  ownership being a separate list of GitHub accounts set with `lax owners`.
- `abstract` or `abstract_file` (one required): the submission's abstract,
  Markdown with `$…$` math.

  Where the library should appear. Lax's citation block names only the
  formalizers, and its page renders `bibEntries` as a references section, so
  the library belongs there as a software citation of the exported version
  (its DOI, as in the example), beside the papers; the abstract should link
  the repository and the documentation, since a reader of the page sees
  nothing else of the library; and each concept's docstring can link the
  documentation page of the declaration it restates, which is where the
  reader lands on the real code. The first two are the author's to write in
  the export file; the third is for the generator to emit from the
  concept-to-declaration mapping, once that exists.
- `copyright`: the one trailing "YYYY NAME" line the Lax archive allows after
  the Apache 2.0 text of the submission's `LICENSE`.
- `force_license`: write the submission even if the library's license does
  not permit redistribution under Apache 2.0 (see Licenses).
- `env`: target an archive environment other than the epoch, such as
  `v4.30.0`. A submission there can only cite and be cited within that
  environment.
- `out`: the submission folder, default the folder holding the file;
  `--out` overrides. To be submitted, it has to be committed to a public
  repository on one of the hosts the archive accepts (GitHub, GitLab.com,
  Codeberg, Bitbucket Cloud), which `lax submit` then points the archive at.

### Command-line options

Operational only:

- `--out DIR`: overrides the file's `out`, the submission folder.
- `--cache DIR`: where a clone is built when the local build cannot be used
  (see below). Default: `$LAX_EXPORT_CACHE` if set, else `lax-export/` under
  the system's temporary directory, which the `TMPDIR`, `TEMP` or `TMP`
  environment variables select (Python's `tempfile.gettempdir()`); on a
  machine where `/tmp` is small, set one of them or `--cache` to a disk with
  room for a Mathlib build (about 10 GB).
- `--no-environment-check`: skip the check against the Lax archive's
  environment list and Mathlib's tag, for offline use.
- `--jobs N`: how many files to elaborate in parallel when listing commands
  (default 4).
- `--work DIR`: where the plans go, the closure and per-file command
  listings, reused on a second run (default: `plans/lax-N/` under the
  cache).

### Which build is read

The rewrite relies on the `.ilean` and `.olean` files of a build of exactly
the sources exported. A local checkout is used as it stands when the ref is
its HEAD, its tree is clean and it is fully built: every module's olean and
ilean present and no older than its source, Mathlib built. In every other
case the ref is cloned and built under the cache, at
`<cache>/<library>@<ref>/`, with Mathlib from `lake exe cache get`; a second
export of the same library and ref finds that build in place, and a ref that
moved is fetched and rebuilt. The build's log is `.lake-export-build.log` in
the clone.

### Environment

Before anything is built or sliced, the library's Lean version must be the
archive's epoch, read from `https://laxarchive.org/environments.json`, and
its Mathlib pin must be the commit of Mathlib's tag of that version, which
is what the environment records. `--env` targets another listed environment
instead; `--no-environment-check` skips the check.

### Licenses

The Lax accepts exactly one license for a submission, Apache 2.0, with
at most one trailing copyright line, so the tool always writes that text as
the submission's `LICENSE`. The vendored files keep the library's own
copyright headers. When the library is itself under Apache 2.0 nothing more
is needed. When it is under a permissive license that permits sublicensing
(MIT, BSD, ISC, 0BSD, Unlicense, CC0), the library's license text goes into
a `NOTICE` file at the submission's root, with a sentence saying where the
code comes from; the Lax archive allows extra root-level documentation. A
library under any other license, copyleft ones above all, is refused,
since relabeling it would not be lawful; `--force-license` overrides for
the cases the detection gets wrong.

### Checking the result

The way the Lax archive will:

```
cd ../lax-123456/proofs && lake build
LEAN_PATH=… lean --run Check.lean Lax123456Proofs Lax123456Proofs.MyLib.main_theorem
```

`Check.lean` lists every constant of the package outside its prefix and the
axioms of the targets, and exits non-zero when a target rests on more than
`propext`, `Classical.choice` and `Quot.sound`.

## How it works

1. **Closure.** `Slice.lean closure` walks the kernel environment from the
   targets' proof terms and reports every constant reached with its module
   and source range. Generated constants (recursors, `match` auxiliaries,
   equation lemmas) have no range and are attributed to the declaration that
   generated them.
2. **Commands.** For each module of the import closure, `Slice.lean commands`
   elaborates the file against its own imports and lists its commands with
   kinds and byte ranges, one process per file. A command a library-defined
   elaborator produced (`my_command …`) is captured from the info trees and
   pretty-printed in its place.
3. **Slice.** A command is kept when it is scaffolding (namespace, section,
   variable, open, universe, options, notations, module docstrings), when it
   declares a selected constant, or when it is an instance or an attributed
   lemma that tactics use without leaving a trace in proof terms (`@[simp]`
   lemmas proved by `rfl`, coercion instances) and it still elaborates.
   Modules declaring syntax, macros or elaborators are vendored in full and
   their declarations fed back as targets, to a fixed point. A scaffolding
   command mentioning an unselected library constant is dropped.
4. **Rename.** The library's namespace moves under `LaxNProofs` by a
   whole-name rewrite. Constants the library declares in foreign namespaces
   (Mathlib's, say `FirstOrder.Language.sat`) are renamed usage by usage from
   the `.ilean` records and rooted under `LaxNProofs.Foreign.…`, with an
   `export` alias at the old name so that generalized field notation still
   finds them; unnamed instances get the name the library's build gave them;
   `deriving` clauses are re-derived in a jump namespace that replays the
   scaffolding it had to close.
5. **Imports.** An import of a dropped module is replaced by the vendored
   modules and the Mathlib modules below it.
6. **Layout.** Lakefiles, toolchain files, root modules, manifest, abstract
   and license, per the Lax archive's spec.

Whatever the slicer misses fails the build of the package, which is the test.

## Tests

`tests/unit` covers the pure Python parts (export-file validation, the
renaming, the manifest and license writers) and runs with `pytest tests/unit`.
`tests/test_export.py` is the integration test: it exports `tests/fixture`,
a small Mathlib-based library with a module for every rule of the slicer
(a coercion, a `@[simp]` lemma proved by `rfl`, a macro, foreign-namespace
declarations with a derived instance, a generated constant, a private name,
a `_root_` declaration, an unreached module), builds what comes out, and
runs `Check.lean` on it. It needs the fixture built (`lake build` in
`tests/fixture`, with Mathlib from `lake exe cache get`) and `lean`, `lake`
on `PATH`; it skips otherwise. The workflow in `.github/workflows/ci.yml`
runs both, building the fixture with `leanprover/lean-action`.

`Check.lean` is the test's stand-in for the validation `lax build` performs
on a real submission; the archive's tool is authoritative, and the checker
exists so that a plain `lake build` and a CI job without the Lax tool can
still catch a constant outside the prefix or an unexpected axiom.

## Known limits

- Two kinds of constant land outside the package prefix and cannot be moved:
  syntax categories (`Lean.Parser.Category.…`) and the congruence lemmas
  `simp` generates for Mathlib functions (`….congr_simp`). Any submission
  using those features produces them.
- A `variable` of a section is lost across a jump namespace (expansion of a
  library-defined command, or a `deriving` clause on a foreign inductive)
  unless the section's scaffolding is replayed, which the tool does for
  `open`, `variable`, `universe`, `set_option`, `omit`, `include` and local
  notations only.
- The rewrite assumes the library keeps its declarations under one top-level
  namespace, foreign-namespace declarations aside.

Not yet done: the registry that lets a later submission require an earlier
one instead of vendoring the same declarations again; the substitution of
backward bridges so the Lax archive's proof network shows cross-submission
dependencies; links from a library's README and docstrings to the Lax archive
pages; a CI job regenerating and building every submission at each tag.

## License

Apache 2.0, the license of Lean, Mathlib and Lax's own tooling.
Copyright 2026 Pierre Senellart.
