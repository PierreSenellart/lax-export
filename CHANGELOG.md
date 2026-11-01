# Changelog

All notable changes are documented here. The format is loosely based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this project
adheres to [Semantic Versioning](https://semver.org/).

## [0.1.0]

First release.

### Added
- `lax_export.py EXPORT.yaml` writes, into the submission folder `lax init`
  made, a Lax proofs package carrying the proof-term closure of the
  exported theorems, sliced from the library command by command and renamed
  under the submission's namespace; `whole_modules` vendors whole modules
  instead. Hand-written files (`abstract.md`, concepts, bridges) are left
  alone, and a second run replaces only the vendored tree.
- The library is read from a local checkout when it is a build of exactly
  the exported sources, and is otherwise cloned and built under a cache;
  its Lean and Mathlib versions are checked against the archive's
  environments.
- `restated` maps library declarations to the concept declarations that
  restate them, and `--skeleton` drafts those concept modules from the
  library's own definitions.
- `requires` builds on registered submissions, pinned as the archive
  demands, and `restated_from` reuses their `restated` maps.
- The submission's `LICENSE` is Apache 2.0; a library under a permissive
  license that permits sublicensing has its license text carried in
  `NOTICE`, and any other license is refused unless `force_license` is set.
- `Check.lean` lists what a package's targets rest on, as the archive's
  inspector does.

[0.1.0]: https://github.com/PierreSenellart/lax-export/releases/tag/v0.1.0
