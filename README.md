# Fixing the Fixpoint

This repository contains the Lean 4 formalization and paper sources for
*Fixing the Fixpoint: A Formal Theory of Convergence Detection for Incremental
Recursive Computation*.

## Contents

- [`paper.pdf`](paper.pdf): manuscript.
- [`DBSP/`](DBSP/) and [`DBSP.lean`](DBSP.lean): Lean 4 formalization.
- [`paper/`](paper/): LaTeX sources and figures for the paper, with
  [`main.tex`](paper/main.tex) as the entry point.
- [`paper-to-lean.md`](paper-to-lean.md): correspondence between the paper's
  definitions and results and their Lean declarations, with source links.
- [`lakefile.toml`](lakefile.toml) and [`lean-toolchain`](lean-toolchain): build
  configuration and pinned Lean version.

## Building the Lean formalization

Install Lean 4 (for example, using [elan](https://github.com/leanprover/elan)),
then run the following commands from the repository root:

```sh
lake exe cache get
lake build
```

Getting the Mathlib cache initially takes 1–2 minutes, and a clean build takes
about 2–3 minutes on a fast laptop.

## License

The original code and its accompanying documentation are available under the
[MIT License](LICENSE). Inherited code and bundled third-party files retain
their existing licenses and copyright notices, including the BSD-2-Clause
notices in `DBSP/StreamTheory/`. The manuscript, its LaTeX sources, and figures
are not covered by the code's MIT license.
