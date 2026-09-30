# Revision Submission Attachment

This attachment accompanies the revised submission of _Fixing the Fixpoint: A
Formal Theory of Convergence Detection for Incremental Recursive Computation_. 

## Contents

NOTICE: If you are viewing this on the Anonymous Github website, there will be issues with figure display in `paper.pdf`, `revision-diff.pdf` and `revision-diff-full.pdf`. Please consider downloading and reading them elsewhere.

- [`paper.pdf`](./paper.pdf): revised manuscript.
- [`revision-diff.pdf`](./revision-diff.pdf): revised manuscript with added material highlighted in dark blue.
- [`revision-diff-full.pdf`](./revision-diff-full.pdf): full diff between the original and revised manuscripts,
  showing both additions and deletions.
- [`summary-of-changes.pdf`](./summary-of-changes.pdf): summary of the revision and how it addresses the reviews.
- [`response-to-reviewer-C.pdf`](./response-to-reviewer-C.pdf): additional response to Reviewer C.
- [`paper-to-lean.md`](./paper-to-lean.md): correspondence between paper definitions and results and
  their Lean declarations, with links to the paper LaTex source and the Lean code.
- [`paper/`](./paper/): LaTeX source of the revised manuscript.
- [`DBSP/`](./DBSP/) and [`DBSP.lean`](./DBSP.lean): Lean 4 formalization. The project configuration is in
  `lakefile.toml`, with the Lean version pinned by `lean-toolchain`.

## Building the Lean formalization

Install Lean 4 (for example, using [elan](https://github.com/leanprover/elan)),
then run the following commands from the attachment directory:

```sh
lake exe cache get
lake build
```

Getting the Mathlib cache initially takes 1–2 minutes, and a clean build takes
about 2–3 minutes on a fast laptop.

## Use of AI
AI is used to assist with Lean development and artifact preparation. The authors carefully reviewed all definitions and theorem statements and take full responsibility for the paper, formalization, and accompanying artifacts.