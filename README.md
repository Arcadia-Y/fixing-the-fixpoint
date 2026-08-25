# Revision Submission Attachment

This attachment accompanies the revised submission of *Fixing the Fixpoint: A
Formal Theory of Convergence Detection for Incremental Recursive Computation*.

## Contents

- `paper.pdf`: revised manuscript.
- `revision-diff.pdf`: differences between the original and revised manuscripts.
- `summary-of-changes.pdf`: summary of the revision and how it addresses the reviews.
- `response-to-reviewer-C.pdf`: additional response to Reviewer C.
- `paper-to-lean.md`: correspondence between paper definitions and results and
  their Lean declarations, with links to the paper LaTex source and the Lean code.
- `paper/`: LaTeX source of the revised manuscript.
- `DBSP/` and `DBSP.lean`: Lean 4 formalization. The project configuration is in
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
