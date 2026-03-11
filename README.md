# Fixing the Fixpoint Artifact

This is the Lean formalization for the paper "Fixing the Fixpoint".

## Proof checking

Install Lean4 (for example, using elan), then run:

```sh
lake exe cache get
lake build
```

Getting the cache initially takes 1-2min, and a clean build takes about 2-3min on a fast laptop.
