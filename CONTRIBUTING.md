# Contributing

Contributions should state precise mathematical assumptions, use existing mathlib APIs where practical, and document what each theorem does not establish.

Before proposing a change, run:

```sh
lake exe cache get
bash scripts/verify.sh
```

The gate includes source-policy scanning, Lean compilation, module coverage, independent kernel replay, named dependency checks, and project-wide axiom auditing. Do not introduce `sorry`, custom axioms, kernel bypasses, or widen the axiom allowlist without an explicit, separately reviewed policy change.

The hosted Lean checkpoint is weekly or manually dispatched rather than automatically run on every pull request. Describe local verification in PRs and distinguish unverified proposals from checked results.

This project uses AI assistance for drafting, navigation and proof search. All contributions must be independently reviewed for mathematical correctness, source attribution, scope, and novelty claims.
