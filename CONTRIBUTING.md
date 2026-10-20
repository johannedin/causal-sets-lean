# Contributing

Contributions should state precise mathematical assumptions, use existing mathlib APIs where practical, and document what each theorem does not establish.

Before proposing a change, run:

```sh
lake exe cache get
bash scripts/verify.sh
```

The gate includes source-policy scanning, Lean compilation, module coverage, independent kernel replay, named dependency checks, and project-wide axiom auditing. Do not introduce `sorry`, custom axioms, kernel bypasses, or widen the axiom allowlist without an explicit, separately reviewed policy change.

The hosted Lean checkpoint is weekly or manually dispatched rather than automatically run on every pull request. Describe local verification in PRs and distinguish unverified proposals from checked results.

This project uses AI assistance for drafting, navigation and proof search. All contributions must be reviewed for mathematical correctness, source attribution, and scope. Novelty is welcome but neither expected nor required; novelty claims, when made, require supporting review.

## Issue curation and research scope

This repository contains **curated, self-contained proposals** for general causal-set mathematics. New exploratory research is reviewed privately before publication. Public issues must not contain private research discussions, unpublished hypotheses, private repository links, or personal correspondence. Do not copy issue threads or comments from a private workspace.

A research issue should state the precise mathematical goal and assumptions, existing literature and attribution, counterexamples or limitations, expected Lean deliverables, and explicit non-claims. Distinguish established infrastructure from possible novel results; acceptance into this repository is not a novelty endorsement.

Maintainers review and approve the proposed public text before creating the issue. Publication of issues and PRs is a deliberate manual action, not an automatic transfer from a private repository. Legitimate citations to published research should be retained.

## Private-first development and curated promotion

Substantive mathematical changes are researched, implemented, locally verified, and reviewed in a private development workspace **before** being proposed here. The public repository is the canonical accepted library, not a mirror of experimental development history.

For each approved contribution:

1. Prepare a minimal, self-contained public issue and a reviewed code/documentation patch. Do not copy private issue discussions, review comments, experimental commits, branch history, or private links.
2. Create a **fresh branch from the current curated `main`** and apply only the approved patch. Private repository branches must not be merged into this repository.
3. Re-run `bash scripts/verify.sh` against the curated dependency baseline and report the actual result. Recheck the entire PR diff, title, description, and metadata for accidental disclosure.
4. Obtain final mathematical and publication review; squash-merge the focused PR when approved. Preserve author credit, relevant published citations, and the existing AI-assistance disclosure.

The private development record retains experiments and failed approaches; this repository's history records accepted releases. Passing tests does not itself authorize publication. If the destination baseline has changed, reconcile and re-review the patch rather than assuming the earlier verification remains valid.

**Value standard:** Correct, maintainable formalization of established causal-set mathematics is a complete contribution. New theorems are optional.
