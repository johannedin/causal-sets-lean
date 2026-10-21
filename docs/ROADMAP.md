# General causal-set research roadmap

This repository provides a reusable Lean 4 formalization of elementary causal-set order theory. The library's established mathematical results are useful as formalization infrastructure; no claim of mathematical novelty is made.

## Implemented foundations

- [x] Locally finite preorders, Alexandrov intervals, interval cardinalities, and links.
- [x] Link-closure reconstruction of strict precedence, and reflexive precedence under the stated partial-order assumptions.
- [x] Transport of intervals and links under order isomorphisms.
- [x] Interval-cardinality and link invariance under order duality.
- [x] Finite interval abundance, its link and strict-pair counting identities, and invariance under order isomorphisms and duality.
- [x] A three-element pair of non-isomorphic order-dual finite partial orders with equal interval abundance, and a general obstruction for duality-invariant observables.
- [x] A four-element pair of finite partial orders with equal interval abundance that are neither order-isomorphic nor dual-isomorphic, via a reusable isolated-element obstruction.
- [x] A five-element pair of finite partial orders with equal interval abundance and equal antichain counts by size that are neither order-isomorphic nor dual-isomorphic.
- [x] Pinned Lean/mathlib environment, local proof and axiom audits, and a change-aware weekly/manual verification workflow.

## Possible future extensions

The following are proposals, not accepted theorems or release requirements.

### Limits of reconstruction

- Investigate further non-dual finite orders that share selected counting invariants beyond interval abundance.
- Investigate stronger invariant families beyond interval abundance and antichain counts, documenting precisely what information they retain or fail to distinguish.

### Statistical reconstruction

- Investigate finite random two-dimensional orders and exact permutation-statistic identities.
- Introduce probabilistic and geometric assumptions explicitly rather than interpreting finite counts as spacetime volume without justification.

### Library quality

- Maintain minimal assumptions, stable mathlib-compatible APIs, executable examples, and transparent trust auditing.
- Improve documentation and attribution as the library grows.

No dimension, spacetime embedding, metric reconstruction, continuum limit, or physical field dynamics follows from the current formalization.
