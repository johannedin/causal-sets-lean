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
- [x] Exact finite permutation sums for interval abundances, links, strict relations, and the two-dimensional Benincasa--Dowker interval combination in random two-orders.
- [x] Joint correspondence distance for finite labelled pseudometric families, including symmetry, the triangle inequality, equivalence invariance, and a compact zero-distance characterization under explicit maximum-metric hypotheses.
- [x] Finite Pauli–Jordan relation-sign matrices: the injective two-coordinate sign identity, real antisymmetry, Hermitian imaginary multiple, cardinality normalization, and relabelling invariance.
- [x] Pinned Lean/mathlib environment, local proof and axiom audits, and a change-aware weekly/manual verification workflow.

## Possible future extensions

The following are proposals, not accepted theorems or release requirements.

### Limits of reconstruction

- Investigate further non-dual finite orders that share selected counting invariants beyond interval abundance.
- Investigate stronger invariant families beyond interval abundance and antichain counts, documenting precisely what information they retain or fail to distinguish.

### Statistical reconstruction

- Formalize probabilistic or geometric bridges only with their sampling, measurability, and embedding assumptions explicit.
- Investigate variance, asymptotics, or higher-dimensional models separately from the accepted finite two-order identities.

### Library quality

- Maintain minimal assumptions, stable mathlib-compatible APIs, executable examples, and transparent trust auditing.
- Improve documentation and attribution as the library grows.

No dimension, spacetime embedding, metric reconstruction, continuum limit, or physical field dynamics follows from the current formalization.

## Incremental curation model for maintainers

Promote small coherent mathematical milestones: a complete reusable module or theorem
family, not a collection of unrelated proofs. Proof trust comes before quantity:
each theorem must state its assumptions, compile locally, pass kernel replay and the
restricted-axiom/source audits, and receive independent exact-commit review before merge.

Keep status distinctions explicit: paper-proved, independently reviewed, Lean-formalized,
publicly promoted, numerically supported, and conjectural are different claims. Public
formalization does not establish novelty or physical validity beyond the theorem statement.
At suitable research checkpoints, assess candidates individually; promotion is never automatic.
Preserve authorship, licenses and upstream provenance for adapted third-party mathematics.
Use local verification and owner-controlled releases rather than expensive hosted CI.

Possible later curation candidates, requiring separate scope and approval:

1. Exact finite Pauli–Jordan Fourier/Cayley reduction.
2. General Hermitian spectral infrastructure, with a separate provenance and maintenance
   assessment; reusable results may ultimately belong in mathlib rather than here.
3. Causal-profile algebra relating labelled kernels and indicator functions; this is a
   future formalization milestone, not an already implemented module.
4. Later finite-band spectral comparisons, with explicit band, positivity and indexing hypotheses.

These candidates are not release commitments and do not authorize new implementation.
