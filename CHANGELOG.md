# Changelog

All notable changes to this project are documented here.

## [0.2.0] — 2026-10-24

The release date will be assigned when the maintainer publishes the GitHub Release. This
candidate keeps Lean 4.35.0 and the existing mathlib pin.

### Added

- A reusable isolated-element obstruction and a four-element pair with equal interval
  abundance that is neither order-isomorphic nor dual-isomorphic.
- Antichain counting, its isomorphism and duality invariance, and a five-element pair showing
  that interval abundance together with antichain counts is still incomplete up to isomorphism
  and duality.
- Exact finite counting identities for permutation-generated two-orders: interval windows,
  interval abundances, links, strict relations, and the two-dimensional interval combination.
- A general joint correspondence distance for finite labelled families of real-valued
  pseudometric kernels, including symmetry, the triangle inequality, invariance under
  label-preserving equivalences, and a compact zero-distance characterization when the
  pointwise maximum kernel induces each ambient metric.
- Umbrella imports, executable examples, and named restricted-axiom guards for the new public
  declarations.

### Scope and limitations

- The finite non-identifiability results are explicit examples and counterexamples; they do not
  classify all finite orders or establish minimality unless a theorem explicitly says so.
- The two-order results are deterministic sums over finite permutations. The library defines no
  probability space and does not formalize the geometric or measure-theoretic bridge from a
  spacetime sprinkling to a uniform permutation.
- The labelled-correspondence module is general-purpose metric infrastructure. Its compact
  zero-distance theorem does not by itself prove physical isometry, geometric reconstruction,
  identifiability from unlabelled samples, or statistical convergence.
- The related preprint cited below contains results that are not all Lean-formalized here.

### Related publication

Johan Nedin, *Finite-sample consistency of joint causal profiles in bounded-density
two-dimensional diamonds*, Zenodo (2026), version 1.0,
[doi:10.5281/zenodo.23624630](https://doi.org/10.5281/zenodo.23624630).

## [0.1.0] — 2026-10-21

- Initial curated release of foundational finite causal-set order theory: Alexandrov intervals,
  interval cardinalities, links and link-path reconstruction, transport under order
  isomorphisms, order-duality invariance, interval abundance, and the three-element dual
  non-identifiability example.

[0.2.0]: https://github.com/johannedin/causal-sets-lean/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/johannedin/causal-sets-lean/releases/tag/v0.1.0
