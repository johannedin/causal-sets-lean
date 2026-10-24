# Causal Sets Lean

A Lean 4 / mathlib formalization of foundational causal-set order theory. The library develops elementary results for locally finite preorders and partial orders using existing mathlib abstractions.

## Scope

The current API includes finite Alexandrov intervals, interval cardinalities, links as cover relations, reconstruction of strict and reflexive precedence from link paths, transport and order-duality invariance, finite interval-abundance counting identities, and exact finite sums over permutation-generated two-dimensional orders. It is mathematical infrastructure: these elementary statements are not claimed as novel research.

The three-element partial order `CausalSet.Vee` and its order dual are not order-isomorphic,
yet their entire interval-abundance functions agree. More generally, every duality-invariant
observable of finite partial orders covered by the API agrees on this pair; no
isomorphism-invariance assumption is needed for that conclusion. Invariance therefore does
**not** ensure completeness. No minimality claim is made for this example. Order duality is
formal reversal of `≤`, not a physical time orientation.

The four-element orders `CausalSet.LamPt` and `CausalSet.TwoChains` strengthen this
incompleteness example: their interval-abundance functions agree although they are neither
order-isomorphic nor dual-isomorphic. An isolated element supplies the structural obstruction.

The five-element orders `CausalSet.ButterflyPt` and `CausalSet.NPlus` show that interval
abundance together with antichain counts by size still does not determine a finite order up
to isomorphism or duality.

For a permutation `σ : Equiv.Perm (Fin N)`, `CausalSet.TwoOrder σ` intersects the usual
order on positions with the order of their images under `σ`. The library proves exact sums
over all `N!` permutations for interval abundances, links, strict relations, and the
two-dimensional Benincasa--Dowker interval combination. These are finite combinatorial
identities; no probability space is defined in Lean.

The **fixed-cardinality diamond correspondence** is an unformalized sampling assumption:
condition a homogeneous Poisson sprinkling into a two-dimensional Minkowski Alexandrov
diamond on exactly `N` points, use affine null coordinates, assume the almost-sure absence
of coordinate ties, and sort by one coordinate. The ranks of the other coordinate then
give a uniform permutation, whose induced causal order is represented by `TwoOrder`.
The library does not prove this measure-theoretic or geometric bridge. In particular, the
finite formulas do not by themselves establish a sprinkling law, faithful embedding,
dimension estimator, continuum limit, curvature result, or physical action. See
[`docs/LITERATURE.md`](docs/LITERATURE.md) for the precise literature relationship.

The library also provides a general correspondence-distance API for finite labelled
families of real-valued pseudometric kernels. A single correspondence controls every label.
On nonempty compact metric spaces whose ambient metrics are the pointwise maxima of the
labelled kernels, zero joint distance is equivalent to a bijection preserving every
kernel. This is abstract metric infrastructure: it does not identify physical spacetimes,
establish geometric reconstruction, or supply statistical convergence rates.

The formalization **does not** establish faithful spacetime embeddings, dimension, sprinkling laws, physical volume, continuum convergence, Lorentzian metric reconstruction, or field dynamics. Additional geometric and probabilistic assumptions would be required.

## Reproducible verification

The project pins Lean and mathlib to v4.35.0 and commits its dependency manifest. From a clean checkout with Lean/Elan and Git installed:

```sh
lake exe cache get
bash scripts/verify.sh
```

The verification script runs the source trust policy, warnings-as-errors build, generated module coverage, independent kernel replay, named dependency checks, and project-wide axiom audit. The permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. See `CONTRIBUTING.md` for requirements.

The GitHub workflow is a change-aware weekly checkpoint, with manual dispatch. Ordinary changes must be verified locally; the hosted checkpoint is not automatically required for each pull request.

## Public API

- `CausalSet.alexandrovInterval x y`: finite open interval `Finset.Ioo x y`.
- `CausalSet.intervalCard x y`: cardinality of that interval.
- `CausalSet.IsLink x y`: strict precedence with no intervening element.
- `CausalSet.isLink_iff_covBy`: identification with mathlib's cover relation.
- `CausalSet.lt_iff_transGen_isLink`: strict order reconstructed from finite link paths.
- `CausalSet.le_iff_reflTransGen_isLink`: reflexive precedence reconstructed for partial orders.
- `CausalSet.alexandrovInterval_map` and `intervalCard_map`: interval transport and cardinality preservation under order isomorphisms.
- `CausalSet.isLink_map`: link invariance under order isomorphisms.
- `CausalSet.intervalCard_toDual` and `isLink_toDual`: interval-cardinality and link invariance under order duality.
- `CausalSet.intervalAbundance α k`: number of ordered strict pairs with exactly `k` elements in their open interval.
- `CausalSet.bdCombination2 α`: the interval combination `N - 2N₀ + 4N₁ - 2N₂`; its identification with a physical action is not formalized.
- `CausalSet.intervalAbundance_zero`: the zeroth abundance counts links.
- `CausalSet.intervalCard_lt_card` and `intervalAbundance_eq_zero_of_card_le`: finite support below the carrier cardinality.
- `CausalSet.sum_intervalAbundance`: summing the abundances over that support counts all strict pairs.
- `CausalSet.intervalAbundance_congr` and `intervalAbundance_toDual`: invariance under order isomorphism and order duality.
- `CausalSet.isEmpty_orderIso_orderDual_of_isTop`: a preorder with a greatest element but no least element cannot be order-isomorphic to its dual.
- `CausalSet.Vee`: a finite partial order with two incomparable minimal elements below a greatest element.
- `CausalSet.Vee.isTop_top` and `not_isBot`: greatest-element and no-least-element witnesses.
- `CausalSet.Vee.isEmpty_orderIso_orderDual`: structural non-isomorphism with the order dual.
- `CausalSet.Vee.intervalAbundance_not_complete`: equality of interval-abundance functions on that non-isomorphic pair.
- `CausalSet.Vee.dual_invariant_not_complete`: the corresponding obstruction for duality-invariant observables.
- `CausalSet.IsIsolated`, `IsIsolated.map`, and `isIsolated_toDual_iff`: isolated elements and their invariance under order isomorphism and order duality.
- `CausalSet.isEmpty_orderIso_of_isIsolated`: an isolated-element obstruction to ordinary and dual order isomorphisms.
- `CausalSet.LamPt`, `TwoChains`, and `intervalAbundance_not_complete_nonDual`: a four-element equal-abundance pair that is neither isomorphic nor dual-isomorphic.
- `CausalSet.antichainCount α k`: number of `k`-element antichains in a finite order.
- `CausalSet.antichainCount_congr` and `antichainCount_toDual`: invariance under order isomorphism and order duality.
- `CausalSet.antichainCount_eq_zero_of_card_lt`: finite support of antichain counts.
- `CausalSet.NPlus`, `ButterflyPt`, and `intervalAbundance_antichainCount_not_complete_nonDual`: a five-element pair with equal interval abundance and antichain counts that is neither isomorphic nor dual-isomorphic.
- `CausalSet.TwoOrder σ`: the finite order obtained by intersecting position order with the order induced by a permutation.
- `CausalSet.windowCount` and `CausalSet.RandomTwoOrder.windowCount_spec`: exact counting of permutations with a prescribed two-order interval window.
- `CausalSet.RandomTwoOrder.sum_intervalAbundance_twoOrder` and `sum_intervalAbundance_twoOrder_closed`: exact finite sums of interval abundances, including a harmonic-number closed form.
- `CausalSet.RandomTwoOrder.sum_links_twoOrder`: the exact finite sum of link counts over all permutations.
- `CausalSet.RandomTwoOrder.sum_relations_twoOrder`: the exact ordering-fraction sum over all permutations.
- `CausalSet.RandomTwoOrder.sum_bdCombination2_twoOrder`: the interval-combination sum for every nonempty carrier.
- `LabelledCorrespondence.KernelFamily`: a finite labelled family of real-valued pseudometric kernels.
- `LabelledCorrespondence.Correspondence`: a relation with surjective coordinate projections.
- `LabelledCorrespondence.componentDistortion`, `jointDistortion`, and `jointDistance`: componentwise and common-correspondence distortions and their joint distance.
- `LabelledCorrespondence.jointDistance_symm` and `jointDistance_triangle`: symmetry and the triangle inequality.
- `LabelledCorrespondence.Preserves`, `jointDistance_congr_left`, and `jointDistance_congr_right`: preservation and invariance under label-preserving equivalences.
- `LabelledCorrespondence.jointDistance_eq_zero_iff_exists_preserving_equiv`: the compact zero-distance characterization under explicit finite-label and maximum-metric hypotheses.

Abundance counting uses `Fintype` and `DecidableLT` in addition to `Preorder` and
`LocallyFiniteOrder`; it requires neither antisymmetry nor `DecidableEq`.
Antichain counting uses only `LE` together with `Fintype`, `DecidableEq`, and `DecidableLE`.

For a worked example, see the following use of the link equivalence in a locally finite partial order:

```lean
import CausalSet

example {α : Type*} [PartialOrder α] [LocallyFiniteOrder α]
    {x y : α} (h : CausalSet.IsLink x y) : x < y :=
  CausalSet.IsLink.lt h
```

## Provenance and limitations

The project is AI-assisted in drafting and proof search. Accepted Lean results are expected to pass the documented verification checks; machine checking does not establish physical interpretation or scientific novelty. Bibliographic background is recorded in `REFERENCES.bib`, with claim-level context in [`docs/LITERATURE.md`](docs/LITERATURE.md).

## License

Apache-2.0; see `LICENSE` and `NOTICE`.
