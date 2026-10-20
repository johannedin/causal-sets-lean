# Causal Sets Lean

A Lean 4 / mathlib formalization of foundational causal-set order theory. The library develops elementary results for locally finite preorders and partial orders using existing mathlib abstractions.

## Scope

The current API includes finite Alexandrov intervals, interval cardinalities, links as cover relations, reconstruction of strict and reflexive precedence from link paths, transport and order-duality invariance, and finite interval-abundance counting identities. It is mathematical infrastructure: these elementary statements are not claimed as novel research.

The three-element partial order `CausalSet.Vee` and its order dual are not order-isomorphic,
yet their entire interval-abundance functions agree. More generally, every duality-invariant
observable of finite partial orders covered by the API agrees on this pair; no
isomorphism-invariance assumption is needed for that conclusion. Invariance therefore does
**not** ensure completeness. No minimality claim is made for this example. Order duality is
formal reversal of `≤`, not a physical time orientation.

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

Abundance counting uses `Fintype` and `DecidableLT` in addition to `Preorder` and
`LocallyFiniteOrder`; it requires neither antisymmetry nor `DecidableEq`.

For a worked example, see the following use of the link equivalence in a locally finite partial order:

```lean
import CausalSet

example {α : Type*} [PartialOrder α] [LocallyFiniteOrder α]
    {x y : α} (h : CausalSet.IsLink x y) : x < y :=
  CausalSet.IsLink.lt h
```

## Provenance and limitations

The project is AI-assisted in drafting and proof search. Accepted Lean results are expected to pass the documented verification checks; machine checking does not establish physical interpretation or scientific novelty. Bibliographic background is recorded in `REFERENCES.bib`.

## License

Apache-2.0; see `LICENSE` and `NOTICE`.
