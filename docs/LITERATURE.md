# Literature context for finite random two-orders

`CausalSet.RandomTwoOrder` proves finite combinatorial identities for the order obtained
from a uniformly enumerated permutation. This note records where closely related models
and observables occur in the literature. It does not claim novelty or add hypotheses to
the Lean theorems.

## Uniform permutation model

Eppstein and Simons [EppsteinSimons2013] generate a two-dimensional partial order from a
uniform permutation by intersecting the order of positions with the order of permutation
values. This is the construction represented by `CausalSet.TwoOrder`. They compute the
expected number of Hasse-diagram edges as

```text
sum (H_k - 1), k = 1,...,N = (N + 1) H_N - 2N.
```

For a finite partial order, Hasse-diagram edges are links. The library theorem
`sum_links_twoOrder` is the denominator-cleared finite sum corresponding to this
expectation. The Lean development proves it from the more general interval-window count;
it does not depend on the published proof.

## Interval abundances and the two-dimensional combination

Glaser and Surya [GlaserSurya2013] define `N_m` as the number of order intervals with
exactly `m` elements between their endpoints, derive ensemble expectations for
sprinklings into Minkowski Alexandrov intervals, and record the two-dimensional
combination `N - 2N_0 + 4N_1 - 2N_2`. Benincasa, Dowker, and Schmitzer
[BenincasaDowkerSchmitzer2011] study the associated random discrete action in finite-volume
two-dimensional Lorentzian regions and its mean for several geometries.

The library's `intervalAbundance` uses the same open-interval cardinality convention, and
`bdCombination2` uses that coefficient pattern. The theorem
`sum_bdCombination2_twoOrder` is only an exact sum over finite permutations. Lean does not
identify `bdCombination2` with a normalized physical action or prove any continuum or
boundary-term statement.

## Sampling assumption and non-claims

The **fixed-cardinality diamond correspondence** used to motivate the finite model is not
formalized. It assumes a homogeneous Poisson sprinkling into a two-dimensional Minkowski
Alexandrov diamond, conditions on exactly `N` points, passes to affine null coordinates,
uses the almost-sure absence of coordinate ties, and sorts one coordinate. Under these
assumptions the ranks of the other coordinate form a uniform permutation and causal
comparability becomes the intersection of the two coordinate orders.

No theorem in the library defines that Poisson process, proves this conditional-distribution
statement, constructs a faithful spacetime embedding, or infers physical volume,
dimension, locality, curvature, continuum convergence, or dynamics. The finite identities
also make no novelty claim. Any such bridge requires separate measure-theoretic and
geometric formalization.

Bibliographic metadata and persistent identifiers are in [`../REFERENCES.bib`](../REFERENCES.bib).
