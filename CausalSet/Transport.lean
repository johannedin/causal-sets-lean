/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

public import CausalSet.Link

/-!
# Transport and order duality

Order isomorphisms preserve finite open Alexandrov intervals, their cardinalities,
and links. Order duality preserves the cardinalities and links after reversing
both endpoints. These elementary results require only locally finite preorders:
antisymmetry, finiteness of the entire type, and comparability of the endpoints
are not assumed.

The proofs reuse mathlib's finite-set cardinality, cover-relation transport, and
order-dual interval APIs. These are invariance results, not completeness results:
they do not say that interval or link observables determine an order up to
isomorphism, nor do they reconstruct continuum geometry or specify physical dynamics.
-/

@[expose] public section

namespace CausalSet

variable {α β : Type*}
variable [Preorder α] [LocallyFiniteOrder α]
variable [Preorder β] [LocallyFiniteOrder β]

/-- Order isomorphisms carry finite open intervals to finite open intervals. -/
theorem alexandrovInterval_map (e : α ≃o β) (x y : α) :
    (alexandrovInterval x y).map e.toEquiv.toEmbedding =
      alexandrovInterval (e x) (e y) := by
  ext z
  simp only [Finset.mem_map, mem_alexandrovInterval]
  constructor
  · rintro ⟨w, ⟨hxw, hwy⟩, rfl⟩
    exact ⟨e.strictMono hxw, e.strictMono hwy⟩
  · intro hz
    refine ⟨e.symm z, ?_, by simp⟩
    constructor
    · simpa using (e.symm.strictMono hz.1)
    · simpa using (e.symm.strictMono hz.2)

/-- An order isomorphism preserves interval cardinality. -/
theorem intervalCard_map (e : α ≃o β) (x y : α) :
    intervalCard (e x) (e y) = intervalCard x y := by
  rw [intervalCard, intervalCard, ← alexandrovInterval_map]
  exact Finset.card_map _

/-- An order isomorphism preserves links. -/
theorem isLink_map (e : α ≃o β) {x y : α} :
    IsLink (e x) (e y) ↔ IsLink x y := by
  rw [isLink_iff_covBy, isLink_iff_covBy]
  exact apply_covBy_apply_iff e

/-- Reversing the order and endpoints preserves interval cardinality. -/
theorem intervalCard_toDual (x y : α) :
    intervalCard (OrderDual.toDual y) (OrderDual.toDual x) =
      intervalCard x y := by
  simp only [intervalCard, alexandrovInterval]
  rw [Finset.Ioo_toDual, Finset.card_map]

/-- Reversing the order and endpoints preserves links. -/
theorem isLink_toDual {x y : α} :
    IsLink (OrderDual.toDual y) (OrderDual.toDual x) ↔ IsLink x y := by
  rw [isLink_iff_covBy, isLink_iff_covBy]
  exact toDual_covBy_toDual_iff

end CausalSet
