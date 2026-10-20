/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

public import CausalSet.Abundance

/-!
# Finite-order non-identifiability

A preorder with a greatest element but no least element cannot be order-isomorphic
to its dual. The three-element partial order `Vee`, with two incomparable minimal
elements below a greatest element, supplies a finite example. Its dual is `Veeᵒᵈ`.
Interval abundance, and any observable of finite partial orders invariant under
order duality, agree on this non-isomorphic pair. Isomorphism invariance is not
needed for that conclusion.

These are established order-theoretic results. No minimality of the example or
novelty is asserted. Order duality is formal reversal of `≤`, not a physical time
orientation. Incompleteness of these observables entails no continuum geometric,
metric, or dynamical conclusion without further hypotheses.
-/

@[expose] public section

namespace CausalSet

/-- A preorder with a greatest element but no least element is not order-isomorphic to its dual. -/
theorem isEmpty_orderIso_orderDual_of_isTop
    {α : Type*} [Preorder α] {t : α} (ht : IsTop t)
    (hbot : ∀ b : α, ¬ IsBot b) : IsEmpty (α ≃o αᵒᵈ) := by
  refine ⟨fun e => hbot (OrderDual.ofDual (e t)) ?_⟩
  intro a
  change OrderDual.toDual a ≤ e t
  simpa only [e.apply_symm_apply] using e.monotone (ht (e.symm (OrderDual.toDual a)))

/-- The three-element order `V`: two incomparable minimal elements below a top.
Its order dual `Veeᵒᵈ` is the order `Λ`. -/
inductive Vee
  | left | right | top
  deriving DecidableEq

namespace Vee

instance : Fintype Vee :=
  ⟨⟨{left, right, top}, by decide⟩, fun x => by cases x <;> decide⟩

/-- Reflexive order with `top` above both other elements. -/
def le (x y : Vee) : Bool := x == y || y == top

instance : PartialOrder Vee where
  le x y := le x y
  le_refl x := by cases x <;> decide
  le_trans x y z := by cases x <;> cases y <;> cases z <;> decide
  le_antisymm x y := by cases x <;> cases y <;> decide

instance : DecidableLE Vee := fun x y => inferInstanceAs (Decidable (le x y = true))
instance : DecidableLT Vee := fun _ _ => decidable_of_iff _ lt_iff_le_not_ge.symm

-- This concrete type has no competing locally finite order instance.
instance : LocallyFiniteOrder Vee := Fintype.toLocallyFiniteOrder

/-- The element `top` is greatest in `Vee`. -/
theorem isTop_top : IsTop top := by
  intro x
  cases x <;> decide

/-- None of the three elements is least in `Vee`. -/
theorem not_isBot (b : Vee) : ¬ IsBot b := by
  intro h
  cases b with
  | left => exact (by decide : ¬ left ≤ right) (h right)
  | right => exact (by decide : ¬ right ≤ left) (h left)
  | top => exact (by decide : ¬ top ≤ left) (h left)

/-- `V` is not order-isomorphic to its dual `Λ`. -/
theorem isEmpty_orderIso_orderDual : IsEmpty (Vee ≃o Veeᵒᵈ) :=
  isEmpty_orderIso_orderDual_of_isTop isTop_top not_isBot

/-- Interval abundance does not separate `V` from its non-isomorphic dual `Λ`. -/
theorem intervalAbundance_not_complete :
    intervalAbundance Veeᵒᵈ = intervalAbundance Vee ∧ IsEmpty (Vee ≃o Veeᵒᵈ) :=
  ⟨funext intervalAbundance_toDual, isEmpty_orderIso_orderDual⟩

/-- Any duality-invariant observable of finite partial orders agrees on `V` and
its non-isomorphic dual. No isomorphism-invariance assumption is needed. -/
theorem dual_invariant_not_complete {γ : Sort*}
    (F : ∀ (α : Type) [PartialOrder α] [LocallyFiniteOrder α] [Fintype α] [DecidableLT α], γ)
    (hF : ∀ (α : Type) [PartialOrder α] [LocallyFiniteOrder α] [Fintype α] [DecidableLT α],
      F αᵒᵈ = F α) :
    F Veeᵒᵈ = F Vee ∧ IsEmpty (Vee ≃o Veeᵒᵈ) :=
  ⟨hF Vee, isEmpty_orderIso_orderDual⟩

end Vee
end CausalSet
