/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

public import CausalSet.NonIdentifiability

/-!
# Non-dual finite-order non-identifiability

An isolated element is incomparable to every distinct element. This property is
preserved by order isomorphisms and order duality, so it obstructs both ordinary
and dual order isomorphisms.

The four-element orders `LamPt` (a three-element `Λ` plus an isolated point) and
`TwoChains` (two disjoint two-element chains) have equal interval abundance, but
the former has an isolated element and the latter does not. Thus interval
abundance can agree for orders that are neither isomorphic nor dual-isomorphic.

These are established finite-order facts. No novelty or minimality is asserted.
Order duality is formal reversal of `≤`, not a physical time orientation, and no
continuum geometric, metric, or dynamical conclusion is inferred.
-/

@[expose] public section

namespace CausalSet

/-- `x` is incomparable to every other element. -/
def IsIsolated {α : Type*} [Preorder α] (x : α) : Prop :=
  ∀ y, y ≠ x → ¬ x ≤ y ∧ ¬ y ≤ x

/-- Order isomorphisms preserve isolated elements. -/
theorem IsIsolated.map {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β) {x : α}
    (hx : IsIsolated x) : IsIsolated (e x) := by
  intro y hy
  have hne : e.symm y ≠ x := by
    intro h
    apply hy
    rw [← e.apply_symm_apply y, h]
  obtain ⟨hxy, hyx⟩ := hx (e.symm y) hne
  exact ⟨fun h => hxy (by simpa using e.symm.monotone h),
    fun h => hyx (by simpa using e.symm.monotone h)⟩

/-- Isolatedness is unchanged by reversing the order. -/
theorem isIsolated_toDual_iff {α : Type*} [Preorder α] {x : α} :
    IsIsolated (OrderDual.toDual x) ↔ IsIsolated x := by
  constructor
  · intro h y hy
    obtain ⟨hyx, hxy⟩ := h (OrderDual.toDual y) hy
    exact ⟨hxy, hyx⟩
  · intro h y hy
    obtain ⟨hxy, hyx⟩ := h (OrderDual.ofDual y) hy
    exact ⟨hyx, hxy⟩

/-- An order with an isolated element is neither isomorphic nor dual-isomorphic
to an order without one. -/
theorem isEmpty_orderIso_of_isIsolated {α β : Type*} [Preorder α] [Preorder β] {x : α}
    (hx : IsIsolated x) (hβ : ∀ y : β, ¬ IsIsolated y) :
    IsEmpty (α ≃o β) ∧ IsEmpty (α ≃o βᵒᵈ) := by
  constructor
  · exact ⟨fun e => hβ (e x) (hx.map e)⟩
  · refine ⟨fun e => hβ (OrderDual.ofDual (e x)) ?_⟩
    exact isIsolated_toDual_iff.mp (hx.map e)

/-- A three-element `Λ` together with an isolated point. -/
inductive LamPt
  | bot | left | right | pt
  deriving DecidableEq

namespace LamPt

instance : Fintype LamPt :=
  ⟨⟨{bot, left, right, pt}, by decide⟩, fun x => by cases x <;> decide⟩

/-- Reflexive order with `bot` below `left` and `right`, and `pt` isolated. -/
def le (x y : LamPt) : Bool :=
  x == y || x == bot && (y == left || y == right)

instance : PartialOrder LamPt where
  le x y := le x y
  le_refl x := by cases x <;> decide
  le_trans x y z := by cases x <;> cases y <;> cases z <;> decide
  le_antisymm x y := by cases x <;> cases y <;> decide

instance : DecidableLE LamPt := fun x y => inferInstanceAs (Decidable (le x y = true))
instance : DecidableLT LamPt := fun _ _ => decidable_of_iff _ lt_iff_le_not_ge.symm

-- This concrete type has no competing locally finite order instance.
instance : LocallyFiniteOrder LamPt := Fintype.toLocallyFiniteOrder

/-- The point `pt` is isolated in `LamPt`. -/
theorem isIsolated_pt : IsIsolated pt := by
  intro y hy
  cases y with
  | bot => exact ⟨by decide, by decide⟩
  | left => exact ⟨by decide, by decide⟩
  | right => exact ⟨by decide, by decide⟩
  | pt => exact (hy rfl).elim

end LamPt

/-- Two disjoint two-element chains. -/
inductive TwoChains
  | a₀ | a₁ | b₀ | b₁
  deriving DecidableEq

namespace TwoChains

instance : Fintype TwoChains :=
  ⟨⟨{a₀, a₁, b₀, b₁}, by decide⟩, fun x => by cases x <;> decide⟩

/-- Reflexive order consisting of the two strict relations `a₀ < a₁` and `b₀ < b₁`. -/
def le (x y : TwoChains) : Bool :=
  x == y || x == a₀ && y == a₁ || x == b₀ && y == b₁

instance : PartialOrder TwoChains where
  le x y := le x y
  le_refl x := by cases x <;> decide
  le_trans x y z := by cases x <;> cases y <;> cases z <;> decide
  le_antisymm x y := by cases x <;> cases y <;> decide

instance : DecidableLE TwoChains := fun x y => inferInstanceAs (Decidable (le x y = true))
instance : DecidableLT TwoChains := fun _ _ => decidable_of_iff _ lt_iff_le_not_ge.symm

-- This concrete type has no competing locally finite order instance.
instance : LocallyFiniteOrder TwoChains := Fintype.toLocallyFiniteOrder

/-- No element of `TwoChains` is isolated. -/
theorem not_isIsolated (y : TwoChains) : ¬ IsIsolated y := by
  intro h
  cases y with
  | a₀ => exact (h a₁ (by decide)).1 (by decide)
  | a₁ => exact (h a₀ (by decide)).2 (by decide)
  | b₀ => exact (h b₁ (by decide)).1 (by decide)
  | b₁ => exact (h b₀ (by decide)).2 (by decide)

end TwoChains

/-- Interval abundance does not separate `LamPt` from `TwoChains`, which are
neither isomorphic nor dual-isomorphic. -/
theorem intervalAbundance_not_complete_nonDual :
    intervalAbundance LamPt = intervalAbundance TwoChains ∧
      IsEmpty (LamPt ≃o TwoChains) ∧ IsEmpty (LamPt ≃o TwoChainsᵒᵈ) := by
  refine ⟨?_, isEmpty_orderIso_of_isIsolated LamPt.isIsolated_pt TwoChains.not_isIsolated⟩
  funext k
  match k with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | k + 4 =>
      have hLamPt : Fintype.card LamPt ≤ k + 4 := by
        simpa only [show Fintype.card LamPt = 4 by decide] using Nat.le_add_left 4 k
      have hTwoChains : Fintype.card TwoChains ≤ k + 4 := by
        simpa only [show Fintype.card TwoChains = 4 by decide] using Nat.le_add_left 4 k
      rw [intervalAbundance_eq_zero_of_card_le (α := LamPt) hLamPt,
        intervalAbundance_eq_zero_of_card_le (α := TwoChains) hTwoChains]

end CausalSet
