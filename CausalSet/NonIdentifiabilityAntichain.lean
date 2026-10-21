/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

public import CausalSet.NonIdentifiabilityNonDual
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Antichain

/-!
# Non-identifiability with antichain counts

This module counts finite antichains by cardinality and proves that the count is
preserved by order isomorphisms and order duality. It then gives a five-element
example showing that interval abundance together with all antichain counts does
not determine a finite order up to isomorphism or duality.

The witnesses are `NPlus`, with strict relations `a < e`, `b < e`, `c < e`, and
`c < d`, and `ButterflyPt`, with `b` and `c` below both `d` and `e`, together
with the isolated point `a`. No novelty or minimality is asserted.
-/

@[expose] public section

namespace CausalSet

/-- Decidability of the antichain property for a finite set; used as a local instance. -/
@[instance_reducible]
def decidableIsAntichainFinset {α : Type*} [LE α] [DecidableEq α] [DecidableLE α]
    (s : Finset α) : Decidable (IsAntichain (· ≤ ·) (s : Set α)) := by
  unfold IsAntichain Set.Pairwise
  apply decidable_of_iff' (∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ a ≤ b) Iff.rfl

attribute [local instance] decidableIsAntichainFinset

/-- Number of `k`-element antichains of a finite order.

Unlike `intervalAbundance`, this definition requires `DecidableEq` because the
antichain predicate compares distinct elements of a finite set. -/
def antichainCount (α : Type*) [LE α] [Fintype α] [DecidableEq α] [DecidableLE α]
    (k : ℕ) : ℕ :=
  (Finset.filter (fun s : Finset α =>
      IsAntichain (fun a b : α => a ≤ b) (s : Set α))
    ((Finset.univ : Finset α).powersetCard k)).card

variable {α β : Type*} [LE α] [Fintype α] [DecidableEq α] [DecidableLE α]
  [LE β] [Fintype β] [DecidableEq β] [DecidableLE β]

/-- Antichain counts are preserved by order isomorphisms. -/
theorem antichainCount_congr (e : α ≃o β) (k : ℕ) :
    antichainCount β k = antichainCount α k := by
  unfold antichainCount
  refine Finset.card_bij'
    (fun s _ => s.map e.symm.toEquiv.toEmbedding)
    (fun s _ => s.map e.toEquiv.toEmbedding) ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_powersetCard] at hs ⊢
      exact ⟨Finset.subset_univ _, by simpa using hs.1.2⟩
    · simpa using hs.2.image_iso e.symm
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_powersetCard] at hs ⊢
      exact ⟨Finset.subset_univ _, by simpa using hs.1.2⟩
    · simpa using hs.2.image_iso e
  · intro s hs
    ext x
    simp
  · intro s hs
    ext x
    simp

/-- Antichain counts are unchanged by reversing the order. -/
theorem antichainCount_toDual (k : ℕ) : antichainCount αᵒᵈ k = antichainCount α k := by
  unfold antichainCount
  refine Finset.card_bij'
    (fun s _ => s.map (OrderDual.ofDual : αᵒᵈ ≃ α).toEmbedding)
    (fun s _ => s.map (OrderDual.toDual : α ≃ αᵒᵈ).toEmbedding) ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_powersetCard] at hs ⊢
      exact ⟨Finset.subset_univ _, by simpa using hs.1.2⟩
    · simpa using
        hs.2.swap.image OrderDual.ofDual
          (fun {a b : αᵒᵈ} (h : OrderDual.ofDual a ≤ OrderDual.ofDual b) => h)
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_powersetCard] at hs ⊢
      exact ⟨Finset.subset_univ _, by simpa using hs.1.2⟩
    · simpa using
        hs.2.swap.image OrderDual.toDual
          (fun {a b : α} (h : OrderDual.toDual a ≤ OrderDual.toDual b) => h)
  · intro s hs
    ext x
    simp
  · intro s hs
    ext x
    simp

/-- No antichain can have cardinality larger than its finite carrier. -/
theorem antichainCount_eq_zero_of_card_lt {k : ℕ} (hk : Fintype.card α < k) :
    antichainCount α k = 0 := by
  unfold antichainCount
  rw [Finset.powersetCard_eq_empty.mpr (by simpa using hk)]
  simp

/-- A five-element order shaped like an `N`, with one additional minimal element. -/
inductive NPlus
  | a | b | c | d | e
  deriving DecidableEq

namespace NPlus

instance : Fintype NPlus :=
  ⟨⟨{a, b, c, d, e}, by decide⟩, fun x => by cases x <;> decide⟩

/-- Reflexive order with strict relations `a < e`, `b < e`, `c < e`, and `c < d`. -/
def le (x y : NPlus) : Bool :=
  x == y || y == e && (x == a || x == b || x == c) || x == c && y == d

instance : PartialOrder NPlus where
  le x y := le x y
  le_refl x := by cases x <;> decide
  le_trans x y z := by cases x <;> cases y <;> cases z <;> decide
  le_antisymm x y := by cases x <;> cases y <;> decide

instance : DecidableLE NPlus := fun x y => inferInstanceAs (Decidable (le x y = true))
instance : DecidableLT NPlus := fun _ _ => decidable_of_iff _ lt_iff_le_not_ge.symm

-- This concrete type has no competing locally finite order instance.
instance : LocallyFiniteOrder NPlus := Fintype.toLocallyFiniteOrder

/-- No element of `NPlus` is isolated. -/
theorem not_isIsolated (x : NPlus) : ¬ IsIsolated x := by
  intro h
  cases x with
  | a => exact (h e (by decide)).1 (by decide)
  | b => exact (h e (by decide)).1 (by decide)
  | c => exact (h d (by decide)).1 (by decide)
  | d => exact (h c (by decide)).2 (by decide)
  | e => exact (h a (by decide)).2 (by decide)

end NPlus

/-- A four-element butterfly order together with an isolated point. -/
inductive ButterflyPt
  | a | b | c | d | e
  deriving DecidableEq

namespace ButterflyPt

instance : Fintype ButterflyPt :=
  ⟨⟨{a, b, c, d, e}, by decide⟩, fun x => by cases x <;> decide⟩

/-- Reflexive order with `b` and `c` below both `d` and `e`, and `a` isolated. -/
def le (x y : ButterflyPt) : Bool :=
  x == y || (x == b || x == c) && (y == d || y == e)

instance : PartialOrder ButterflyPt where
  le x y := le x y
  le_refl x := by cases x <;> decide
  le_trans x y z := by cases x <;> cases y <;> cases z <;> decide
  le_antisymm x y := by cases x <;> cases y <;> decide

instance : DecidableLE ButterflyPt := fun x y => inferInstanceAs (Decidable (le x y = true))
instance : DecidableLT ButterflyPt := fun _ _ => decidable_of_iff _ lt_iff_le_not_ge.symm

-- This concrete type has no competing locally finite order instance.
instance : LocallyFiniteOrder ButterflyPt := Fintype.toLocallyFiniteOrder

/-- The point `a` is isolated in `ButterflyPt`. -/
theorem isIsolated_a : IsIsolated a := by
  intro y hy
  cases y with
  | a => exact (hy rfl).elim
  | b => exact ⟨by decide, by decide⟩
  | c => exact ⟨by decide, by decide⟩
  | d => exact ⟨by decide, by decide⟩
  | e => exact ⟨by decide, by decide⟩

end ButterflyPt

/-- Interval abundance together with antichain counts does not separate
`ButterflyPt` from `NPlus`, which are neither isomorphic nor dual-isomorphic. -/
theorem intervalAbundance_antichainCount_not_complete_nonDual :
    intervalAbundance ButterflyPt = intervalAbundance NPlus ∧
      antichainCount ButterflyPt = antichainCount NPlus ∧
      IsEmpty (ButterflyPt ≃o NPlus) ∧ IsEmpty (ButterflyPt ≃o NPlusᵒᵈ) := by
  refine ⟨?_, ?_, isEmpty_orderIso_of_isIsolated
    ButterflyPt.isIsolated_a NPlus.not_isIsolated⟩
  · funext k
    match k with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | k + 5 =>
        have hButterflyPt : Fintype.card ButterflyPt ≤ k + 5 := by
          have : Fintype.card ButterflyPt = 5 := by decide
          omega
        have hNPlus : Fintype.card NPlus ≤ k + 5 := by
          have : Fintype.card NPlus = 5 := by decide
          omega
        rw [intervalAbundance_eq_zero_of_card_le (α := ButterflyPt) hButterflyPt,
          intervalAbundance_eq_zero_of_card_le (α := NPlus) hNPlus]
  · funext k
    match k with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | k + 6 =>
        have hButterflyPt : Fintype.card ButterflyPt < k + 6 := by
          have : Fintype.card ButterflyPt = 5 := by decide
          omega
        have hNPlus : Fintype.card NPlus < k + 6 := by
          have : Fintype.card NPlus = 5 := by decide
          omega
        rw [antichainCount_eq_zero_of_card_lt (α := ButterflyPt) hButterflyPt,
          antichainCount_eq_zero_of_card_lt (α := NPlus) hNPlus]

end CausalSet
