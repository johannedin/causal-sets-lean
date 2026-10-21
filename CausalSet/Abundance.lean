/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

public import CausalSet.Transport
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Interval abundance

For a finite locally finite preorder, `intervalAbundance α k` counts ordered strict
pairs with exactly `k` elements in their open Alexandrov interval. Its zeroth
entry counts links, and summing over its finite support counts all strict pairs.
The counts are invariant under order isomorphism and order duality.

These are elementary finite-order counting identities. Antisymmetry is not needed;
distinct mutually related elements in a preorder do not form a strict pair.
Invariance is not completeness: these statistics are not asserted to determine
an order up to isomorphism. No volume, dimension, continuum geometry, or physical
dynamics is inferred.
-/

@[expose] public section

namespace CausalSet

open Finset

variable {α β : Type*}
variable [Preorder α] [LocallyFiniteOrder α] [DecidableLT α]

/-- Link decidability follows from strict-order decidability and interval cardinality. -/
instance decidableRelIsLink : DecidableRel (IsLink : α → α → Prop) := fun _ _ =>
  decidable_of_iff _ isLink_iff_lt_and_intervalCard_eq_zero.symm

/-- Interval abundance `N_k` counts ordered strict pairs with `k` elements between them. -/
def intervalAbundance (α : Type*) [Preorder α] [LocallyFiniteOrder α] [Fintype α]
    [DecidableLT α] (k : ℕ) : ℕ :=
  #{p : α × α | p.1 < p.2 ∧ intervalCard p.1 p.2 = k}

/-- The two-dimensional Benincasa--Dowker interval combination
`N - 2N₀ + 4N₁ - 2N₂`; its identification with the BD action is not formalized. -/
def bdCombination2 (α : Type*) [Preorder α] [LocallyFiniteOrder α] [Fintype α]
    [DecidableLT α] : ℤ :=
  Fintype.card α - 2 * intervalAbundance α 0 + 4 * intervalAbundance α 1 -
    2 * intervalAbundance α 2

variable [Fintype α]
variable [Preorder β] [LocallyFiniteOrder β] [Fintype β] [DecidableLT β]

/-- Links are exactly the strict pairs counted by the zeroth abundance. -/
theorem intervalAbundance_zero :
    intervalAbundance α 0 = #{p : α × α | IsLink p.1 p.2} := by
  simp only [intervalAbundance, isLink_iff_lt_and_intervalCard_eq_zero]

omit [DecidableLT α] in
/-- An open interval omits its left endpoint, so is smaller than the finite carrier. -/
theorem intervalCard_lt_card (x y : α) : intervalCard x y < Fintype.card α := by
  exact Finset.card_lt_univ_of_notMem (x := x) (by simp [mem_alexandrovInterval])

/-- No interval abundance occurs at or above the cardinality of the carrier. -/
theorem intervalAbundance_eq_zero_of_card_le {k : ℕ} (hk : Fintype.card α ≤ k) :
    intervalAbundance α k = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro p _ h
  exact (not_lt_of_ge hk) (h.2 ▸ intervalCard_lt_card p.1 p.2)

/-- Partitioning strict pairs by interval cardinality recovers their total count. -/
theorem sum_intervalAbundance :
    ∑ k ∈ range (Fintype.card α), intervalAbundance α k =
      #{p : α × α | p.1 < p.2} := by
  symm
  simpa only [intervalAbundance, filter_filter] using
    (card_eq_sum_card_fiberwise
      (f := fun p : α × α => intervalCard p.1 p.2)
      (s := {p : α × α | p.1 < p.2}) (t := range (Fintype.card α))
      (fun p _ => mem_range.mpr (intervalCard_lt_card p.1 p.2)))

/-- Order isomorphisms preserve every interval abundance. -/
theorem intervalAbundance_congr (e : α ≃o β) (k : ℕ) :
    intervalAbundance β k = intervalAbundance α k := by
  unfold intervalAbundance
  symm
  apply Finset.card_equiv (e.toEquiv.prodCongr e.toEquiv)
  intro p
  simp [intervalCard_map]

/-- Reversing the order preserves abundance by exchanging both endpoints of each pair. -/
theorem intervalAbundance_toDual (k : ℕ) :
    intervalAbundance αᵒᵈ k = intervalAbundance α k := by
  unfold intervalAbundance
  symm
  apply Finset.card_equiv
    ((Equiv.prodComm α α).trans (OrderDual.toDual.prodCongr OrderDual.toDual))
  intro p
  simp [intervalCard_toDual]

end CausalSet
