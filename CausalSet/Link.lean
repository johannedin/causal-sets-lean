/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

public import CausalSet.Interval

/-!
# Links

A causal-set link is a pair `x < y` with no intervening element.  This is exactly mathlib's
cover relation.  The equivalence below is proved from the definitions, leaving later developments
free to use either causal-set vocabulary or the existing order-theory API.

These are purely order-theoretic reconstruction results: they recover `<` (and, for partial orders,
`≤`) from links, but supply no dimension, embedding, sprinkling, density, volume, continuum
approximation, or metric information.
-/

@[expose] public section

namespace CausalSet

variable {α : Type*} [Preorder α] [LocallyFiniteOrder α]

/-- `IsLink x y` means that `x` strictly precedes `y` with no element strictly between them. -/
def IsLink (x y : α) : Prop :=
  x < y ∧ alexandrovInterval x y = ∅

/-- A link is, in particular, a strict causal precedence relation. -/
theorem IsLink.lt {x y : α} (h : IsLink x y) : x < y :=
  h.1

theorem isLink_iff_covBy {x y : α} :
    IsLink x y ↔ x ⋖ y := by
  constructor
  · rintro ⟨hxy, hInterval⟩
    refine ⟨hxy, ?_⟩
    intro z hxz hzy
    have hz : z ∈ alexandrovInterval x y :=
      mem_alexandrovInterval.mpr ⟨hxz, hzy⟩
    rw [hInterval] at hz
    simp at hz
  · intro h
    refine ⟨h.1, ?_⟩
    ext z
    constructor
    · intro hz
      exact (h.2 (mem_alexandrovInterval.mp hz).1
        (mem_alexandrovInterval.mp hz).2).elim
    · intro hz
      simp at hz

theorem isLink_iff_lt_and_intervalCard_eq_zero {x y : α} :
    IsLink x y ↔ x < y ∧ intervalCard x y = 0 := by
  simp [IsLink]

/-- In a locally finite preorder, strict precedence is the transitive closure of links. -/
theorem lt_iff_transGen_isLink {x y : α} :
    x < y ↔ Relation.TransGen IsLink x y := by
  have mapCover : ∀ {a b : α}, Relation.TransGen (fun p q => p ⋖ q) a b →
      Relation.TransGen IsLink a b := by
    intro a b h
    induction h with
    | single hab =>
        exact Relation.TransGen.single (isLink_iff_covBy.mpr hab)
    | tail _ hbc ih =>
        exact Relation.TransGen.tail ih (isLink_iff_covBy.mpr hbc)
  have mapLink : ∀ {a b : α}, Relation.TransGen IsLink a b →
      Relation.TransGen (fun p q => p ⋖ q) a b := by
    intro a b h
    induction h with
    | single hab =>
        exact Relation.TransGen.single (isLink_iff_covBy.mp hab)
    | tail _ hbc ih =>
        exact Relation.TransGen.tail ih (isLink_iff_covBy.mp hbc)
  constructor
  · intro hxy
    exact mapCover ((lt_iff_transGen_covBy (x := x) (y := y)).mp hxy)
  · intro hLink
    apply (lt_iff_transGen_covBy (x := x) (y := y)).mpr
    exact mapLink hLink

/--
In a locally finite preorder, a reflexive link path recovers equality or strict precedence.

This does not in general recover `x ≤ y`: without antisymmetry, distinct elements may satisfy both
`x ≤ y` and `y ≤ x`, while neither equality nor strict precedence holds.
-/
theorem reflTransGen_isLink_iff {x y : α} :
    Relation.ReflTransGen IsLink x y ↔ x = y ∨ x < y := by
  rw [Relation.reflTransGen_iff_eq_or_transGen, ← lt_iff_transGen_isLink, eq_comm]

/-- In a locally finite partial order, reflexive precedence is equality or a nonempty link path. -/
theorem le_iff_eq_or_transGen_isLink {β : Type*} [PartialOrder β] [LocallyFiniteOrder β]
    {x y : β} :
    x ≤ y ↔ x = y ∨ Relation.TransGen IsLink x y := by
  constructor
  · intro hxy
    rcases eq_or_lt_of_le hxy with hEq | hLt
    · exact Or.inl hEq
    · exact Or.inr (lt_iff_transGen_isLink.mp hLt)
  · rintro (rfl | hLink)
    · exact le_rfl
    · exact le_of_lt (lt_iff_transGen_isLink.mpr hLink)

/-- In a locally finite partial order, reflexive precedence is the reflexive–transitive closure of
links. -/
theorem le_iff_reflTransGen_isLink {β : Type*} [PartialOrder β] [LocallyFiniteOrder β]
    {x y : β} :
    x ≤ y ↔ Relation.ReflTransGen IsLink x y := by
  rw [reflTransGen_isLink_iff, le_iff_eq_or_lt]

end CausalSet
