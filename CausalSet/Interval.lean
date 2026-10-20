/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

public import CausalSet.Basic

/-!
# Alexandrov intervals

For elements `x y` of a locally finite preorder, the open Alexandrov interval is the finite set of
elements strictly between them. Its cardinality is an elementary order-theoretic proxy for volume
used in later causal-set constructions. It becomes a physical volume estimator only after adding
sprinkling and density assumptions.

The interval excludes both endpoints. Whenever `¬ x < y`—for example if `x = y`, `y < x`, or the
endpoints are incomparable—the interval is empty and there is no link. When `x < y`, an empty
interval characterizes a link.
-/

@[expose] public section

namespace CausalSet

variable {α : Type*} [Preorder α] [LocallyFiniteOrder α]

/-- The finite open Alexandrov interval between `x` and `y`. -/
def alexandrovInterval (x y : α) : Finset α :=
  Finset.Ioo x y

/-- The finite Alexandrov interval coerces to the ordinary open order interval. -/
@[simp] theorem coe_alexandrovInterval (x y : α) :
    (↑(alexandrovInterval x y) : Set α) = Set.Ioo x y := by
  ext z
  simp [alexandrovInterval]

@[simp] theorem mem_alexandrovInterval {x y z : α} :
    z ∈ alexandrovInterval x y ↔ x < z ∧ z < y := by
  simp only [alexandrovInterval, Finset.mem_Ioo]

/-- Number of elements strictly between `x` and `y`. -/
def intervalCard (x y : α) : ℕ :=
  (alexandrovInterval x y).card

@[simp] theorem intervalCard_eq_zero {x y : α} :
    intervalCard x y = 0 ↔ alexandrovInterval x y = ∅ := by
  simp [intervalCard]

end CausalSet
