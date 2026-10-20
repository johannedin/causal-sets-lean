/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

import CausalSet
import Mathlib.Order.Interval.Finset.Fin

/-!
# Axiom audit

These guarded commands make the trusted dependencies of foundational results visible and cause
their dedicated CI step to fail if they drift.
-/

/-- info: 'CausalSet.mem_alexandrovInterval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.mem_alexandrovInterval

/-- info: 'CausalSet.intervalCard_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.intervalCard_eq_zero

/-- info: 'CausalSet.isLink_iff_covBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.isLink_iff_covBy

/-- info: 'CausalSet.isLink_iff_lt_and_intervalCard_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.isLink_iff_lt_and_intervalCard_eq_zero

/-- info: 'CausalSet.lt_iff_transGen_isLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.lt_iff_transGen_isLink

/-- info: 'CausalSet.reflTransGen_isLink_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.reflTransGen_isLink_iff

/-- info: 'CausalSet.le_iff_eq_or_transGen_isLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.le_iff_eq_or_transGen_isLink

/-- info: 'CausalSet.le_iff_reflTransGen_isLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.le_iff_reflTransGen_isLink

/-- info: 'CausalSet.alexandrovInterval_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.alexandrovInterval_map

/-- info: 'CausalSet.intervalCard_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.intervalCard_map

/-- info: 'CausalSet.isLink_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.isLink_map

/-- info: 'CausalSet.intervalCard_toDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.intervalCard_toDual

/-- info: 'CausalSet.isLink_toDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.isLink_toDual

/-- info: 'CausalSet.intervalAbundance_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.intervalAbundance_zero

/-- info: 'CausalSet.sum_intervalAbundance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.sum_intervalAbundance

/-- info: 'CausalSet.intervalAbundance_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.intervalAbundance_congr

/-- info: 'CausalSet.intervalAbundance_toDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.intervalAbundance_toDual

/-! ## Executable interval-abundance examples

These kernel-checked examples distinguish strict from reflexive pairs and check
that endpoints are excluded. Extra concrete-order imports stay out of the library.
-/

section IntervalAbundanceExamples

open CausalSet

example : intervalAbundance (Fin 4) 0 = 3 := by decide
example : intervalAbundance (Fin 4) 1 = 2 := by decide
example : intervalAbundance (Fin 4) 2 = 1 := by decide
example : intervalAbundance (Fin 4) 3 = 0 := by decide

section ProductSquare

-- Derive strict-order decidability locally, without adding a product-order instance globally.
local instance : DecidableLT (Fin 2 × Fin 2) := fun _ _ =>
  decidable_of_iff _ lt_iff_le_not_ge.symm

example : intervalAbundance (Fin 2 × Fin 2) 0 = 4 := by decide
example : intervalAbundance (Fin 2 × Fin 2) 2 = 1 := by decide

end ProductSquare

example : intervalAbundance (Fin 0) 0 = 0 := by decide
example : intervalAbundance (Fin 4)ᵒᵈ 1 = 2 := by decide
example (k : ℕ) : intervalAbundance (Fin 4)ᵒᵈ k = intervalAbundance (Fin 4) k :=
  intervalAbundance_toDual k

end IntervalAbundanceExamples
