/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

import CausalSet
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.NormNum

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

/-- info: 'CausalSet.isEmpty_orderIso_orderDual_of_isTop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.isEmpty_orderIso_orderDual_of_isTop

/-- info: 'CausalSet.Vee.isEmpty_orderIso_orderDual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.Vee.isEmpty_orderIso_orderDual

/-- info: 'CausalSet.Vee.intervalAbundance_not_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.Vee.intervalAbundance_not_complete

/-- info: 'CausalSet.Vee.dual_invariant_not_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.Vee.dual_invariant_not_complete

/-- info: 'CausalSet.isEmpty_orderIso_of_isIsolated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.isEmpty_orderIso_of_isIsolated

/-- info: 'CausalSet.intervalAbundance_not_complete_nonDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.intervalAbundance_not_complete_nonDual

/-- info: 'CausalSet.antichainCount_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.antichainCount_congr

/-- info: 'CausalSet.antichainCount_toDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.antichainCount_toDual

/-- info: 'CausalSet.antichainCount_eq_zero_of_card_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.antichainCount_eq_zero_of_card_lt

/-- info: 'CausalSet.intervalAbundance_antichainCount_not_complete_nonDual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.intervalAbundance_antichainCount_not_complete_nonDual

/-- info: 'CausalSet.RandomTwoOrder.windowCount_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.RandomTwoOrder.windowCount_spec

/-- info: 'CausalSet.RandomTwoOrder.sum_intervalAbundance_twoOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.RandomTwoOrder.sum_intervalAbundance_twoOrder

/-- info: 'CausalSet.RandomTwoOrder.sum_links_twoOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.RandomTwoOrder.sum_links_twoOrder

/-- info: 'CausalSet.RandomTwoOrder.sum_relations_twoOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.RandomTwoOrder.sum_relations_twoOrder

/-- info: 'CausalSet.RandomTwoOrder.sum_bdCombination2_twoOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.RandomTwoOrder.sum_bdCombination2_twoOrder

/-! ## Labelled correspondence distance -/

/-- info: 'LabelledCorrespondence.jointDistance_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LabelledCorrespondence.jointDistance_triangle

/-- info: 'LabelledCorrespondence.jointDistance_congr_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LabelledCorrespondence.jointDistance_congr_left

/-- info: 'LabelledCorrespondence.exists_jointDistortion_eq_zero_of_jointDistance_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms LabelledCorrespondence.exists_jointDistortion_eq_zero_of_jointDistance_eq_zero

/-- info: 'LabelledCorrespondence.jointDistance_eq_zero_iff_exists_preserving_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms LabelledCorrespondence.jointDistance_eq_zero_iff_exists_preserving_equiv

section LabelledCorrespondenceExamples

open LabelledCorrespondence

/-- A concrete two-label family whose kernels vanish identically. -/
noncomputable def zeroKernelFamily : KernelFamily (Fin 2) (Fin 3) := fun _ => ⊥

example : Preserves zeroKernelFamily zeroKernelFamily (Equiv.refl (Fin 3)) := by
  simp [Preserves, zeroKernelFamily]

example : jointDistance zeroKernelFamily zeroKernelFamily = 0 :=
  jointDistance_self zeroKernelFamily

end LabelledCorrespondenceExamples

/-! ## Three-element non-identifiability examples -/

section NonIdentifiabilityExamples

open CausalSet

example : Fintype.card Vee = 3 := by decide
example : intervalAbundance Vee 0 = 2 := by decide
example : intervalAbundance Vee 1 = 0 := by decide
example : intervalAbundance Veeᵒᵈ 0 = 2 := by decide

example : intervalAbundance Veeᵒᵈ = intervalAbundance Vee ∧ IsEmpty (Vee ≃o Veeᵒᵈ) :=
  Vee.dual_invariant_not_complete
    (fun α _ _ _ _ => intervalAbundance α)
    (fun _ _ _ _ _ => funext intervalAbundance_toDual)

end NonIdentifiabilityExamples

/-! ## Four-element non-dual non-identifiability examples -/

section NonDualNonIdentifiabilityExamples

open CausalSet

example : Fintype.card LamPt = 4 := by decide
example : Fintype.card TwoChains = 4 := by decide
example : intervalAbundance LamPt 0 = 2 := by decide
example : intervalAbundance TwoChains 0 = 2 := by decide
example : intervalAbundance LamPt 1 = 0 := by decide
example : intervalAbundance TwoChains 1 = 0 := by decide

end NonDualNonIdentifiabilityExamples

/-! ## Five-element antichain-strengthened non-identifiability examples -/

section AntichainNonIdentifiabilityExamples

open CausalSet

example : Fintype.card NPlus = 5 := by decide
example : Fintype.card ButterflyPt = 5 := by decide
example : antichainCount NPlus 3 = 2 := by decide
example : antichainCount ButterflyPt 3 = 2 := by decide
example : antichainCount NPlus 2 = 6 := by decide
example : intervalAbundance NPlus 0 = 4 := by decide

end AntichainNonIdentifiabilityExamples

/-! ## Finite random two-order examples -/

section RandomTwoOrderExamples

open CausalSet CausalSet.RandomTwoOrder

example : windowCount 4 1 (0 : Fin 4) (3 : Fin 4) = 4 := by decide

example :
    ∑ σ : Equiv.Perm (Fin 3), (intervalAbundance (TwoOrder σ) 0 : ℚ) = 8 := by
  norm_num [sum_intervalAbundance_twoOrder_closed, harmonic_succ, Nat.factorial]

example :
    ∑ σ : Equiv.Perm (Fin 3), bdCombination2 (TwoOrder σ) = 6 := by
  simpa [Nat.factorial] using sum_bdCombination2_twoOrder (N := 3) (by decide)

example :
    ∑ σ : Equiv.Perm (Fin 4), bdCombination2 (TwoOrder σ) = 24 := by decide +kernel

end RandomTwoOrderExamples
