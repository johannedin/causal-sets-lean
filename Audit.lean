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

/-! ## Finite Pauli–Jordan foundations -/

/-- info: 'CausalSet.PauliJordan.twoOrder_sign_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.twoOrder_sign_identity

/-- info: 'CausalSet.PauliJordan.pauliJordan_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.pauliJordan_transpose

/-- info: 'CausalSet.PauliJordan.iPauliJordan_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.iPauliJordan_isHermitian

/-- info: 'CausalSet.PauliJordan.normalizedIPauliJordan_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.normalizedIPauliJordan_isHermitian

/-- info: 'CausalSet.PauliJordan.pauliJordan_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.pauliJordan_relabel

/-- info: 'CausalSet.PauliJordan.iPauliJordan_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.iPauliJordan_relabel

/-- info: 'CausalSet.PauliJordan.normalizedIPauliJordan_relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.normalizedIPauliJordan_relabel

/-- info: 'CausalSet.PauliJordan.twoOrder_lt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.twoOrder_lt_iff

section PauliJordanExamples

open CausalSet.PauliJordan

-- Two points with the same increasing rank in both coordinates.
example :
    2 * relationSign (coordinatePrecedes (id : Fin 2 → Fin 2) id) 0 1 =
      coordinateSign (0 : Fin 2) 1 + coordinateSign (0 : Fin 2) 1 :=
  twoOrder_sign_identity id id Function.injective_id Function.injective_id 0 1

example : relationSign (coordinatePrecedes (id : Fin 2 → Fin 2) id) 0 1 = -1 := by
  decide

example :
    (iPauliJordan (coordinatePrecedes (id : Fin 2 → Fin 2) id)).IsHermitian :=
  iPauliJordan_isHermitian _

example :
    (normalizedIPauliJordan (coordinatePrecedes (id : Fin 2 → Fin 2) id)).IsHermitian :=
  normalizedIPauliJordan_isHermitian _

end PauliJordanExamples

/-! ## Exact finite Fourier/Cayley representation -/

/-- info: 'CausalSet.PauliJordan.signMatrix_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.signMatrix_transpose

/-- info: 'CausalSet.PauliJordan.signOperator_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.signOperator_isHermitian

/-- info: 'CausalSet.PauliJordan.normalizedIPauliJordan_coordinatePrecedes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.normalizedIPauliJordan_coordinatePrecedes

/-- info: 'CausalSet.PauliJordan.normalizedIPauliJordan_relativePermutation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.normalizedIPauliJordan_relativePermutation

/-- info: 'CausalSet.PauliJordan.twistedShift_mulVec_twistedFourierVector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.twistedShift_mulVec_twistedFourierVector

/-- info: 'CausalSet.PauliJordan.one_sub_mul_geom_sum_of_pow_eq_neg_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.one_sub_mul_geom_sum_of_pow_eq_neg_one

/-- info: 'CausalSet.PauliJordan.AntiperiodicFourier.root_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.AntiperiodicFourier.root_pow

/-- info: 'CausalSet.PauliJordan.AntiperiodicFourier.root_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.AntiperiodicFourier.root_injective

/-- info: 'CausalSet.PauliJordan.AntiperiodicFourier.orthonormal_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.AntiperiodicFourier.orthonormal_vec

/-- info: 'CausalSet.PauliJordan.AntiperiodicFourier.shift_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.AntiperiodicFourier.shift_vec

/-- info: 'CausalSet.PauliJordan.AntiperiodicFourier.shift_pow_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.AntiperiodicFourier.shift_pow_vec

/-- info: 'CausalSet.PauliJordan.AntiperiodicFourier.shift_pow_antiperiodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.AntiperiodicFourier.shift_pow_antiperiodic

/-- info: 'CausalSet.PauliJordan.AntiperiodicFourier.sign_mulVec_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.AntiperiodicFourier.sign_mulVec_vec

/-- info: 'CausalSet.PauliJordan.AntiperiodicFourier.signMatrix_eq_neg_sum_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.AntiperiodicFourier.signMatrix_eq_neg_sum_shift

/-- info: 'CausalSet.PauliJordan.AntiperiodicFourier.eig_eq_I_mul_cot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.AntiperiodicFourier.eig_eq_I_mul_cot

/-- info: 'CausalSet.PauliJordan.AntiperiodicFourier.signOperator_mulVec_vec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.AntiperiodicFourier.signOperator_mulVec_vec

/-- info: 'CausalSet.PauliJordan.AntiperiodicFourier.one_sub_shift_mul_shiftInverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.AntiperiodicFourier.one_sub_shift_mul_shiftInverse

/-- info: 'CausalSet.PauliJordan.AntiperiodicFourier.shiftInverse_mul_one_sub_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.AntiperiodicFourier.shiftInverse_mul_one_sub_shift

/-- info: 'CausalSet.PauliJordan.AntiperiodicFourier.signMatrix_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CausalSet.PauliJordan.AntiperiodicFourier.signMatrix_cayley

section PauliJordanFourierExamples

open Matrix CausalSet.PauliJordan CausalSet.PauliJordan.AntiperiodicFourier

-- Orientation: S has positive entries above the diagonal, negative below.
example : signMatrix 2 0 1 = 1 := by norm_num [signMatrix, coordinateSign]
example : signMatrix 2 1 0 = -1 := by norm_num [signMatrix, coordinateSign]

example (f : Fin 3 → ℂ) :
    (twistedShift 3 *ᵥ f) 0 = -f (Fin.last 2) :=
  twistedShift_mulVec_zero 2 f

example (f : Fin 3 → ℂ) (a : Fin 2) :
    (twistedShift 3 *ᵥ f) a.succ = f a.castSucc :=
  twistedShift_mulVec_succ 2 f a

-- The smallest positive dimension and a two-dimensional case.
example : twistedShift 1 ^ 1 = -(1 : Matrix (Fin 1) (Fin 1) ℂ) :=
  shift_pow_antiperiodic 0

example : twistedShift 2 ^ 2 = -(1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  shift_pow_antiperiodic 1

example :
    normalizedIPauliJordan
      (coordinatePrecedes (Equiv.refl (Fin 2)) (Equiv.refl (Fin 2))) =
        signOperator 2 + signOperator 2 := by
  simpa using normalizedIPauliJordan_relativePermutation 2
    (Equiv.refl (Fin 2)) (Equiv.refl (Fin 2))

example : Orthonormal ℂ (vec 1) := orthonormal_vec 1

example :
    (signMatrix 2).map (algebraMap ℝ ℂ) =
      -((1 + twistedShift 2) * shiftInverse 1) :=
  signMatrix_cayley 1

example :
    signOperator 2 *ᵥ ⇑(vec 1 (0 : Fin 2)) =
      (Complex.cot ((angle 1 (0 : Fin 2) : ℂ) / 2) / (4 * (1+1 : ℂ))) •
        ⇑(vec 1 (0 : Fin 2)) :=
  by simpa using signOperator_mulVec_vec 1 (0 : Fin 2)

end PauliJordanFourierExamples
