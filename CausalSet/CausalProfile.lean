/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

public import CausalSet.LabelledCorrespondence
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# L² causal profiles and three-label recovery

Strict measurable causal relations on probability spaces give actual real L² profiles
`-α_r 1_past + β_r 1_future`. Their unsquared distances are pseudometric kernels.
The three labels `-1/2, 0, 1/2` recover the two symmetric-difference masses and the
sum of the mixed-cone intersection masses. No ambient topology or geometric
identifiability assertion is made.

The definitions and component identity follow Johan Nedin, *Finite-sample consistency
of joint causal profiles in bounded-density two-dimensional diamonds*, version 1.0,
https://doi.org/10.5281/zenodo.23624630, Sections 1–2. This module formalizes only the
profile algebra, not the paper's geometry, sampling results or reconstruction theorems.
-/

@[expose] public section

open MeasureTheory Set
open Matrix
open scoped ENNReal symmDiff

namespace CausalSet.CausalProfile

variable {X : Type*} [MeasurableSpace X]

/-- A jointly measurable strict transitive relation; no topology or atomlessness is assumed. -/
structure CausalRelation (X : Type*) [MeasurableSpace X] where
  precedes : X → X → Prop
  irrefl : ∀ x, ¬ precedes x x
  trans : ∀ {x y z}, precedes x y → precedes y z → precedes x z
  measurable : MeasurableSet {p : X × X | precedes p.1 p.2}

namespace CausalRelation

def past (R : CausalRelation X) (x : X) : Set X := {z | R.precedes z x}
def future (R : CausalRelation X) (x : X) : Set X := {z | R.precedes x z}

theorem measurable_past (R : CausalRelation X) (x : X) : MeasurableSet (R.past x) :=
  R.measurable.preimage (measurable_id.prodMk measurable_const)

theorem measurable_future (R : CausalRelation X) (x : X) : MeasurableSet (R.future x) :=
  R.measurable.preimage (measurable_const.prodMk measurable_id)

theorem past_inter_future (R : CausalRelation X) (x : X) : R.past x ∩ R.future x = ∅ := by
  ext z
  simp only [mem_inter_iff, past, future, mem_ofPred_eq, mem_empty_iff_false, iff_false,
    not_and]
  intro hzx hxz
  exact R.irrefl z (R.trans hzx hxz)

end CausalRelation

variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- The indicator as an a.e.-equivalence class, using mathlib's actual L² construction. -/
noncomputable def indicator (s : Set X) (hs : MeasurableSet s) : Lp ℝ 2 μ :=
  indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)

theorem indicator_ae (s : Set X) (hs : MeasurableSet s) :
    ⇑(indicator μ s hs) =ᵐ[μ] s.indicator (fun _ => (1 : ℝ)) :=
  indicatorConstLp_coeFn

theorem inner_indicator (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    inner ℝ (indicator μ s hs) (indicator μ t ht) = μ.real (s ∩ t) := by
  exact L2.real_inner_indicatorConstLp_one_indicatorConstLp_one hs ht

theorem norm_indicator_sub_sq (s t : Set X) (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    ‖indicator μ s hs - indicator μ t ht‖ ^ 2 = μ.real (s ∆ t) := by
  rw [← dist_eq_norm, indicator, indicator, dist_indicatorConstLp_eq_norm,
    norm_indicatorConstLp (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  norm_num only [norm_one, one_mul, ENNReal.toReal_ofNat]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (measureReal_nonneg)]

variable (R : CausalRelation X)

noncomputable def pastIndicator (x : X) : Lp ℝ 2 μ :=
  indicator μ (R.past x) (R.measurable_past x)

noncomputable def futureIndicator (x : X) : Lp ℝ 2 μ :=
  indicator μ (R.future x) (R.measurable_future x)

noncomputable def alpha (r : ℝ) : ℝ := (1-r)/2
noncomputable def beta (r : ℝ) : ℝ := (1+r)/2

/-- The sign convention is minus past, plus future. Scalars may be arbitrary real labels. -/
noncomputable def profile (r : ℝ) (x : X) : Lp ℝ 2 μ :=
  (-alpha r) • pastIndicator μ R x + beta r • futureIndicator μ R x

theorem profile_ae (r : ℝ) (x : X) :
    ⇑(profile μ R r x) =ᵐ[μ] fun z =>
      (-alpha r) * (R.past x).indicator (fun _ => (1 : ℝ)) z +
        beta r * (R.future x).indicator (fun _ => (1 : ℝ)) z := by
  unfold profile
  filter_upwards [Lp.coeFn_add ((-alpha r) • pastIndicator μ R x)
      (beta r • futureIndicator μ R x),
    Lp.coeFn_smul (-alpha r) (pastIndicator μ R x),
    Lp.coeFn_smul (beta r) (futureIndicator μ R x),
    indicator_ae μ (R.past x) (R.measurable_past x),
    indicator_ae μ (R.future x) (R.measurable_future x)] with z hadd hp hf hpx hfx
  rw [hadd]
  change ((-alpha r) • pastIndicator μ R x) z +
    (beta r • futureIndicator μ R x) z = _
  rw [hp, hf]
  change (-alpha r) * indicator μ (R.past x) (R.measurable_past x) z +
    beta r * indicator μ (R.future x) (R.measurable_future x) z = _
  rw [hpx, hfx]

/-- Past symmetric-difference mass, identified below with the squared L² difference. -/
def componentA (x y : X) : ℝ := μ.real (R.past x ∆ R.past y)
/-- Future symmetric-difference mass. -/
def componentB (x y : X) : ℝ := μ.real (R.future x ∆ R.future y)
/-- Mixed-cone mass sum; it is the negative, not positive, inner product of differences. -/
def componentC (x y : X) : ℝ :=
  μ.real (R.past x ∩ R.future y) + μ.real (R.future x ∩ R.past y)

theorem componentA_eq (x y : X) :
    componentA μ R x y = ‖pastIndicator μ R x - pastIndicator μ R y‖ ^ 2 :=
  (norm_indicator_sub_sq μ _ _ (R.measurable_past x) (R.measurable_past y)).symm

theorem componentB_eq (x y : X) :
    componentB μ R x y = ‖futureIndicator μ R x - futureIndicator μ R y‖ ^ 2 :=
  (norm_indicator_sub_sq μ _ _ (R.measurable_future x) (R.measurable_future y)).symm

theorem componentC_eq (x y : X) :
    componentC μ R x y =
      -inner ℝ (pastIndicator μ R x - pastIndicator μ R y)
        (futureIndicator μ R x - futureIndicator μ R y) := by
  simp only [inner_sub_left, inner_sub_right, pastIndicator, futureIndicator, inner_indicator,
    R.past_inter_future, measureReal_empty, sub_zero, zero_sub, componentC]
  rw [inter_comm (R.past y) (R.future x)]
  ring

/-- General Hilbert-space identity, subsequently instantiated with the actual indicators. -/
theorem quadratic_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : ℝ) (u v : E) :
    ‖(-a) • u + b • v‖ ^ 2 =
      a^2 * ‖u‖^2 + b^2 * ‖v‖^2 + 2*a*b*(-inner ℝ u v) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm v u]
  simp only [real_inner_self_eq_norm_sq]
  ring

noncomputable def profileDistance (r : ℝ) (x y : X) : ℝ :=
  dist (profile μ R r x) (profile μ R r y)

theorem profileDistance_sq (r : ℝ) (x y : X) :
    profileDistance μ R r x y ^ 2 =
      alpha r ^ 2 * componentA μ R x y + beta r ^ 2 * componentB μ R x y +
        2 * alpha r * beta r * componentC μ R x y := by
  rw [profileDistance, dist_eq_norm]
  have h : profile μ R r x - profile μ R r y =
      (-alpha r) • (pastIndicator μ R x - pastIndicator μ R y) +
        beta r • (futureIndicator μ R x - futureIndicator μ R y) := by
    simp only [profile, smul_sub]
    abel
  rw [h, quadratic_identity, componentA_eq, componentB_eq, componentC_eq]

/-- The three labels in the source's stated order. -/
noncomputable def label : Fin 3 → ℝ := ![-(1/2), 0, 1/2]

/-- Rows correspond to labels; columns to A, B, C. -/
noncomputable def coefficientMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![9/16, 1/16, 6/16; 4/16, 4/16, 8/16; 1/16, 9/16, 6/16]

def recoveryMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![3, -3, 1; 1, -3, 3; -2, 5, -2]

theorem coefficientMatrix_det : coefficientMatrix.det = -(1/16) := by
  norm_num [coefficientMatrix, Matrix.det_fin_three]

theorem recovery_mul_coefficient : recoveryMatrix * coefficientMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [recoveryMatrix, coefficientMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem coefficient_mul_recovery : coefficientMatrix * recoveryMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [recoveryMatrix, coefficientMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem coefficientMatrix_isUnit : IsUnit coefficientMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det, coefficientMatrix_det]
  norm_num

/-- Reusable simultaneous recovery, not three assumed scalar formulas. -/
theorem recover_vector (v : Fin 3 → ℝ) :
    recoveryMatrix *ᵥ (coefficientMatrix *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, recovery_mul_coefficient, Matrix.one_mulVec]

theorem coefficient_mulVec_injective :
    Function.Injective (fun v : Fin 3 → ℝ => coefficientMatrix *ᵥ v) :=
  Function.LeftInverse.injective recover_vector

noncomputable def components (x y : X) : Fin 3 → ℝ :=
  ![componentA μ R x y, componentB μ R x y, componentC μ R x y]

/-- Observations are squares of genuine unsquared profile distances. -/
noncomputable def observedSquared (x y : X) : Fin 3 → ℝ :=
  fun i => profileDistance μ R (label i) x y ^ 2

theorem observedSquared_eq (x y : X) :
    observedSquared μ R x y = coefficientMatrix *ᵥ components μ R x y := by
  ext i
  fin_cases i <;>
    norm_num [observedSquared, profileDistance_sq, label, alpha, beta, coefficientMatrix,
      components, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- The source's simultaneous three-label recovery of all three measure components. -/
theorem three_label_recovery (x y : X) :
    recoveryMatrix *ᵥ observedSquared μ R x y = components μ R x y := by
  rw [observedSquared_eq, recover_vector]

theorem observations_characterize (x y : X) (v : Fin 3 → ℝ) :
    observedSquared μ R x y = coefficientMatrix *ᵥ v ↔ components μ R x y = v := by
  rw [observedSquared_eq]
  exact coefficient_mulVec_injective.eq_iff

/-- Equality of the three observations is exactly equality of the three components,
even for pairs in different probability spaces. -/
theorem observations_eq_iff_components {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (S : CausalRelation Y)
    (x y : X) (u v : Y) :
    observedSquared μ R x y = observedSquared ν S u v ↔
      components μ R x y = components ν S u v := by
  rw [observedSquared_eq, observedSquared_eq]
  exact coefficient_mulVec_injective.eq_iff

theorem recover_A (x y : X) :
    componentA μ R x y = 3 * observedSquared μ R x y 0 -
      3 * observedSquared μ R x y 1 + observedSquared μ R x y 2 := by
  have h := congrFun (three_label_recovery μ R x y).symm (0 : Fin 3)
  simpa [components, recoveryMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    sub_eq_add_neg, add_assoc] using h

theorem recover_B (x y : X) :
    componentB μ R x y = observedSquared μ R x y 0 -
      3 * observedSquared μ R x y 1 + 3 * observedSquared μ R x y 2 := by
  have h := congrFun (three_label_recovery μ R x y).symm (1 : Fin 3)
  simpa [components, recoveryMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    sub_eq_add_neg, add_assoc] using h

theorem recover_C (x y : X) :
    componentC μ R x y = -2 * observedSquared μ R x y 0 +
      5 * observedSquared μ R x y 1 - 2 * observedSquared μ R x y 2 := by
  have h := congrFun (three_label_recovery μ R x y).symm (2 : Fin 3)
  simpa [components, recoveryMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    sub_eq_add_neg, add_assoc] using h

/-- Pull back the L² distance, never its square. No topology on X is installed. -/
noncomputable def profileKernel (r : ℝ) : PseudoMetric X ℝ where
  toFun := profileDistance μ R r
  refl' _ := dist_self _
  symm' _ _ := dist_comm _ _
  triangle' _ _ _ := dist_triangle _ _ _

theorem profileDistance_nonneg (r : ℝ) (x y : X) : 0 ≤ profileDistance μ R r x y :=
  dist_nonneg

@[simp] theorem profileDistance_self (r : ℝ) (x : X) : profileDistance μ R r x x = 0 :=
  dist_self _

theorem profileDistance_symm (r : ℝ) (x y : X) :
    profileDistance μ R r x y = profileDistance μ R r y x := dist_comm _ _

theorem profileDistance_triangle (r : ℝ) (x y z : X) :
    profileDistance μ R r x z ≤ profileDistance μ R r x y + profileDistance μ R r y z :=
  dist_triangle _ _ _

noncomputable def kernels : LabelledCorrespondence.KernelFamily (Fin 3) X :=
  fun i => profileKernel μ R (label i)

@[simp] theorem kernels_apply (i : Fin 3) (x y : X) :
    kernels μ R i x y = profileDistance μ R (label i) x y := rfl

end CausalSet.CausalProfile
