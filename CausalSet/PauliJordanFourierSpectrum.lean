/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

public import CausalSet.PauliJordanFourier
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact antiperiodic Fourier spectrum of the finite sign matrix

This module constructs the concrete half-integer Fourier roots of the antiperiodic cyclic shift,
proves that their normalized Fourier vectors form an orthonormal basis, and diagonalizes both the
shift and the finite sign matrix in that basis.  It then proves the finite geometric-sum and
corrected Cayley identities and obtains the exact cotangent eigenvalues of the normalized sign
operator.

The Fourier construction is finite-dimensional and deterministic.  It introduces no probability
or asymptotic assumptions.
-/

@[expose] public section

open scoped ComplexConjugate

namespace CausalSet.PauliJordan.AntiperiodicFourier

open Matrix
open scoped BigOperators

noncomputable def angle (n : ℕ) (k : Fin (n+1)) : ℝ :=
  Real.pi * (2 * k.val + 1) / (n+1)

noncomputable def root (n : ℕ) (k : Fin (n+1)) : ℂ :=
  Complex.exp ((angle n k : ℂ) * Complex.I)

theorem root_pow (n : ℕ) (k : Fin (n+1)) : root n k ^ (n+1) = -1 := by
  rw [root, angle, ← Complex.exp_nat_mul]
  rw [show ((n + 1 : ℕ) : ℂ) *
      (↑(Real.pi * (2 * k.val + 1) / (n + 1)) * Complex.I) =
      ((2 * k.val + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) by
    push_cast
    field_simp]
  rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  rw [pow_add, pow_mul]
  simp

theorem angle_mem (n : ℕ) (k : Fin (n+1)) : angle n k ∈ Set.Ioc 0 (2 * Real.pi) := by
  unfold angle
  constructor
  · exact div_pos (mul_pos Real.pi_pos (by positivity)) (by positivity)
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)]
    have hk : 2 * k.val + 1 ≤ 2 * (n + 1) := by omega
    calc
      Real.pi * (2 * k.val + 1) ≤ Real.pi * (2 * (n + 1)) := by
        apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
        exact_mod_cast hk
      _ = 2 * Real.pi * (n + 1) := by ring

theorem root_injective (n : ℕ) : Function.Injective (root n) := by
  intro k l h
  apply Fin.ext
  have hc : Circle.exp (angle n k) = Circle.exp (angle n l) := by
    apply Subtype.ext
    exact h
  have ha := Circle.exp_injOn_Ioc (a := 0) (b := 2 * Real.pi) (by linarith [Real.pi_pos])
      (angle_mem n k) (angle_mem n l) hc
  dsimp [angle] at ha
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp at ha
  norm_cast at ha
  omega

theorem conj_root (n : ℕ) (k : Fin (n+1)) : conj (root n k) = (root n k)⁻¹ := by
  rw [root, ← Complex.exp_conj]
  rw [show conj ((angle n k : ℂ) * Complex.I) = -((angle n k : ℂ) * Complex.I) by simp]
  exact Complex.exp_neg _

theorem root_ne_zero (n : ℕ) (k : Fin (n+1)) : root n k ≠ 0 :=
  Complex.exp_ne_zero _

theorem root_div_pow (n : ℕ) (k l : Fin (n+1)) :
    (root n k / root n l) ^ (n+1) = 1 := by
  rw [div_pow, root_pow, root_pow]
  simp

theorem sum_root_div_pow (n : ℕ) (k l : Fin (n+1)) (hkl : k ≠ l) :
    ∑ a : Fin (n+1), (root n k / root n l) ^ a.val = 0 := by
  rw [Fin.sum_univ_eq_sum_range]
  let r := root n k / root n l
  have hrpow : r ^ (n+1) = 1 := root_div_pow n k l
  have hrne : r ≠ 1 := by
    intro h
    have : root n k = root n l := (div_eq_one_iff_eq (root_ne_zero n l)).mp h
    exact hkl (root_injective n this)
  have hgeom := geom_sum_mul r (n+1)
  rw [hrpow, sub_self] at hgeom
  exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hrne)

noncomputable def vec (n : ℕ) (k : Fin (n+1)) : EuclideanSpace ℂ (Fin (n+1)) :=
  WithLp.toLp 2 (fun a => (((Real.sqrt (n+1))⁻¹ : ℝ) : ℂ) * root n k ^ (a.val + 1))

theorem inner_vec (n : ℕ) (k l : Fin (n+1)) :
    inner ℂ (vec n k) (vec n l) = if k = l then 1 else 0 := by
  rw [PiLp.inner_apply]
  simp only [vec, RCLike.inner_apply]
  simp_rw [map_mul, map_pow, conj_root]
  simp_rw [show (starRingEnd ℂ) (↑(Real.sqrt (n + 1))⁻¹ : ℂ) =
      (↑(Real.sqrt (n + 1))⁻¹ : ℂ) by
    exact Complex.conj_ofReal _]
  simp_rw [show ∀ x y : ℂ,
      (↑(Real.sqrt (n + 1))⁻¹ : ℂ) * x * ((↑(Real.sqrt (n + 1))⁻¹ : ℂ) * y) =
        ((↑(Real.sqrt (n + 1))⁻¹ : ℂ) * (↑(Real.sqrt (n + 1))⁻¹ : ℂ)) * (x * y) by
    intro x y
    ring]
  rw [← Finset.mul_sum]
  split_ifs with hkl
  · subst l
    have hsqrt : Real.sqrt (n + 1) ≠ 0 := by positivity
    simp only [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (root_ne_zero n k)),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [← Complex.ofReal_mul]
    norm_cast
    rw [← mul_inv, ← sq, Real.sq_sqrt (Nat.cast_nonneg (n + 1))]
    field_simp
  ·
    rw [show ∑ x : Fin (n + 1),
        root n l ^ (x.val + 1) * (root n k)⁻¹ ^ (x.val + 1) =
        (root n l / root n k) *
          ∑ x : Fin (n + 1), (root n l / root n k) ^ x.val by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [← mul_pow, div_eq_mul_inv, pow_succ']]
    rw [sum_root_div_pow n l k (Ne.symm hkl), mul_zero, mul_zero]

theorem orthonormal_vec (n : ℕ) : Orthonormal ℂ (vec n) := by
  rw [orthonormal_iff_ite]
  exact inner_vec n

noncomputable def basis (n : ℕ) :
    OrthonormalBasis (Fin (n+1)) ℂ (EuclideanSpace ℂ (Fin (n+1))) :=
  OrthonormalBasis.mk (orthonormal_vec n)
    ((orthonormal_vec n).linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge

@[simp] theorem basis_apply (n : ℕ) (k : Fin (n+1)) : basis n k = vec n k := by
  simp [basis]

theorem shift_vec (n : ℕ) (k : Fin (n+1)) :
    twistedShift (n+1) *ᵥ ⇑(vec n k) = (root n k)⁻¹ • ⇑(vec n k) := by
  rw [show ⇑(vec n k) =
      (((Real.sqrt (n+1))⁻¹ : ℂ) • twistedFourierVector (root n k)) by
    funext a
    simp [vec, twistedFourierVector]]
  rw [Matrix.mulVec_smul, twistedShift_mulVec_twistedFourierVector n (root n k) (root_pow n k)]
  simp [smul_smul, mul_comm]

theorem shift_pow_vec (n m : ℕ) (k : Fin (n+1)) :
    twistedShift (n+1) ^ m *ᵥ ⇑(vec n k) = ((root n k)⁻¹ ^ m) • ⇑(vec n k) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, shift_vec]
      simp only [pow_succ', smul_smul]
      rw [mul_comm]

theorem shift_pow_antiperiodic (n : ℕ) :
    twistedShift (n+1) ^ (n+1) = -(1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) := by
  apply Matrix.toEuclideanLin.injective
  apply (basis n).toBasis.ext
  intro k
  simp only [OrthonormalBasis.coe_toBasis, basis_apply, Matrix.toLpLin_apply]
  change WithLp.toLp 2 (twistedShift (n + 1) ^ (n + 1) *ᵥ ⇑(vec n k)) =
    WithLp.toLp 2 ((-1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) *ᵥ ⇑(vec n k))
  rw [shift_pow_vec]
  rw [Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [inv_pow, root_pow]
  simp

theorem sign_row_zero (n : ℕ) (f : Fin (n+1) → ℂ) :
    ((signMatrix (n+1)).map (algebraMap ℝ ℂ) *ᵥ f) 0 = ∑ b : Fin n, f b.succ := by
  classical
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, signMatrix, coordinateSign]

theorem sign_entry_succ (n : ℕ) (a : Fin n) (b : Fin (n+1)) :
    signMatrix (n+1) a.succ b = signMatrix (n+1) a.castSucc b -
      (if b.val = a.val then 1 else 0) - (if b.val = a.val + 1 then 1 else 0) := by
  change (coordinateSign b a.succ : ℝ) = (coordinateSign b a.castSucc : ℝ) -
      (if b.val = a.val then 1 else 0) - (if b.val = a.val + 1 then 1 else 0)
  have h : coordinateSign b a.succ = coordinateSign b a.castSucc -
      (if b.val = a.val then 1 else 0) - (if b.val = a.val + 1 then 1 else 0) := by
    change (if a.val + 1 < b.val then 1 else if b.val < a.val + 1 then -1 else 0) =
      (if a.val < b.val then 1 else if b.val < a.val then -1 else 0) -
        (if b.val = a.val then 1 else 0) - (if b.val = a.val + 1 then 1 else 0)
    split_ifs <;> norm_num at * <;> omega
  exact_mod_cast h

theorem sign_row_succ (n : ℕ) (f : Fin (n+1) → ℂ) (a : Fin n) :
    ((signMatrix (n+1)).map (algebraMap ℝ ℂ) *ᵥ f) a.succ =
      ((signMatrix (n+1)).map (algebraMap ℝ ℂ) *ᵥ f) a.castSucc -
        f a.castSucc - f a.succ := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  have he (b : Fin (n + 1)) :
      algebraMap ℝ ℂ (signMatrix (n+1) a.succ b) =
        algebraMap ℝ ℂ (signMatrix (n+1) a.castSucc b) -
          (if b.val = a.val then 1 else 0) -
          (if b.val = a.val + 1 then 1 else 0) := by
    rw [sign_entry_succ]
    push_cast
    split_ifs <;> norm_num
  simp_rw [he]
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [show (∑ x : Fin (n + 1), (if x.val = a.val then (1 : ℂ) else 0) * f x) =
      f a.castSucc by
    rw [Finset.sum_eq_single a.castSucc]
    · simp
    · intro b _ hb
      have hval : b.val ≠ a.val := by
        intro h
        apply hb
        exact Fin.ext h
      simp [hval]
    · simp]
  rw [show (∑ x : Fin (n + 1), (if x.val = a.val + 1 then (1 : ℂ) else 0) * f x) =
      f a.succ by
    rw [Finset.sum_eq_single a.succ]
    · simp
    · intro b _ hb
      have hval : b.val ≠ a.val + 1 := by
        intro h
        apply hb
        exact Fin.ext h
      simp [hval]
    · simp]

noncomputable def eig (n : ℕ) (k : Fin (n+1)) : ℂ :=
  ∑ m ∈ Finset.range n, root n k ^ (m + 1)

theorem root_ne_one (n : ℕ) (k : Fin (n+1)) : root n k ≠ 1 := by
  intro h
  have hp := root_pow n k
  rw [h, one_pow] at hp
  norm_num at hp

theorem eig_eq_ratio (n : ℕ) (k : Fin (n+1)) :
    eig n k = (1 + root n k) / (1 - root n k) := by
  let r := root n k
  have hr : r ≠ 1 := root_ne_one n k
  have hgeom := CausalSet.PauliJordan.one_sub_mul_geom_sum_of_pow_eq_neg_one
    r (n+1) (root_pow n k)
  rw [Finset.sum_range_succ'] at hgeom
  change (1 - r) * (eig n k + 1) = 2 at hgeom
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hr))).2
  calc
    eig n k * (1 - r) = (1 - r) * (eig n k + 1) - (1 - r) := by ring
    _ = 2 - (1 - r) := by rw [hgeom]
    _ = 1 + r := by ring

theorem eig_recurrence (n : ℕ) (k : Fin (n+1)) :
    eig n k * root n k = eig n k - 1 - root n k := by
  rw [eig_eq_ratio]
  field_simp [sub_ne_zero.mpr (Ne.symm (root_ne_one n k))]
  ring

theorem sign_mulVec_vec (n : ℕ) (k : Fin (n+1)) :
    (signMatrix (n+1)).map (algebraMap ℝ ℂ) *ᵥ ⇑(vec n k) =
      eig n k • ⇑(vec n k) := by
  funext a
  refine Fin.induction ?_ ?_ a
  · rw [sign_row_zero]
    simp only [vec, Fin.val_succ, Pi.smul_apply, smul_eq_mul, Fin.val_zero]
    rw [← Finset.mul_sum]
    simp_rw [show ∀ m : ℕ, m + 1 + 1 = m + 2 by omega]
    simp only [zero_add, pow_one]
    change (↑(Real.sqrt (n + 1))⁻¹ : ℂ) *
        (∑ b : Fin n, root n k ^ (b.val + 2)) =
      eig n k * ((↑(Real.sqrt (n + 1))⁻¹ : ℂ) * root n k)
    have hsum : (∑ b : Fin n, root n k ^ (b.val + 2)) =
        ∑ m ∈ Finset.range n, root n k ^ (m + 2) :=
      Fin.sum_univ_eq_sum_range (fun m => root n k ^ (m + 2)) n
    rw [hsum]
    change (↑(Real.sqrt (n + 1))⁻¹ : ℂ) *
        (∑ m ∈ Finset.range n, root n k ^ (m + 2)) =
      eig n k * ((↑(Real.sqrt (n + 1))⁻¹ : ℂ) * root n k)
    simp only [eig]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
    ring
  · intro a ih
    rw [sign_row_succ]
    rw [ih]
    have hv : ⇑(vec n k) a.succ = root n k * ⇑(vec n k) a.castSucc := by
      simp only [vec, Fin.val_succ, Fin.val_castSucc]
      rw [show a.val + 1 + 1 = (a.val + 1) + 1 by omega, pow_succ]
      ring
    simp_rw [hv]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      eig n k * ⇑(vec n k) a.castSucc - ⇑(vec n k) a.castSucc -
          root n k * ⇑(vec n k) a.castSucc =
          (eig n k - 1 - root n k) * ⇑(vec n k) a.castSucc := by ring
      _ = (eig n k * root n k) * ⇑(vec n k) a.castSucc := by rw [eig_recurrence]
      _ = eig n k * (root n k * ⇑(vec n k) a.castSucc) := by ring
      _ = eig n k * ⇑(vec n k) a.succ := by rw [hv]

noncomputable def invEig (n : ℕ) (k : Fin (n+1)) : ℂ :=
  ∑ m ∈ Finset.range n, (root n k)⁻¹ ^ (m + 1)

theorem inv_root_pow (n : ℕ) (k : Fin (n+1)) :
    (root n k)⁻¹ ^ (n+1) = -1 := by
  rw [inv_pow, root_pow]
  simp

theorem invEig_eq_ratio (n : ℕ) (k : Fin (n+1)) :
    invEig n k = (1 + (root n k)⁻¹) / (1 - (root n k)⁻¹) := by
  let r := (root n k)⁻¹
  have hr : r ≠ 1 := inv_ne_one.mpr (root_ne_one n k)
  have hgeom := CausalSet.PauliJordan.one_sub_mul_geom_sum_of_pow_eq_neg_one
    r (n+1) (inv_root_pow n k)
  rw [Finset.sum_range_succ'] at hgeom
  change (1 - r) * (invEig n k + 1) = 2 at hgeom
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hr))).2
  calc
    invEig n k * (1 - r) = (1 - r) * (invEig n k + 1) - (1 - r) := by ring
    _ = 2 - (1 - r) := by rw [hgeom]
    _ = 1 + r := by ring

theorem neg_invEig_eq_eig (n : ℕ) (k : Fin (n+1)) :
    -invEig n k = eig n k := by
  rw [invEig_eq_ratio, eig_eq_ratio]
  have h₁ : 1 - root n k ≠ 0 := sub_ne_zero.mpr (Ne.symm (root_ne_one n k))
  have h₂ : 1 - (root n k)⁻¹ ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (inv_ne_one.mpr (root_ne_one n k)))
  have h₃ : root n k - 1 ≠ 0 := sub_ne_zero.mpr (root_ne_one n k)
  field_simp [h₁, h₂, h₃, root_ne_zero]
  ring

theorem signMatrix_eq_neg_sum_shift (n : ℕ) :
    (signMatrix (n+1)).map (algebraMap ℝ ℂ) =
      -∑ m ∈ Finset.range n, twistedShift (n+1) ^ (m+1) := by
  apply Matrix.toEuclideanLin.injective
  apply (basis n).toBasis.ext
  intro k
  simp only [OrthonormalBasis.coe_toBasis, basis_apply, Matrix.toLpLin_apply]
  rw [sign_mulVec_vec]
  simp only [Matrix.neg_mulVec, Matrix.sum_mulVec]
  simp_rw [shift_pow_vec]
  apply congrArg (WithLp.toLp 2)
  funext a
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.neg_apply]
  rw [← Finset.sum_mul]
  change eig n k * ⇑(vec n k) a = -(invEig n k * ⇑(vec n k) a)
  rw [show -(invEig n k * ⇑(vec n k) a) =
      (-invEig n k) * ⇑(vec n k) a by ring, neg_invEig_eq_eig]

theorem exp_half_angle (n : ℕ) (k : Fin (n+1)) :
    Complex.exp (2 * Complex.I * ((angle n k : ℂ) / 2)) = root n k := by
  rw [root]
  congr 1
  ring

theorem eig_eq_I_mul_cot (n : ℕ) (k : Fin (n+1)) :
    eig n k = Complex.I * Complex.cot ((angle n k : ℂ) / 2) := by
  rw [Complex.cot_eq_exp_ratio, exp_half_angle, eig_eq_ratio]
  have h : 1 - root n k ≠ 0 := sub_ne_zero.mpr (Ne.symm (root_ne_one n k))
  field_simp [h]
  ring

theorem signOperator_mulVec_vec (n : ℕ) (k : Fin (n+1)) :
    signOperator (n+1) *ᵥ ⇑(vec n k) =
      (Complex.cot ((angle n k : ℂ) / 2) / (4 * (n+1 : ℂ))) • ⇑(vec n k) := by
  rw [signOperator, Matrix.smul_mulVec, sign_mulVec_vec, eig_eq_I_mul_cot]
  ext a
  simp only [Pi.smul_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  have hn : (1 + (n : ℂ)) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    have hp : (0 : ℝ) < 1 + n := by positivity
    linarith
  field_simp [hn]
  push_cast
  ring

noncomputable def shiftInverse (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  (2 : ℂ)⁻¹ • ∑ m ∈ Finset.range (n+1), twistedShift (n+1) ^ m

theorem one_sub_shift_mul_shiftInverse (n : ℕ) :
    (1 - twistedShift (n+1)) * shiftInverse n = 1 := by
  rw [shiftInverse, Matrix.mul_smul]
  rw [CausalSet.PauliJordan.one_sub_mul_geom_sum_of_pow_eq_neg_one]
  · rw [show (2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) =
        (2 : ℂ) • 1 by
      calc
        (2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) = 2 • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :=
          (Nat.smul_one_eq_cast 2).symm
        _ = (2 : ℂ) • 1 := (Nat.cast_smul_eq_nsmul ℂ 2 1).symm]
    rw [smul_smul]
    norm_num
  · exact shift_pow_antiperiodic n

theorem shiftInverse_mul_one_sub_shift (n : ℕ) :
    shiftInverse n * (1 - twistedShift (n+1)) = 1 := by
  rw [shiftInverse, Matrix.smul_mul]
  rw [geom_sum_mul_neg, shift_pow_antiperiodic]
  rw [show (1 - (-1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) =
      (2 : ℂ) • 1 by
    rw [sub_neg_eq_add, one_add_one_eq_two]
    calc
      (2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) = 2 • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :=
        (Nat.smul_one_eq_cast 2).symm
      _ = (2 : ℂ) • 1 := (Nat.cast_smul_eq_nsmul ℂ 2 1).symm]
  rw [smul_smul]
  norm_num

theorem one_add_shift_mul_shiftInverse (n : ℕ) :
    (1 + twistedShift (n+1)) * shiftInverse n =
      ∑ m ∈ Finset.range n, twistedShift (n+1) ^ (m+1) := by
  let Z := twistedShift (n+1)
  let G := ∑ m ∈ Finset.range (n+1), Z ^ m
  let T := ∑ m ∈ Finset.range n, Z ^ (m+1)
  have hgeom : (1 - Z) * G = 2 := by
    exact CausalSet.PauliJordan.one_sub_mul_geom_sum_of_pow_eq_neg_one
      Z (n+1) (shift_pow_antiperiodic n)
  have hsplit : G = T + 1 := by
    dsimp [G, T]
    rw [Finset.sum_range_succ']
    simp
  have hprod : (1 + Z) * G = T + T := by
    rw [hsplit] at hgeom ⊢
    rw [← one_add_one_eq_two] at hgeom
    have hz : Z * T + Z = T - 1 := by
      have hcanon : T + 1 - (Z * T + Z) = 1 + 1 := by
        calc
          T + 1 - (Z * T + Z) = (1 - Z) * (T + 1) := by noncomm_ring
          _ = 1 + 1 := hgeom
      have h' : T + 1 = (1 + 1) + (Z * T + Z) := sub_eq_iff_eq_add.mp hcanon
      have hh : 1 + T = 1 + ((Z * T + Z) + 1) := by
        simpa [add_assoc, add_comm, add_left_comm] using h'
      exact eq_sub_of_add_eq (add_left_cancel hh).symm
    calc
      (1 + Z) * (T + 1) = T + 1 + (Z * T + Z) := by
        simp only [add_mul, one_mul, mul_add, mul_one]
        abel
      _ = T + 1 + (T - 1) := by rw [hz]
      _ = T + T := by abel
  rw [shiftInverse]
  change (1 + Z) * ((2 : ℂ)⁻¹ • G) = T
  rw [Matrix.mul_smul, hprod]
  ext a b
  simp only [Matrix.smul_apply, Matrix.add_apply]
  ring

theorem signMatrix_cayley (n : ℕ) :
    (signMatrix (n+1)).map (algebraMap ℝ ℂ) =
      -((1 + twistedShift (n+1)) * shiftInverse n) := by
  rw [signMatrix_eq_neg_sum_shift, one_add_shift_mul_shiftInverse]

end CausalSet.PauliJordan.AntiperiodicFourier
