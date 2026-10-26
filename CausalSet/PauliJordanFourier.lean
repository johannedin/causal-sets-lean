/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

public import CausalSet.PauliJordan
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Permutation reduction for finite Pauli--Jordan matrices

This module proves the exact deterministic permutation reduction for finite Pauli--Jordan
matrices.  Coordinate ranks are represented by permutations of `Fin N`; after sorting the first
coordinate, the probability-normalized matrix is a fixed sign operator plus a copy reindexed by
the relative permutation.

It also records the general finite geometric-series identity underlying the Cayley transform.
The explicit twisted-shift realization and its Fourier diagonalization are intentionally left to
a later module.
-/

@[expose] public section

namespace CausalSet.PauliJordan

open Matrix
open scoped BigOperators

/-- The real sign matrix `S`, with `S a b = sign(b - a)`. -/
def signMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun a b => coordinateSign b a

@[simp]
theorem signMatrix_apply (N : ℕ) (a b : Fin N) :
    signMatrix N a b = coordinateSign b a := rfl

/-- The sign matrix is antisymmetric. -/
theorem signMatrix_transpose (N : ℕ) : (signMatrix N)ᵀ = -signMatrix N := by
  ext a b
  simp only [Matrix.transpose_apply, signMatrix_apply, Matrix.neg_apply]
  exact_mod_cast coordinateSign_swap b a

/-- The fixed probability-normalized one-coordinate operator `-i S / (4N)`. -/
noncomputable def signOperator (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  (-Complex.I / (4 * (N : ℂ))) • (signMatrix N).map (algebraMap ℝ ℂ)

@[simp]
theorem signOperator_apply (N : ℕ) (a b : Fin N) :
    signOperator N a b =
      (-Complex.I / (4 * (N : ℂ))) * (coordinateSign b a : ℂ) := by
  rfl

/-- The fixed sign operator is Hermitian. -/
theorem signOperator_isHermitian (N : ℕ) : (signOperator N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  rw [signOperator_apply, signOperator_apply]
  rw [show coordinateSign b a = -coordinateSign a b from coordinateSign_swap a b]
  push_cast
  simp
  ring

/-- Before choosing a sorted coordinate, the normalized matrix is the sum of the two fixed sign
operators pulled back by the two rank permutations. -/
theorem normalizedIPauliJordan_coordinatePrecedes (N : ℕ)
    (u v : Equiv.Perm (Fin N)) :
    normalizedIPauliJordan (coordinatePrecedes u v) =
      Matrix.reindex u.symm u.symm (signOperator N) +
        Matrix.reindex v.symm v.symm (signOperator N) := by
  ext x y
  have hsign :
      (2 : ℂ) * relationSign (coordinatePrecedes u v) x y =
        coordinateSign (u x) (u y) + coordinateSign (v x) (v y) := by
    exact_mod_cast twoOrder_sign_identity u v u.injective v.injective x y
  rw [normalizedIPauliJordan_apply, iPauliJordan_apply_complex]
  simp only [Fintype.card_fin, Matrix.add_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, signOperator_apply]
  rw [show coordinateSign (u y) (u x) = -coordinateSign (u x) (u y) from
      coordinateSign_swap (u x) (u y)]
  rw [show coordinateSign (v y) (v x) = -coordinateSign (v x) (v y) from
      coordinateSign_swap (v x) (v y)]
  push_cast at hsign ⊢
  linear_combination (Complex.I * (N : ℂ)⁻¹ / 4) * hsign

/-- Sorting by `u` leaves a fixed sign operator and a copy indexed by the relative permutation
`v ∘ u⁻¹`.  This is an exact identity of finite matrices. -/
theorem normalizedIPauliJordan_relativePermutation (N : ℕ)
    (u v : Equiv.Perm (Fin N)) :
    Matrix.reindex u u (normalizedIPauliJordan (coordinatePrecedes u v)) =
      signOperator N +
        Matrix.reindex (u.symm.trans v).symm (u.symm.trans v).symm (signOperator N) := by
  ext a b
  rw [normalizedIPauliJordan_coordinatePrecedes]
  simp only [Matrix.reindex_apply, Matrix.add_apply]
  simp

/-- The sign attached to the output coordinate of the antiperiodic cyclic shift. -/
def twistWeight {N : ℕ} (a : Fin N) : ℂ := if a.val = 0 then -1 else 1

/-- The antiperiodic cyclic shift `Z`: it shifts basis vectors forward and changes the sign on
wrapping past the last coordinate. -/
noncomputable def twistedShift (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal twistWeight * ((finRotate N)⁻¹).permMatrix ℂ

/-- Pointwise action of the antiperiodic cyclic shift. -/
theorem twistedShift_mulVec (N : ℕ) (f : Fin N → ℂ) (a : Fin N) :
    (twistedShift N *ᵥ f) a = twistWeight a * f ((finRotate N)⁻¹ a) := by
  classical
  rw [twistedShift, ← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

/-- The shift wraps the last basis coordinate to minus the first. -/
theorem twistedShift_mulVec_zero (n : ℕ) (f : Fin (n + 1) → ℂ) :
    (twistedShift (n + 1) *ᵥ f) 0 = -f (Fin.last n) := by
  rw [twistedShift_mulVec]
  simp only [twistWeight, Fin.val_zero, ite_eq_left, neg_one_mul]
  congr 1

/-- Away from the wrap, the shift reads the immediately preceding coordinate. -/
theorem twistedShift_mulVec_succ (n : ℕ) (f : Fin (n + 1) → ℂ) (a : Fin n) :
    (twistedShift (n + 1) *ᵥ f) a.succ = f a.castSucc := by
  rw [twistedShift_mulVec]
  simp only [twistWeight, Fin.val_succ, Nat.succ_ne_zero, ↓reduceIte, one_mul]
  apply congrArg f
  change (finRotate (n + 1)).symm a.succ = a.castSucc
  apply (finRotate (n + 1)).symm_apply_eq.mpr
  simp

/-- The unnormalized twisted Fourier vector associated to a scalar `ζ`. -/
def twistedFourierVector {N : ℕ} (ζ : ℂ) : Fin N → ℂ :=
  fun a => ζ ^ (a.val + 1)

/-- Every `ζ` with `ζ ^ N = -1` gives an exact eigenvector of the antiperiodic shift, with
eigenvalue `ζ⁻¹`. -/
theorem twistedShift_mulVec_twistedFourierVector (n : ℕ) (ζ : ℂ)
    (hζ : ζ ^ (n + 1) = -1) :
    twistedShift (n + 1) *ᵥ twistedFourierVector ζ =
      ζ⁻¹ • twistedFourierVector ζ := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    subst ζ
    simp at hζ
  funext a
  refine Fin.cases ?_ (fun b => ?_) a
  · rw [twistedShift_mulVec_zero]
    simp [twistedFourierVector, hζ, hζ0]
  · rw [twistedShift_mulVec_succ]
    simp only [twistedFourierVector, Fin.val_castSucc, Fin.val_succ, Pi.smul_apply,
      smul_eq_mul]
    rw [show b.val + 1 + 1 = (b.val + 1) + 1 by omega, pow_succ]
    field_simp
    rw [← pow_add]

section Cayley

variable {A : Type*} [Ring A]

/-- The geometric-series equation needed for the twisted Cayley transform.  In particular, if a
matrix `Z` satisfies `Z ^ N = -1`, then `(1 - Z) * ∑ m < N, Z ^ m = 2`. -/
theorem one_sub_mul_geom_sum_of_pow_eq_neg_one (z : A) (N : ℕ) (hz : z ^ N = -1) :
    (1 - z) * (∑ m ∈ Finset.range N, z ^ m) = 2 := by
  rw [mul_neg_geom_sum, hz]
  rw [sub_neg_eq_add]
  exact one_add_one_eq_two

variable {K : Type*} [Field K]

/-- If `z^N = -1`, the half geometric sum is a right inverse of `1-z`.  Applied to the
twisted cyclic shift, this is the inverse formula in the finite Cayley identity. -/
theorem one_sub_mul_half_geom_sum (z : K) (N : ℕ) (hz : z ^ N = -1) :
    (1 - z) * ((2 : K)⁻¹ * ∑ m ∈ Finset.range N, z ^ m) = (2 : K)⁻¹ * 2 := by
  rw [← mul_assoc]
  rw [show (1 - z) * (2 : K)⁻¹ = (2 : K)⁻¹ * (1 - z) by ring, mul_assoc]
  rw [one_sub_mul_geom_sum_of_pow_eq_neg_one z N hz]

/-- A field-valued form of `one_sub_mul_half_geom_sum`: the displayed geometric sum is a right
inverse of `1-z`. -/
theorem one_sub_mul_twistedShiftInverse (z : K) (N : ℕ)
    (hz : z ^ N = -1) (h2 : (2 : K) ≠ 0) :
    (1 - z) * ((2 : K)⁻¹ * ∑ m ∈ Finset.range N, z ^ m) = 1 := by
  rw [one_sub_mul_half_geom_sum z N hz, inv_mul_cancel₀ h2]

end Cayley

end CausalSet.PauliJordan
