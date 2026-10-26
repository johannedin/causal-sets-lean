/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

public import CausalSet.RandomTwoOrder
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Finite Pauli--Jordan matrices for two-orders

This module formalizes the finite, deterministic foundations of the massless two-dimensional
Pauli--Jordan operator.  It separates the generic construction from the special coordinatewise
order:

* `relationSign r x y` is the signed antisymmetrization of a decidable relation;
* `pauliJordan r` is the real matrix with entries `relationSign / 2`;
* `iPauliJordan r` is its Hermitian complex multiple by `Complex.I`;
* `normalizedIPauliJordan r` is the exact probability normalization by the cardinality;
* `twoOrder_sign_identity` is the finite causal-precedence sign identity.

No probability law, continuum operator, eigenvalue approximation, or physical truncation claim is
made here.
-/

@[expose] public section

namespace CausalSet

open Matrix

namespace PauliJordan

variable {ι κ α β : Type*}

/-- Signed antisymmetrization of a decidable relation.  It is `1` when only `r y x` holds,
`-1` when only `r x y` holds, and `0` otherwise. -/
def relationSign (r : ι → ι → Prop) [DecidableRel r] (x y : ι) : ℤ :=
  (if r y x then 1 else 0) - if r x y then 1 else 0

@[simp]
theorem relationSign_self (r : ι → ι → Prop) [DecidableRel r] (x : ι) :
    relationSign r x x = 0 := by
  simp [relationSign]

theorem relationSign_swap (r : ι → ι → Prop) [DecidableRel r] (x y : ι) :
    relationSign r y x = -relationSign r x y := by
  simp only [relationSign]
  omega

/-- Strict coordinatewise causal precedence. -/
def coordinatePrecedes [LT α] [LT β] (u : ι → α) (v : ι → β) (x y : ι) : Prop :=
  u x < u y ∧ v x < v y

instance [LT α] [LT β] [DecidableLT α] [DecidableLT β] (u : ι → α) (v : ι → β) :
    DecidableRel (coordinatePrecedes u v) := by
  intro x y
  unfold coordinatePrecedes
  infer_instance

/-- The sign of `a - b`, defined without additive structure on the coordinate type. -/
def coordinateSign [LT α] [DecidableLT α] (a b : α) : ℤ :=
  if b < a then 1 else if a < b then -1 else 0

@[simp]
theorem coordinateSign_self [LinearOrder α] (a : α) : coordinateSign a a = 0 := by
  simp [coordinateSign]

theorem coordinateSign_swap [LinearOrder α] (a b : α) :
    coordinateSign b a = -coordinateSign a b := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · simp [coordinateSign, hab, not_lt_of_ge hab.le]
  · simp [coordinateSign]
  · simp [coordinateSign, hba, not_lt_of_ge hba.le]

/-- Twice the causal-precedence sign is the sum of the two coordinate signs.  Injectivity is the
no-ties hypothesis.  The identity is stated in division-free form. -/
theorem twoOrder_sign_identity [LinearOrder α] [LinearOrder β]
    (u : ι → α) (v : ι → β) (hu : Function.Injective u) (hv : Function.Injective v)
    (x y : ι) :
    2 * relationSign (coordinatePrecedes u v) x y =
      coordinateSign (u x) (u y) + coordinateSign (v x) (v y) := by
  by_cases hxy : x = y
  · subst y
    simp
  have hune : u x ≠ u y := hu.ne hxy
  have hvne : v x ≠ v y := hv.ne hxy
  rcases lt_or_gt_of_ne hune with huLt | huGt
  · rcases lt_or_gt_of_ne hvne with hvLt | hvGt
    · simp [relationSign, coordinatePrecedes, coordinateSign, huLt, hvLt,
        not_lt_of_ge huLt.le, not_lt_of_ge hvLt.le]
    · simp [relationSign, coordinatePrecedes, coordinateSign, huLt, hvGt,
        not_lt_of_ge huLt.le, not_lt_of_ge hvGt.le]
  · rcases lt_or_gt_of_ne hvne with hvLt | hvGt
    · simp [relationSign, coordinatePrecedes, coordinateSign, huGt, hvLt,
        not_lt_of_ge huGt.le, not_lt_of_ge hvLt.le]
    · simp [relationSign, coordinatePrecedes, coordinateSign, huGt, hvGt,
        not_lt_of_ge huGt.le, not_lt_of_ge hvGt.le]

/-- The real antisymmetric Pauli--Jordan matrix `Delta`, with the conventional factor `1/2`. -/
noncomputable def pauliJordan (r : ι → ι → Prop) [DecidableRel r] : Matrix ι ι ℝ :=
  fun x y => (relationSign r x y : ℝ) / 2

@[simp]
theorem pauliJordan_apply (r : ι → ι → Prop) [DecidableRel r] (x y : ι) :
    pauliJordan r x y = (relationSign r x y : ℝ) / 2 := rfl

@[simp]
theorem pauliJordan_diagonal (r : ι → ι → Prop) [DecidableRel r] (x : ι) :
    pauliJordan r x x = 0 := by
  simp [pauliJordan]

theorem pauliJordan_swap (r : ι → ι → Prop) [DecidableRel r] (x y : ι) :
    pauliJordan r y x = -pauliJordan r x y := by
  unfold pauliJordan
  rw [relationSign_swap, Int.cast_neg, neg_div]

/-- The real Pauli--Jordan matrix is antisymmetric. -/
theorem pauliJordan_transpose (r : ι → ι → Prop) [DecidableRel r] :
    (pauliJordan r)ᵀ = -pauliJordan r := by
  ext x y
  exact pauliJordan_swap r x y

/-- The complex Hermitian matrix `i Delta`. -/
noncomputable def iPauliJordan (r : ι → ι → Prop) [DecidableRel r] : Matrix ι ι ℂ :=
  fun x y => Complex.I * pauliJordan r x y

@[simp]
theorem iPauliJordan_apply (r : ι → ι → Prop) [DecidableRel r] (x y : ι) :
    iPauliJordan r x y = Complex.I * pauliJordan r x y := rfl

@[simp]
theorem iPauliJordan_apply_complex (r : ι → ι → Prop) [DecidableRel r] (x y : ι) :
    iPauliJordan r x y = Complex.I * (relationSign r x y : ℂ) / 2 := by
  rw [iPauliJordan_apply, pauliJordan_apply]
  push_cast
  ring

/-- Multiplication of the real antisymmetric matrix by `i` makes it Hermitian. -/
theorem iPauliJordan_isHermitian (r : ι → ι → Prop) [DecidableRel r] :
    (iPauliJordan r).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro x y
  rw [iPauliJordan_apply, iPauliJordan_apply, pauliJordan_swap]
  simp

/-- Exact probability normalization: divide `i Delta` by the finite cardinality. -/
noncomputable def normalizedIPauliJordan [Fintype ι] (r : ι → ι → Prop) [DecidableRel r] :
    Matrix ι ι ℂ :=
  (Fintype.card ι : ℂ)⁻¹ • iPauliJordan r

@[simp]
theorem normalizedIPauliJordan_apply [Fintype ι] (r : ι → ι → Prop) [DecidableRel r]
    (x y : ι) :
    normalizedIPauliJordan r x y =
      (Fintype.card ι : ℂ)⁻¹ * iPauliJordan r x y := by
  rfl

theorem normalizedIPauliJordan_isHermitian [Fintype ι]
    (r : ι → ι → Prop) [DecidableRel r] :
    (normalizedIPauliJordan r).IsHermitian := by
  exact (iPauliJordan_isHermitian r).smul (isSelfAdjoint_iff.mpr (by simp))

/-- Pull a relation across a relabelling equivalence. -/
def Relabel (e : ι ≃ κ) (r : ι → ι → Prop) : κ → κ → Prop :=
  fun x y => r (e.symm x) (e.symm y)

instance (e : ι ≃ κ) (r : ι → ι → Prop) [DecidableRel r] : DecidableRel (Relabel e r) :=
  fun x y => inferInstanceAs (Decidable (r (e.symm x) (e.symm y)))

theorem pauliJordan_relabel (e : ι ≃ κ) (r : ι → ι → Prop) [DecidableRel r] :
    pauliJordan (Relabel e r) = Matrix.reindex e e (pauliJordan r) := by
  ext x y
  rfl

theorem iPauliJordan_relabel (e : ι ≃ κ) (r : ι → ι → Prop) [DecidableRel r] :
    iPauliJordan (Relabel e r) = Matrix.reindex e e (iPauliJordan r) := by
  ext x y
  rfl

theorem normalizedIPauliJordan_relabel [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (r : ι → ι → Prop) [DecidableRel r] :
    normalizedIPauliJordan (Relabel e r) =
      Matrix.reindex e e (normalizedIPauliJordan r) := by
  ext x y
  simp [normalizedIPauliJordan, iPauliJordan_relabel, Fintype.card_congr e]

/-- The strict order on the permutation two-order is exactly strict precedence in both ranks. -/
theorem twoOrder_lt_iff {N : ℕ} (σ : Equiv.Perm (Fin N)) (x y : Fin N) :
    (show TwoOrder σ from x) < (show TwoOrder σ from y) ↔ x < y ∧ σ x < σ y := by
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨hxy, hne⟩
    exact ⟨lt_of_le_of_ne hxy.1 hne, lt_of_le_of_ne hxy.2 (σ.injective.ne hne)⟩
  · rintro ⟨hxy, hσxy⟩
    exact ⟨⟨hxy.le, hσxy.le⟩, hxy.ne⟩

end PauliJordan

end CausalSet
