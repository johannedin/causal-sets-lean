/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/
module

public import Mathlib.Topology.MetricSpace.BundledFun
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Labelled correspondences

This file develops correspondence distance for a finite family of labelled pseudometric
kernels.  A single correspondence controls every label.  Distortions take values in
`ℝ≥0∞`; this makes the definitions meaningful without a boundedness hypothesis and agrees
with the usual real-valued definition for bounded systems.

The construction is independent of causal-set-specific definitions.
-/

@[expose] public section

open scoped ENNReal
open Set

namespace LabelledCorrespondence

universe u v w z

variable {ι : Type u} {α : Type v} {β : Type w} {γ : Type z}

/-- A labelled family of real-valued pseudometric kernels. -/
abbrev KernelFamily (ι α : Type*) := ι → PseudoMetric α ℝ

/-- A relation whose two coordinate projections are surjective. -/
structure Correspondence (α β : Type*) where
  /-- The underlying relation. -/
  rel : Set (α × β)
  left_total : ∀ x, ∃ y, (x, y) ∈ rel
  right_total : ∀ y, ∃ x, (x, y) ∈ rel

namespace Correspondence

instance : Membership (α × β) (Correspondence α β) := ⟨fun R p => p ∈ R.rel⟩

@[ext]
theorem ext {R S : Correspondence α β} (h : R.rel = S.rel) : R = S := by
  cases R
  cases S
  simp_all

/-- The identity correspondence. -/
def refl (α : Type*) : Correspondence α α where
  rel := {p | p.1 = p.2}
  left_total x := ⟨x, rfl⟩
  right_total x := ⟨x, rfl⟩

/-- Reverse the two coordinates of a correspondence. -/
def symm (R : Correspondence α β) : Correspondence β α where
  rel := Prod.swap ⁻¹' R.rel
  left_total y := by
    obtain ⟨x, hx⟩ := R.right_total y
    exact ⟨x, hx⟩
  right_total x := by
    obtain ⟨y, hy⟩ := R.left_total x
    exact ⟨y, hy⟩

/-- Relational composition of correspondences. -/
def comp (R : Correspondence α β) (S : Correspondence β γ) : Correspondence α γ where
  rel := {p | ∃ y, (p.1, y) ∈ R ∧ (y, p.2) ∈ S}
  left_total x := by
    obtain ⟨y, hxy⟩ := R.left_total x
    obtain ⟨z, hyz⟩ := S.left_total y
    exact ⟨z, y, hxy, hyz⟩
  right_total z := by
    obtain ⟨y, hyz⟩ := S.right_total z
    obtain ⟨x, hxy⟩ := R.right_total y
    exact ⟨x, y, hxy, hyz⟩

/-- The graph of a surjective map is a correspondence. -/
def graph (f : α → β) (hf : Function.Surjective f) : Correspondence α β where
  rel := {p | f p.1 = p.2}
  left_total x := ⟨f x, rfl⟩
  right_total y := by
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨x, rfl⟩

@[simp] theorem mem_symm {R : Correspondence α β} {y : β} {x : α} :
    (y, x) ∈ R.symm ↔ (x, y) ∈ R := Iff.rfl

@[simp] theorem mem_graph {f : α → β} {hf : Function.Surjective f} {x : α} {y : β} :
    (x, y) ∈ graph f hf ↔ f x = y := Iff.rfl

end Correspondence

/-- Distortion of one labelled component along a correspondence. -/
noncomputable def componentDistortion (K : KernelFamily ι α) (L : KernelFamily ι β)
    (R : Correspondence α β) (i : ι) : ℝ≥0∞ :=
  ⨆ (p : R.rel) (q : R.rel),
    ENNReal.ofReal |K i p.1.1 q.1.1 - L i p.1.2 q.1.2|

/-- Maximum labelled distortion of a common correspondence. -/
noncomputable def jointDistortion (K : KernelFamily ι α) (L : KernelFamily ι β)
    (R : Correspondence α β) : ℝ≥0∞ :=
  ⨆ i, componentDistortion K L R i

/-- Joint correspondence distance, with the standard factor `1 / 2`. -/
noncomputable def jointDistance (K : KernelFamily ι α) (L : KernelFamily ι β) : ℝ≥0∞ :=
  (⨅ R : Correspondence α β, jointDistortion K L R) / 2

theorem componentDistortion_pair_le (K : KernelFamily ι α) (L : KernelFamily ι β)
    (R : Correspondence α β) (i : ι) {x x' : α} {y y' : β}
    (hxy : (x, y) ∈ R) (hxy' : (x', y') ∈ R) :
    ENNReal.ofReal |K i x x' - L i y y'| ≤ componentDistortion K L R i := by
  let p : R.rel := ⟨(x, y), hxy⟩
  let q : R.rel := ⟨(x', y'), hxy'⟩
  exact le_iSup_of_le p (le_iSup_of_le q le_rfl)

theorem componentDistortion_symm (K : KernelFamily ι α) (L : KernelFamily ι β)
    (R : Correspondence α β) (i : ι) :
    componentDistortion L K R.symm i = componentDistortion K L R i := by
  apply le_antisymm
  · refine iSup_le fun p => iSup_le fun q => ?_
    rw [abs_sub_comm]
    exact componentDistortion_pair_le K L R i p.2 q.2
  · refine iSup_le fun p => iSup_le fun q => ?_
    rw [abs_sub_comm]
    exact componentDistortion_pair_le L K R.symm i p.2 q.2

theorem jointDistortion_symm (K : KernelFamily ι α) (L : KernelFamily ι β)
    (R : Correspondence α β) :
    jointDistortion L K R.symm = jointDistortion K L R := by
  simp only [jointDistortion, componentDistortion_symm]

theorem componentDistortion_comp_le (K : KernelFamily ι α) (L : KernelFamily ι β)
    (M : KernelFamily ι γ) (R : Correspondence α β) (S : Correspondence β γ) (i : ι) :
    componentDistortion K M (R.comp S) i ≤
      componentDistortion K L R i + componentDistortion L M S i := by
  refine iSup_le fun p => iSup_le fun q => ?_
  obtain ⟨y, hpyR, hpyS⟩ := p.2
  obtain ⟨y', hqyR, hqyS⟩ := q.2
  calc
    ENNReal.ofReal |K i p.1.1 q.1.1 - M i p.1.2 q.1.2| ≤
        ENNReal.ofReal |K i p.1.1 q.1.1 - L i y y'| +
          ENNReal.ofReal |L i y y' - M i p.1.2 q.1.2| := by
            exact (ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)).trans ENNReal.ofReal_add_le
    _ ≤ componentDistortion K L R i + componentDistortion L M S i :=
      add_le_add
        (componentDistortion_pair_le K L R i hpyR hqyR)
        (componentDistortion_pair_le L M S i hpyS hqyS)

theorem jointDistortion_comp_le (K : KernelFamily ι α) (L : KernelFamily ι β)
    (M : KernelFamily ι γ) (R : Correspondence α β) (S : Correspondence β γ) :
    jointDistortion K M (R.comp S) ≤ jointDistortion K L R + jointDistortion L M S := by
  refine iSup_le fun i => (componentDistortion_comp_le K L M R S i).trans ?_
  exact add_le_add (le_iSup (componentDistortion K L R) i)
    (le_iSup (componentDistortion L M S) i)

theorem jointDistance_symm (K : KernelFamily ι α) (L : KernelFamily ι β) :
    jointDistance K L = jointDistance L K := by
  unfold jointDistance
  congr 1
  apply le_antisymm
  · refine le_iInf fun S => ?_
    calc
      (⨅ R, jointDistortion K L R) ≤ jointDistortion K L S.symm := iInf_le _ _
      _ = jointDistortion L K S := jointDistortion_symm L K S
  · refine le_iInf fun R => ?_
    calc
      (⨅ S, jointDistortion L K S) ≤ jointDistortion L K R.symm := iInf_le _ _
      _ = jointDistortion K L R := jointDistortion_symm K L R

theorem jointDistance_triangle (K : KernelFamily ι α) (L : KernelFamily ι β)
    (M : KernelFamily ι γ) :
    jointDistance K M ≤ jointDistance K L + jointDistance L M := by
  unfold jointDistance
  rw [← ENNReal.add_div]
  apply ENNReal.div_le_div
  · rw [ENNReal.add_iInf]
    refine le_iInf fun S => ?_
    rw [ENNReal.iInf_add]
    refine le_iInf fun R => ?_
    exact (iInf_le (fun T : Correspondence α γ => jointDistortion K M T) (R.comp S)).trans
      (jointDistortion_comp_le K L M R S)
  · exact le_rfl

/-- A bijection preserves a labelled kernel family when it preserves every component. -/
def Preserves (K : KernelFamily ι α) (L : KernelFamily ι β) (e : α ≃ β) : Prop :=
  ∀ i x x', L i (e x) (e x') = K i x x'

theorem componentDistortion_graph_eq_zero (K : KernelFamily ι α) (L : KernelFamily ι β)
    (e : α ≃ β) (he : Preserves K L e) (i : ι) :
    componentDistortion K L (Correspondence.graph e e.surjective) i = 0 := by
  apply le_zero_iff.mp
  refine iSup_le fun p => iSup_le fun q => ?_
  rw [← p.2, ← q.2, he]
  simp

theorem jointDistortion_graph_eq_zero (K : KernelFamily ι α) (L : KernelFamily ι β)
    (e : α ≃ β) (he : Preserves K L e) :
    jointDistortion K L (Correspondence.graph e e.surjective) = 0 := by
  apply le_zero_iff.mp
  exact iSup_le fun i => (componentDistortion_graph_eq_zero K L e he i).le

theorem jointDistance_eq_zero_of_equiv (K : KernelFamily ι α) (L : KernelFamily ι β)
    (e : α ≃ β) (he : Preserves K L e) : jointDistance K L = 0 := by
  apply ENNReal.div_eq_zero_iff.mpr
  left
  apply le_zero_iff.mp
  exact (iInf_le _ (Correspondence.graph e e.surjective)).trans_eq
    (jointDistortion_graph_eq_zero K L e he)

theorem jointDistance_self (K : KernelFamily ι α) : jointDistance K K = 0 := by
  exact jointDistance_eq_zero_of_equiv K K (Equiv.refl α) (by simp [Preserves])

/-- Joint distance is invariant under a label-preserving bijection in its left argument. -/
theorem jointDistance_congr_left (K : KernelFamily ι α) (L : KernelFamily ι β)
    (M : KernelFamily ι γ) (e : α ≃ β) (he : Preserves K L e) :
    jointDistance K M = jointDistance L M := by
  have he' : Preserves L K e.symm := by
    intro i y y'
    simpa [Preserves] using (he i (e.symm y) (e.symm y')).symm
  apply le_antisymm
  · simpa [jointDistance_eq_zero_of_equiv K L e he] using jointDistance_triangle K L M
  · simpa [jointDistance_eq_zero_of_equiv L K e.symm he'] using jointDistance_triangle L K M

/-- Joint distance is invariant under a label-preserving bijection in its right argument. -/
theorem jointDistance_congr_right (K : KernelFamily ι α) (L : KernelFamily ι β)
    (M : KernelFamily ι γ) (e : β ≃ γ) (he : Preserves L M e) :
    jointDistance K L = jointDistance K M := by
  rw [jointDistance_symm K L, jointDistance_symm K M]
  exact jointDistance_congr_left L M K e he

/-! ## Compact zero distance -/

/-- Every labelled kernel is continuous in both variables. -/
def ContinuousKernels [TopologicalSpace α] (K : KernelFamily ι α) : Prop :=
  ∀ i, Continuous fun p : α × α => K i p.1 p.2

/-- The pointwise discrepancy of one label on two matched pairs. -/
def pairDiscrepancy (K : KernelFamily ι α) (L : KernelFamily ι β) (i : ι)
    (p : (α × β) × (α × β)) : ℝ :=
  |K i p.1.1 p.2.1 - L i p.1.2 p.2.2|

theorem continuous_pairDiscrepancy [TopologicalSpace α] [TopologicalSpace β]
    (K : KernelFamily ι α) (L : KernelFamily ι β)
    (hK : ContinuousKernels K) (hL : ContinuousKernels L) (i : ι) :
    Continuous (pairDiscrepancy K L i) := by
  unfold pairDiscrepancy
  exact ((hK i).comp (continuous_fst.fst.prodMk continuous_snd.fst)).sub
    ((hL i).comp (continuous_fst.snd.prodMk continuous_snd.snd)) |>.abs

/-- A nonempty compact relation has both coordinate projections surjective. -/
def IsCommonCompact [TopologicalSpace α] [TopologicalSpace β]
    (C : TopologicalSpace.NonemptyCompacts (α × β)) : Prop :=
  (∀ x, ((C : Set (α × β)) ∩ ({x} ×ˢ (Set.univ : Set β))).Nonempty) ∧
    ∀ y, ((C : Set (α × β)) ∩ ((Set.univ : Set α) ×ˢ {y})).Nonempty

theorem isClosed_isCommonCompact [TopologicalSpace α] [TopologicalSpace β]
    [T1Space α] [T1Space β] :
    IsClosed {C : TopologicalSpace.NonemptyCompacts (α × β) | IsCommonCompact C} := by
  unfold IsCommonCompact
  apply IsClosed.inter
  · let A : Set (TopologicalSpace.NonemptyCompacts (α × β)) := {C |
      ∀ x, ((C : Set (α × β)) ∩ ({x} ×ˢ (Set.univ : Set β))).Nonempty}
    change IsClosed A
    have hA : A = ⋂ x, {C : TopologicalSpace.NonemptyCompacts (α × β) |
        ((C : Set (α × β)) ∩ ({x} ×ˢ (Set.univ : Set β))).Nonempty} := by
      ext C
      simp [A]
    rw [hA]
    exact isClosed_iInter fun x =>
      TopologicalSpace.NonemptyCompacts.isClosed_inter_nonempty_of_isClosed
        (isClosed_singleton.prod isClosed_univ)
  · let A : Set (TopologicalSpace.NonemptyCompacts (α × β)) := {C |
      ∀ y, ((C : Set (α × β)) ∩ ((Set.univ : Set α) ×ˢ {y})).Nonempty}
    change IsClosed A
    have hA : A = ⋂ y, {C : TopologicalSpace.NonemptyCompacts (α × β) |
        ((C : Set (α × β)) ∩ ((Set.univ : Set α) ×ˢ {y})).Nonempty} := by
      ext C
      simp [A]
    rw [hA]
    exact isClosed_iInter fun y =>
      TopologicalSpace.NonemptyCompacts.isClosed_inter_nonempty_of_isClosed
        (isClosed_univ.prod isClosed_singleton)

/-- All pairs in a compact relation have discrepancy at most `c` for every label. -/
def CompactDistortionAtMost [TopologicalSpace α] [TopologicalSpace β]
    (K : KernelFamily ι α) (L : KernelFamily ι β) (c : ℝ)
    (C : TopologicalSpace.NonemptyCompacts (α × β)) : Prop :=
  ∀ i, ((C : Set (α × β)) ×ˢ (C : Set (α × β))) ⊆
    {p | pairDiscrepancy K L i p ≤ c}

theorem isClosed_compactDistortionAtMost [TopologicalSpace α] [TopologicalSpace β]
    [T2Space α] [T2Space β] (K : KernelFamily ι α) (L : KernelFamily ι β)
    (hK : ContinuousKernels K) (hL : ContinuousKernels L) (c : ℝ) :
    IsClosed {C : TopologicalSpace.NonemptyCompacts (α × β) |
      CompactDistortionAtMost K L c C} := by
  unfold CompactDistortionAtMost
  rw [show {C : TopologicalSpace.NonemptyCompacts (α × β) |
      ∀ i, ((C : Set (α × β)) ×ˢ (C : Set (α × β))) ⊆
        {p | pairDiscrepancy K L i p ≤ c}} =
      ⋂ i, {C : TopologicalSpace.NonemptyCompacts (α × β) |
        ((C : Set (α × β)) ×ˢ (C : Set (α × β))) ⊆
        {p | pairDiscrepancy K L i p ≤ c}} by ext; simp]
  apply isClosed_iInter
  intro i
  have hF : IsClosed {p : (α × β) × (α × β) | pairDiscrepancy K L i p ≤ c} :=
    isClosed_Iic.preimage (continuous_pairDiscrepancy K L hK hL i)
  have hprod : Continuous (fun C : TopologicalSpace.NonemptyCompacts (α × β) => C ×ˢ C) := by
    fun_prop
  exact (TopologicalSpace.NonemptyCompacts.isClosed_subsets_of_isClosed hF).preimage hprod

/-- The closure of a correspondence is a common nonempty compact relation on compact spaces. -/
noncomputable def Correspondence.compactClosure [TopologicalSpace α] [TopologicalSpace β]
    [CompactSpace α] [CompactSpace β] [Nonempty α]
    (R : Correspondence α β) : TopologicalSpace.NonemptyCompacts (α × β) where
  carrier := closure R.rel
  isCompact' := isClosed_closure.isCompact
  nonempty' := by
    obtain ⟨y, hy⟩ := R.left_total (Classical.arbitrary α)
    exact ⟨_, subset_closure hy⟩

theorem Correspondence.isCommonCompact_compactClosure [TopologicalSpace α] [TopologicalSpace β]
    [CompactSpace α] [CompactSpace β] [Nonempty α]
    (R : Correspondence α β) : IsCommonCompact R.compactClosure := by
  constructor
  · intro x
    obtain ⟨y, hy⟩ := R.left_total x
    exact ⟨(x, y), subset_closure hy, by simp⟩
  · intro y
    obtain ⟨x, hx⟩ := R.right_total y
    exact ⟨(x, y), subset_closure hx, by simp⟩

theorem Correspondence.compactDistortionAtMost_compactClosure
    [TopologicalSpace α] [TopologicalSpace β] [T2Space α] [T2Space β]
    [CompactSpace α] [CompactSpace β] [Nonempty α]
    (K : KernelFamily ι α) (L : KernelFamily ι β)
    (hK : ContinuousKernels K) (hL : ContinuousKernels L)
    (R : Correspondence α β) (c : ℝ) (hc : 0 ≤ c)
    (hR : jointDistortion K L R ≤ ENNReal.ofReal c) :
    CompactDistortionAtMost K L c R.compactClosure := by
  intro i
  have hclosed : IsClosed {p : (α × β) × (α × β) |
      pairDiscrepancy K L i p ≤ c} :=
    isClosed_Iic.preimage (continuous_pairDiscrepancy K L hK hL i)
  change (closure R.rel ×ˢ closure R.rel) ⊆ _
  rw [← closure_prod_eq]
  apply closure_minimal _ hclosed
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  apply (ENNReal.ofReal_le_ofReal_iff hc).mp
  exact (componentDistortion_pair_le K L R i hx hy).trans
    ((le_iSup (componentDistortion K L R) i).trans hR)

/-- On compact spaces, an infimum of zero is attained by an exact common correspondence. -/
theorem exists_jointDistortion_eq_zero_of_jointDistance_eq_zero
    [MetricSpace α] [MetricSpace β] [CompactSpace α] [CompactSpace β]
    [Nonempty α] [Nonempty β]
    (K : KernelFamily ι α) (L : KernelFamily ι β)
    (hK : ContinuousKernels K) (hL : ContinuousKernels L)
    (hzero : jointDistance K L = 0) :
    ∃ R : Correspondence α β, jointDistortion K L R = 0 := by
  have hinf : (⨅ R : Correspondence α β, jointDistortion K L R) = 0 := by
    unfold jointDistance at hzero
    rcases ENNReal.div_eq_zero_iff.mp hzero with h | h
    · exact h
    · norm_num at h
  let c : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  let A : ℕ → Set (TopologicalSpace.NonemptyCompacts (α × β)) := fun n =>
    {C | IsCommonCompact C ∧ CompactDistortionAtMost K L (c n) C}
  have hc_pos (n : ℕ) : 0 < c n := by
    dsimp [c]
    positivity
  have hAclosed (n : ℕ) : IsClosed (A n) := by
    exact isClosed_isCommonCompact.inter
      (isClosed_compactDistortionAtMost K L hK hL (c n))
  have hAnonempty (n : ℕ) : (A n).Nonempty := by
    have hlt : (⨅ R : Correspondence α β, jointDistortion K L R) <
        ENNReal.ofReal (c n) := by
      rw [hinf]
      exact ENNReal.ofReal_pos.mpr (hc_pos n)
    obtain ⟨R, hR⟩ := iInf_lt_iff.mp hlt
    refine ⟨R.compactClosure, Correspondence.isCommonCompact_compactClosure R, ?_⟩
    exact Correspondence.compactDistortionAtMost_compactClosure K L hK hL R (c n)
      (hc_pos n).le hR.le
  have hAanti (n : ℕ) : A (n + 1) ⊆ A n := by
    rintro C ⟨hcommon, hdist⟩
    refine ⟨hcommon, fun i p hp => ?_⟩
    have hle : pairDiscrepancy K L i p ≤ c (n + 1) := hdist i hp
    refine hle.trans ?_
    dsimp [c]
    gcongr
    exact Nat.le_succ n
  obtain ⟨C, hC⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed A hAanti
    hAnonempty (hAclosed 0).isCompact hAclosed
  have hCn (n : ℕ) : C ∈ A n := Set.mem_iInter.mp hC n
  have hcommon : IsCommonCompact C := (hCn 0).1
  let R : Correspondence α β :=
    { rel := C
      left_total := fun x => by
        obtain ⟨p, hpC, hpx⟩ := hcommon.1 x
        simp only [mem_prod, mem_singleton_iff, mem_univ, and_true] at hpx
        exact ⟨p.2, hpx ▸ hpC⟩
      right_total := fun y => by
        obtain ⟨p, hpC, hpy⟩ := hcommon.2 y
        simp only [mem_prod, mem_univ, mem_singleton_iff, true_and] at hpy
        exact ⟨p.1, hpy ▸ hpC⟩ }
  refine ⟨R, le_zero_iff.mp (iSup_le fun i => iSup_le fun p => iSup_le fun q => ?_)⟩
  have hle (n : ℕ) : pairDiscrepancy K L i (p.1, q.1) ≤ c n :=
    (hCn n).2 i ⟨p.2, q.2⟩
  have hz : pairDiscrepancy K L i (p.1, q.1) = 0 := by
    apply le_antisymm
    · exact ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat hle
    · exact abs_nonneg _
  rw [show K i p.1.1 q.1.1 = L i p.1.2 q.1.2 by
    exact sub_eq_zero.mp (abs_eq_zero.mp hz)]
  simp

/-- Pointwise maximum of a finite family of pseudometric kernels. -/
noncomputable def maximum [Fintype ι] (K : KernelFamily ι α) : PseudoMetric α ℝ :=
  Finset.univ.sup K

/-- The maximum labelled kernel agrees with the ambient metric. -/
def MaximumInducesMetric [Fintype ι] [PseudoMetricSpace α]
    (K : KernelFamily ι α) : Prop :=
  ∀ x y, maximum K x y = dist x y

theorem PseudoMetric.abs_sub_apply_le (d : PseudoMetric α ℝ) (x y x' y' : α) :
    |d x y - d x' y'| ≤ d x x' + d y y' := by
  have h₁ : d x y ≤ d x x' + d x' y' + d y' y := by
    calc
      d x y ≤ d x x' + d x' y := d.triangle _ _ _
      _ ≤ d x x' + (d x' y' + d y' y) := by
        gcongr
        exact d.triangle _ _ _
      _ = d x x' + d x' y' + d y' y := by ring
  have h₂ : d x' y' ≤ d x' x + d x y + d y y' := by
    calc
      d x' y' ≤ d x' x + d x y' := d.triangle _ _ _
      _ ≤ d x' x + (d x y + d y y') := by
        gcongr
        exact d.triangle _ _ _
      _ = d x' x + d x y + d y y' := by ring
  rw [abs_le]
  constructor <;> linarith [d.symm x' x, d.symm y' y]

theorem continuousKernels_of_maximumInducesMetric [Fintype ι]
    [Nonempty ι] [MetricSpace α] (K : KernelFamily ι α)
    (hK : MaximumInducesMetric K) : ContinuousKernels K := by
  intro i
  apply (LipschitzWith.of_dist_le_mul (K := 2) fun p q => ?_).continuous
  rw [Real.dist_eq, Prod.dist_eq]
  calc
    |K i p.1 p.2 - K i q.1 q.2| ≤ K i p.1 q.1 + K i p.2 q.2 :=
      PseudoMetric.abs_sub_apply_le (K i) _ _ _ _
    _ ≤ maximum K p.1 q.1 + maximum K p.2 q.2 := by
      exact add_le_add ((Finset.le_sup (f := K) (Finset.mem_univ i)) _ _)
        ((Finset.le_sup (f := K) (Finset.mem_univ i)) _ _)
    _ = dist p.1 q.1 + dist p.2 q.2 := by rw [hK, hK]
    _ ≤ 2 * max (dist p.1 q.1) (dist p.2 q.2) := by
      linarith [le_max_left (dist p.1 q.1) (dist p.2 q.2),
        le_max_right (dist p.1 q.1) (dist p.2 q.2)]

theorem kernel_eq_of_jointDistortion_eq_zero
    (K : KernelFamily ι α) (L : KernelFamily ι β) (R : Correspondence α β)
    (hR : jointDistortion K L R = 0) (i : ι)
    {x x' : α} {y y' : β} (hxy : (x, y) ∈ R) (hxy' : (x', y') ∈ R) :
    K i x x' = L i y y' := by
  have hle := (componentDistortion_pair_le K L R i hxy hxy').trans
    ((le_iSup (componentDistortion K L R) i).trans_eq hR)
  have habs : |K i x x' - L i y y'| = 0 := by
    apply le_antisymm
    · exact ENNReal.ofReal_eq_zero.mp (le_zero_iff.mp hle)
    · exact abs_nonneg _
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

theorem exists_preserving_equiv_of_exact_correspondence [Fintype ι] [Nonempty ι]
    [MetricSpace α] [MetricSpace β]
    (K : KernelFamily ι α) (L : KernelFamily ι β)
    (hK : MaximumInducesMetric K) (hL : MaximumInducesMetric L)
    (R : Correspondence α β) (hR : jointDistortion K L R = 0) :
    ∃ e : α ≃ β, Preserves K L e := by
  let f : α → β := fun x => Classical.choose (R.left_total x)
  have hf (x : α) : (x, f x) ∈ R := Classical.choose_spec (R.left_total x)
  have hright_unique {x : α} {y y' : β} (hy : (x, y) ∈ R) (hy' : (x, y') ∈ R) :
      y = y' := by
    apply dist_eq_zero.mp
    rw [← hL]
    apply le_antisymm
    · rw [maximum, PseudoMetric.finsetSup_apply (s := Finset.univ)
        ⟨Classical.arbitrary ι, Finset.mem_univ _⟩]
      apply (Finset.sup'_le_iff ⟨Classical.arbitrary ι, Finset.mem_univ _⟩ _).mpr
      intro i hi
      rw [← (K i).refl x]
      exact (kernel_eq_of_jointDistortion_eq_zero K L R hR i hy hy').symm.le
    · exact (maximum L).nonneg _ _
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨x, hxy⟩ := R.right_total y
    exact ⟨x, hright_unique (hf x) hxy⟩
  have hf_inj : Function.Injective f := by
    intro x x' hxx'
    apply dist_eq_zero.mp
    rw [← hK]
    apply le_antisymm
    · rw [maximum, PseudoMetric.finsetSup_apply (s := Finset.univ)
        ⟨Classical.arbitrary ι, Finset.mem_univ _⟩]
      apply (Finset.sup'_le_iff ⟨Classical.arbitrary ι, Finset.mem_univ _⟩ _).mpr
      intro i hi
      rw [kernel_eq_of_jointDistortion_eq_zero K L R hR i (hf x) (hf x'), hxx']
      exact (L i).refl _ |>.le
    · exact (maximum K).nonneg _ _
  let e : α ≃ β := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨e, fun i x x' => ?_⟩
  exact (kernel_eq_of_jointDistortion_eq_zero K L R hR i (hf x) (hf x')).symm

/-- Compact labelled zero-distance theorem.

The label type is finite and nonempty; both spaces are nonempty compact metric spaces; and the
pointwise maximum of each labelled pseudometric family is its ambient metric.  Under precisely
these hypotheses, zero joint correspondence distance is equivalent to a single bijection that
preserves every labelled kernel.
-/
theorem jointDistance_eq_zero_iff_exists_preserving_equiv [Fintype ι] [Nonempty ι]
    [MetricSpace α] [MetricSpace β] [CompactSpace α] [CompactSpace β]
    [Nonempty α] [Nonempty β]
    (K : KernelFamily ι α) (L : KernelFamily ι β)
    (hK : MaximumInducesMetric K) (hL : MaximumInducesMetric L) :
    jointDistance K L = 0 ↔ ∃ e : α ≃ β, Preserves K L e := by
  constructor
  · intro hzero
    obtain ⟨R, hR⟩ := exists_jointDistortion_eq_zero_of_jointDistance_eq_zero K L
      (continuousKernels_of_maximumInducesMetric K hK)
      (continuousKernels_of_maximumInducesMetric L hL) hzero
    exact exists_preserving_equiv_of_exact_correspondence K L hK hL R hR
  · rintro ⟨e, he⟩
    exact jointDistance_eq_zero_of_equiv K L e he

end LabelledCorrespondence
