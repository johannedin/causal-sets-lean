/-
Copyright (c) 2026 Johan Nedin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Nedin
-/

module

public import CausalSet.Abundance
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Finite random two-orders

This module develops exact, measure-free permutation identities for finite two-dimensional
orders. A permutation `σ : Equiv.Perm (Fin N)` orders positions by the intersection of the
usual order and the order of their images under `σ`.

The statements are finite combinatorics over all permutations. Their interpretation using
uniform samples in a two-dimensional causal diamond is not formalized here. No claim about a
Poisson process, physical volume, curvature, or a continuum limit is made.
-/

@[expose] public section

namespace CausalSet

/-- The two-dimensional order of a permutation: `i ≤ j` when both `i ≤ j` and `σ i ≤ σ j`. -/
def TwoOrder {N : ℕ} (_σ : Equiv.Perm (Fin N)) := Fin N

namespace TwoOrder

variable {N : ℕ} (σ : Equiv.Perm (Fin N))

instance : DecidableEq (TwoOrder σ) := inferInstanceAs (DecidableEq (Fin N))
instance : Fintype (TwoOrder σ) := inferInstanceAs (Fintype (Fin N))

instance : PartialOrder (TwoOrder σ) where
  le i j := (show Fin N from i) ≤ (show Fin N from j) ∧
    σ (show Fin N from i) ≤ σ (show Fin N from j)
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ hij hjk := ⟨hij.1.trans hjk.1, hij.2.trans hjk.2⟩
  le_antisymm i j hij hji := by
    change (show Fin N from i) = (show Fin N from j)
    exact le_antisymm hij.1 hji.1

instance : DecidableLE (TwoOrder σ) := fun i j =>
  inferInstanceAs (Decidable ((show Fin N from i) ≤ (show Fin N from j) ∧
    σ (show Fin N from i) ≤ σ (show Fin N from j)))
instance : DecidableLT (TwoOrder σ) := fun _ _ => decidable_of_iff _ lt_iff_le_not_ge.symm

-- This concrete finite type has no competing locally finite order instance.
instance : LocallyFiniteOrder (TwoOrder σ) := Fintype.toLocallyFiniteOrder

end TwoOrder

/-- Number of permutations for which `i` precedes `j` and their open interval has size `k`. -/
def windowCount (N k : ℕ) (i j : Fin N) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ i < σ j ∧
    (Finset.univ.filter fun t : Fin N =>
      i < t ∧ t < j ∧ σ i < σ t ∧ σ t < σ j).card = k).card

namespace RandomTwoOrder

open Equiv Finset Function

private theorem card_filter_congr {α : Type*} [Fintype α] [DecidableEq α]
    (p q : α → Prop) [DecidablePred p] [DecidablePred q] (e : α ≃ α)
    (h : ∀ x, p x ↔ q (e x)) :
    (univ.filter p).card = (univ.filter q).card := by
  rw [← Fintype.card_subtype p, ← Fintype.card_subtype q]
  exact Fintype.card_congr (e.subtypeEquiv h)

private theorem uniformFiber_ratio {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (f : α → β) (p : β → Prop) [DecidablePred p]
    (c : ℕ) (hf : ∀ b, (univ.filter fun a => f a = b).card = c) :
    Fintype.card β * (univ.filter fun a => p (f a)).card =
      Fintype.card α * (univ.filter p).card := by
  have hα : Fintype.card α = Fintype.card β * c := by
    rw [show Fintype.card α = ∑ b ∈ (univ : Finset β),
        ((univ : Finset α).filter fun a => f a = b).card from
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
    simp_rw [hf]
    simp
  have hp : (univ.filter fun a => p (f a)).card = (univ.filter p).card * c := by
    have hsum := Finset.sum_card_fiberwise_eq_card_filter (univ : Finset α)
      (univ.filter p) f
    have hsum' : ∑ b ∈ univ.filter p,
        ((univ : Finset α).filter fun a => f a = b).card =
        (univ.filter fun a => p (f a)).card := by
      simpa using hsum
    rw [← hsum']
    simp_rw [hf]
    simp
  rw [hp, hα]
  ac_rfl

/-- The consecutive window from `i` through `j`, parametrized starting at zero. -/
private def windowEmbedding {N : ℕ} (i j : Fin N) :
    Fin ((j : ℕ) - i + 1) ↪ Fin N where
  toFun r := ⟨(i : ℕ) + r, by
    have hr := r.isLt
    have hj := j.isLt
    omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    simpa using congrArg Fin.val h

private theorem windowEmbedding_zero {N : ℕ} {i j : Fin N} :
    windowEmbedding i j 0 = i := by
  apply Fin.ext
  rfl

private theorem windowEmbedding_last {N : ℕ} {i j : Fin N} (hij : i < j) :
    windowEmbedding i j (Fin.last ((j : ℕ) - i)) = j := by
  apply Fin.ext
  change (i : ℕ) + ((j : ℕ) - i) = j
  omega

/-- The relative-order pattern of an embedding of a finite tuple into a linear order. -/
private def pattern {m : ℕ} {α : Type*} [LinearOrder α] (f : Fin m ↪ α) :
    Equiv.Perm (Fin m) :=
  (Tuple.sort f).symm

private theorem pattern_apply_sort {m : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin m ↪ α) (r : Fin m) : pattern f (Tuple.sort f r) = r := by
  simp [pattern]

private theorem sort_apply_pattern {m : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin m ↪ α) (r : Fin m) : Tuple.sort f (pattern f r) = r := by
  simp [pattern]

private theorem pattern_lt_iff {m : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin m ↪ α) (a b : Fin m) : pattern f a < pattern f b ↔ f a < f b := by
  have hmono : StrictMono (f ∘ Tuple.sort f) :=
    (Tuple.monotone_sort f).strictMono_of_injective
      (f.injective.comp (Tuple.sort f).injective)
  constructor
  · intro h
    simpa [sort_apply_pattern] using hmono h
  · intro h
    by_contra hn
    have hle : pattern f b ≤ pattern f a := le_of_not_gt hn
    have := hmono.monotone hle
    simp only [Function.comp_apply, sort_apply_pattern] at this
    exact (not_le_of_gt h) this

/-- Precomposition by a permutation is an equivalence on embeddings. -/
private def precompEmbedding {m : ℕ} {α : Type*} (τ : Equiv.Perm (Fin m)) :
    (Fin m ↪ α) ≃ (Fin m ↪ α) where
  toFun f := τ.toEmbedding.trans f
  invFun f := τ.symm.toEmbedding.trans f
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp

private theorem pattern_precomp {m : ℕ} {α : Type*} [LinearOrder α]
    (τ : Equiv.Perm (Fin m)) (f : Fin m ↪ α) :
    pattern (precompEmbedding τ f) = τ.trans (pattern f) := by
  apply Equiv.ext
  intro r
  apply (Tuple.sort f).injective
  change Tuple.sort f (pattern (precompEmbedding τ f) r) =
    Tuple.sort f (pattern f (τ r))
  rw [sort_apply_pattern]
  have h := Tuple.comp_perm_comp_sort_eq_comp_sort (f := fun x => f x) (σ := τ)
  have hr := congrFun h (pattern (precompEmbedding τ f) r)
  have hr' := f.injective hr
  change τ (Tuple.sort (precompEmbedding τ f) (pattern (precompEmbedding τ f) r)) =
    Tuple.sort f (pattern (precompEmbedding τ f) r) at hr'
  rw [sort_apply_pattern] at hr'
  exact hr'.symm

private theorem pattern_uniformFiber_ratio {m : ℕ} {α : Type*} [LinearOrder α]
    [Fintype α] [DecidableEq α] (p : Equiv.Perm (Fin m) → Prop) [DecidablePred p] :
    m.factorial * (univ.filter fun f : Fin m ↪ α => p (pattern f)).card =
      Fintype.card (Fin m ↪ α) *
        (univ.filter fun τ : Equiv.Perm (Fin m) => p τ).card := by
  classical
  let one : Equiv.Perm (Fin m) := 1
  let c := (univ.filter fun f : Fin m ↪ α => pattern f = one).card
  have hf : ∀ q : Equiv.Perm (Fin m),
      (univ.filter fun f : Fin m ↪ α => pattern f = q).card = c := by
    intro q
    let τ : Equiv.Perm (Fin m) := q
    symm
    apply card_filter_congr
      (fun f : Fin m ↪ α => pattern f = one)
      (fun f : Fin m ↪ α => pattern f = q)
      (precompEmbedding τ)
    intro f
    rw [pattern_precomp]
    change pattern f = one ↔ τ.trans (pattern f) = q
    constructor
    · intro h
      rw [h]
      exact Equiv.trans_refl q
    · intro h
      have h' := (Equiv.trans_cancel_left τ (pattern f) q).mp h
      change pattern f = Equiv.refl (Fin m)
      simpa [τ] using h'
  simpa only [Fintype.card_perm, Fintype.card_fin] using
    uniformFiber_ratio pattern p c hf

private abbrev EndpointPair (d : ℕ) :=
  {p : Fin (d + 1) × Fin (d + 1) // p.1 ≠ p.2}

private theorem zero_ne_last {d : ℕ} (hd : 0 < d) :
    (0 : Fin (d + 1)) ≠ Fin.last d := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

private def endpoints {d : ℕ} (hd : 0 < d) (τ : Equiv.Perm (Fin (d + 1))) :
    EndpointPair d :=
  ⟨(τ 0, τ (Fin.last d)), τ.injective.ne (zero_ne_last hd)⟩

private theorem card_endpointPair (d : ℕ) :
    Fintype.card (EndpointPair d) = d * (d + 1) := by
  calc
    Fintype.card (EndpointPair d) = Fintype.card (Fin 2 ↪ Fin (d + 1)) :=
      Fintype.card_congr
        (Function.Embedding.twoEmbeddingEquiv : (Fin 2 ↪ Fin (d + 1)) ≃ EndpointPair d).symm
    _ = d * (d + 1) := by
      rw [Fintype.card_embedding_eq]
      simp [Nat.descFactorial]

private def postcompPerm {α : Type*} (h : Equiv.Perm α) :
    Equiv.Perm α ≃ Equiv.Perm α where
  toFun σ := σ.trans h
  invFun σ := σ.trans h.symm
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp

private def precompPerm {α : Type*} (h : Equiv.Perm α) :
    Equiv.Perm α ≃ Equiv.Perm α where
  toFun σ := h.trans σ
  invFun σ := h.symm.trans σ
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp

private theorem endpoints_postcomp {d : ℕ} (hd : 0 < d) (h τ : Equiv.Perm (Fin (d + 1))) :
    endpoints hd (postcompPerm h τ) =
      ⟨(h (τ 0), h (τ (Fin.last d))), by
        exact h.injective.ne (τ.injective.ne (zero_ne_last hd))⟩ := by
  rfl

private theorem endpoints_uniformFiber_ratio {d : ℕ} (hd : 0 < d)
    (p : EndpointPair d → Prop) [DecidablePred p] :
    d * (d + 1) * (univ.filter fun τ : Equiv.Perm (Fin (d + 1)) => p (endpoints hd τ)).card =
      (d + 1).factorial * (univ.filter p).card := by
  classical
  let base : EndpointPair d := endpoints hd 1
  let c := (univ.filter fun τ : Equiv.Perm (Fin (d + 1)) => endpoints hd τ = base).card
  have hf : ∀ b : EndpointPair d,
      (univ.filter fun τ : Equiv.Perm (Fin (d + 1)) => endpoints hd τ = b).card = c := by
    intro b
    let f : Bool → Fin (d + 1) := fun x => if x then base.1.2 else base.1.1
    let g : Bool → Fin (d + 1) := fun x => if x then b.1.2 else b.1.1
    have hf : Function.Injective f := by
      intro x y h
      cases x <;> cases y
      · rfl
      ·
        exact (base.property h).elim
      ·
        exact (base.property h.symm).elim
      · rfl
    have hg : Function.Injective g := by
      intro x y h
      cases x <;> cases y
      · rfl
      ·
        exact (b.property h).elim
      ·
        exact (b.property h.symm).elim
      · rfl
    obtain ⟨h, hh⟩ := Equiv.Perm.exists_extending_pair f g hf hg
    symm
    apply card_filter_congr
      (fun τ : Equiv.Perm (Fin (d + 1)) => endpoints hd τ = base)
      (fun τ : Equiv.Perm (Fin (d + 1)) => endpoints hd τ = b)
      (postcompPerm h)
    intro τ
    constructor
    · intro hτ
      apply Subtype.ext
      apply Prod.ext
      · change h (τ 0) = b.1.1
        have hτ0 := congrArg (fun z : EndpointPair d => z.1.1) hτ
        change τ 0 = base.1.1 at hτ0
        rw [hτ0]
        simpa [f, g] using hh false
      · change h (τ (Fin.last d)) = b.1.2
        have hτ1 := congrArg (fun z : EndpointPair d => z.1.2) hτ
        change τ (Fin.last d) = base.1.2 at hτ1
        rw [hτ1]
        simpa [f, g] using hh true
    · intro hτ
      apply Subtype.ext
      apply Prod.ext
      · apply h.injective
        have hτ0 := congrArg (fun z : EndpointPair d => z.1.1) hτ
        change h (τ 0) = b.1.1 at hτ0
        change h (τ 0) = h base.1.1
        exact hτ0.trans (by simpa [f, g] using (hh false).symm)
      · apply h.injective
        have hτ1 := congrArg (fun z : EndpointPair d => z.1.2) hτ
        change h (τ (Fin.last d)) = b.1.2 at hτ1
        change h (τ (Fin.last d)) = h base.1.2
        exact hτ1.trans (by simpa [f, g] using (hh true).symm)
  rw [← card_endpointPair d]
  simpa only [Fintype.card_perm, Fintype.card_fin] using
    uniformFiber_ratio (endpoints hd) p c hf

private theorem card_goodEndpointPairs {d k : ℕ} (hk : k < d) :
    (univ.filter fun p : EndpointPair d =>
      p.1.1 < p.1.2 ∧ (p.1.2 : ℕ) - p.1.1 = k + 1).card = d - k := by
  let good := univ.filter fun p : EndpointPair d =>
    p.1.1 < p.1.2 ∧ (p.1.2 : ℕ) - p.1.1 = k + 1
  let target := (univ : Finset (Fin (d - k)))
  let toIndex : (p : EndpointPair d) → p ∈ good → Fin (d - k) := fun p hp =>
    ⟨p.1.1, by
      have hgood := (mem_filter.mp hp).2
      have hp2 := p.1.2.isLt
      omega⟩
  let fromIndex : (a : Fin (d - k)) → a ∈ target → EndpointPair d := fun a _ =>
    ⟨(⟨a, by omega⟩, ⟨a + k + 1, by
      have ha := a.isLt
      omega⟩), by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega⟩
  have hi : ∀ p hp, toIndex p hp ∈ target := fun _ _ => mem_univ _
  have hj : ∀ a ha, fromIndex a ha ∈ good := by
    intro a ha
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    constructor <;> simp [fromIndex]
    · omega
  have hleft : ∀ p hp, fromIndex (toIndex p hp) (hi p hp) = p := by
    intro p hp
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> simp [fromIndex, toIndex]
    have hgood := (mem_filter.mp hp).2
    omega
  have hright : ∀ a ha, toIndex (fromIndex a ha) (hj a ha) = a := by
    intro a ha
    apply Fin.ext
    simp [fromIndex, toIndex]
  have hcard : good.card = target.card := by
    exact Finset.card_bij' toIndex fromIndex hi hj hleft hright
  simpa [good, target] using hcard

/-- Restrict a permutation to the consecutive positions from `i` through `j`. -/
private def restrictWindow {N : ℕ} (i j : Fin N) (σ : Equiv.Perm (Fin N)) :
    Fin ((j : ℕ) - i + 1) ↪ Fin N :=
  (windowEmbedding i j).trans σ.toEmbedding

private theorem restriction_uniformFiber_ratio {N : ℕ} {i j : Fin N}
    (p : (Fin ((j : ℕ) - i + 1) ↪ Fin N) → Prop) [DecidablePred p] :
    Fintype.card (Fin ((j : ℕ) - i + 1) ↪ Fin N) *
        (univ.filter fun σ : Equiv.Perm (Fin N) => p (restrictWindow i j σ)).card =
      N.factorial * (univ.filter p).card := by
  classical
  let base := windowEmbedding i j
  let c := (univ.filter fun σ : Equiv.Perm (Fin N) => restrictWindow i j σ = base).card
  have hf : ∀ b : Fin ((j : ℕ) - i + 1) ↪ Fin N,
      (univ.filter fun σ : Equiv.Perm (Fin N) => restrictWindow i j σ = b).card = c := by
    intro b
    obtain ⟨h, hh⟩ := Equiv.Perm.exists_extending_pair base b base.injective b.injective
    symm
    apply card_filter_congr
      (fun σ : Equiv.Perm (Fin N) => restrictWindow i j σ = base)
      (fun σ : Equiv.Perm (Fin N) => restrictWindow i j σ = b)
      (postcompPerm h)
    intro σ
    constructor
    · intro hσ
      apply Function.Embedding.ext
      intro r
      change h (σ (windowEmbedding i j r)) = b r
      rw [show σ (windowEmbedding i j r) = base r by
        exact congrArg (fun f => f r) hσ]
      exact hh r
    · intro hσ
      apply Function.Embedding.ext
      intro r
      apply h.injective
      change h (σ (windowEmbedding i j r)) = h (base r)
      have hr := congrArg (fun f => f r) hσ
      change h (σ (windowEmbedding i j r)) = b r at hr
      exact hr.trans (hh r).symm
  simpa only [Fintype.card_perm, Fintype.card_fin] using
    uniformFiber_ratio (restrictWindow i j) p c hf

private theorem card_window_eq_card_restrict {N : ℕ} {i j : Fin N} (hij : i < j)
    (σ : Equiv.Perm (Fin N)) :
    (univ.filter fun t : Fin N =>
      i < t ∧ t < j ∧ σ i < σ t ∧ σ t < σ j).card =
    (univ.filter fun r : Fin ((j : ℕ) - i + 1) =>
      0 < r ∧ r < Fin.last ((j : ℕ) - i) ∧
        restrictWindow i j σ 0 < restrictWindow i j σ r ∧
        restrictWindow i j σ r < restrictWindow i j σ (Fin.last ((j : ℕ) - i))).card := by
  let left := univ.filter fun t : Fin N =>
    i < t ∧ t < j ∧ σ i < σ t ∧ σ t < σ j
  let right := univ.filter fun r : Fin ((j : ℕ) - i + 1) =>
    0 < r ∧ r < Fin.last ((j : ℕ) - i) ∧
      restrictWindow i j σ 0 < restrictWindow i j σ r ∧
      restrictWindow i j σ r < restrictWindow i j σ (Fin.last ((j : ℕ) - i))
  let toIndex : (t : Fin N) → t ∈ left → Fin ((j : ℕ) - i + 1) := fun t ht =>
    ⟨(t : ℕ) - i, by
      have h := (mem_filter.mp ht).2
      omega⟩
  let fromIndex : (r : Fin ((j : ℕ) - i + 1)) → r ∈ right → Fin N := fun r _ =>
    windowEmbedding i j r
  have hi : ∀ t ht, toIndex t ht ∈ right := by
    intro t ht
    have h := (mem_filter.mp ht).2
    have heq : windowEmbedding i j (toIndex t ht) = t := by
      apply Fin.ext
      change (i : ℕ) + ((t : ℕ) - i) = t
      omega
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    constructor
    · change 0 < (t : ℕ) - i
      omega
    constructor
    · change (t : ℕ) - i < (j : ℕ) - i
      omega
    constructor
    · simpa [restrictWindow, windowEmbedding_zero, heq] using h.2.2.1
    · simpa [restrictWindow, windowEmbedding_last hij, heq] using h.2.2.2
  have hj : ∀ r hr, fromIndex r hr ∈ left := by
    intro r hr
    have h := (mem_filter.mp hr).2
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    constructor
    · change (i : ℕ) < (i : ℕ) + r
      have hr0 := h.1
      change 0 < (r : ℕ) at hr0
      omega
    constructor
    · change (i : ℕ) + r < j
      have hrlast := h.2.1
      change (r : ℕ) < (j : ℕ) - i at hrlast
      omega
    constructor
    · simpa [fromIndex, restrictWindow, windowEmbedding_zero] using h.2.2.1
    · simpa [fromIndex, restrictWindow, windowEmbedding_last hij] using h.2.2.2
  have hleft : ∀ t ht, fromIndex (toIndex t ht) (hi t ht) = t := by
    intro t ht
    apply Fin.ext
    change (i : ℕ) + ((t : ℕ) - i) = t
    have h := (mem_filter.mp ht).2
    omega
  have hright : ∀ r hr, toIndex (fromIndex r hr) (hj r hr) = r := by
    intro r hr
    apply Fin.ext
    change (i : ℕ) + r - i = r
    omega
  exact Finset.card_bij' toIndex fromIndex hi hj hleft hright

private theorem card_pattern_window {d : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin (d + 1) ↪ α) :
    (univ.filter fun r : Fin (d + 1) =>
      0 < r ∧ r < Fin.last d ∧ f 0 < f r ∧ f r < f (Fin.last d)).card =
      (Ioo (pattern f 0) (pattern f (Fin.last d))).card := by
  let left := univ.filter fun r : Fin (d + 1) =>
    0 < r ∧ r < Fin.last d ∧ f 0 < f r ∧ f r < f (Fin.last d)
  let right := Ioo (pattern f 0) (pattern f (Fin.last d))
  let toRank : (r : Fin (d + 1)) → r ∈ left → Fin (d + 1) := fun r _ => pattern f r
  let fromRank : (q : Fin (d + 1)) → q ∈ right → Fin (d + 1) := fun q _ =>
    Tuple.sort f q
  have hi : ∀ r hr, toRank r hr ∈ right := by
    intro r hr
    have h := (mem_filter.mp hr).2
    apply mem_Ioo.mpr
    exact ⟨(pattern_lt_iff f 0 r).mpr h.2.2.1,
      (pattern_lt_iff f r (Fin.last d)).mpr h.2.2.2⟩
  have hj : ∀ q hq, fromRank q hq ∈ left := by
    intro q hq
    have h := mem_Ioo.mp hq
    have h0 : Tuple.sort f q ≠ 0 := by
      intro heq
      have := congrArg (pattern f) heq
      rw [pattern_apply_sort] at this
      exact (ne_of_gt h.1) this
    have hlast : Tuple.sort f q ≠ Fin.last d := by
      intro heq
      have := congrArg (pattern f) heq
      rw [pattern_apply_sort] at this
      exact (ne_of_lt h.2) this
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    constructor
    · have hs := (Tuple.sort f q).isLt
      have h0val : (Tuple.sort f q : ℕ) ≠ 0 := by
        intro hval
        apply h0
        apply Fin.ext
        simpa using hval
      change 0 < (Tuple.sort f q : ℕ)
      omega
    constructor
    · have hs := (Tuple.sort f q).isLt
      have hlastval : (Tuple.sort f q : ℕ) ≠ d := by
        intro hval
        apply hlast
        apply Fin.ext
        simpa using hval
      change (Tuple.sort f q : ℕ) < d
      omega
    constructor
    · apply (pattern_lt_iff f 0 (Tuple.sort f q)).mp
      simpa [pattern_apply_sort] using h.1
    · apply (pattern_lt_iff f (Tuple.sort f q) (Fin.last d)).mp
      simpa [pattern_apply_sort] using h.2
  have hleft : ∀ r hr, fromRank (toRank r hr) (hi r hr) = r := by
    intro r hr
    exact sort_apply_pattern f r
  have hright : ∀ q hq, toRank (fromRank q hq) (hj q hq) = q := by
    intro q hq
    exact pattern_apply_sort f q
  exact Finset.card_bij' toRank fromRank hi hj hleft hright

private theorem card_pattern_window_eq_sub {d : ℕ}
    {α : Type*} [LinearOrder α] (f : Fin (d + 1) ↪ α) :
    (univ.filter fun r : Fin (d + 1) =>
      0 < r ∧ r < Fin.last d ∧ f 0 < f r ∧ f r < f (Fin.last d)).card =
      (pattern f (Fin.last d) : ℕ) - pattern f 0 - 1 := by
  rw [card_pattern_window f, Fin.card_Ioo]

private def embeddingWindowHas {d k : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin (d + 1) ↪ α) : Prop :=
  f 0 < f (Fin.last d) ∧
    (univ.filter fun r : Fin (d + 1) =>
      0 < r ∧ r < Fin.last d ∧ f 0 < f r ∧ f r < f (Fin.last d)).card = k

private noncomputable instance {d k : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin (d + 1) ↪ α) :
    Decidable (embeddingWindowHas (k := k) f) := Classical.propDecidable _

private def endpointHasGap {d k : ℕ} (p : EndpointPair d) : Prop :=
  p.1.1 < p.1.2 ∧ (p.1.2 : ℕ) - p.1.1 = k + 1

private theorem embeddingWindowHas_iff_endpointHasGap {d k : ℕ} (hd : 0 < d)
    {α : Type*} [LinearOrder α] (f : Fin (d + 1) ↪ α) :
    embeddingWindowHas (k := k) f ↔ endpointHasGap (k := k) (endpoints hd (pattern f)) := by
  rw [embeddingWindowHas, endpointHasGap, card_pattern_window_eq_sub f]
  change f 0 < f (Fin.last d) ∧
      (pattern f (Fin.last d) : ℕ) - pattern f 0 - 1 = k ↔
    pattern f 0 < pattern f (Fin.last d) ∧
      (pattern f (Fin.last d) : ℕ) - pattern f 0 = k + 1
  rw [← pattern_lt_iff]
  constructor
  · intro h
    exact ⟨h.1, by omega⟩
  · intro h
    exact ⟨h.1, by omega⟩

private theorem windowCount_eq_restrictions {N k : ℕ} {i j : Fin N} (hij : i < j) :
    windowCount N k i j =
      (univ.filter fun σ : Equiv.Perm (Fin N) =>
        embeddingWindowHas (k := k) (restrictWindow i j σ)).card := by
  classical
  unfold windowCount
  apply congrArg Finset.card
  ext σ
  simp only [mem_filter, mem_univ, true_and]
  rw [embeddingWindowHas]
  rw [← card_window_eq_card_restrict hij σ]
  simp [restrictWindow, windowEmbedding_zero, windowEmbedding_last hij]

/-- Exact count of permutations with an oriented window containing `k` intermediate points.

For `i < j` and `k < j - i`, multiplying the count by the number of ordered distinct
endpoint ranks gives the total number of permutations times the number of admissible lower
endpoint ranks. -/
theorem windowCount_spec (N k : ℕ) {i j : Fin N} (hij : i < j)
    (hk : k < (j : ℕ) - i) :
    ((j : ℕ) - i) * ((j : ℕ) - i + 1) * windowCount N k i j =
      N.factorial * ((j : ℕ) - i - k) := by
  classical
  let d := (j : ℕ) - i
  have hd : 0 < d := by omega
  let Emb := Fin (d + 1) ↪ Fin N
  let embGood := (univ.filter fun f : Emb => embeddingWindowHas (k := k) f).card
  let permGood := (univ.filter fun τ : Equiv.Perm (Fin (d + 1)) =>
    let p := endpoints hd τ
    p.1.1 < p.1.2 ∧ (p.1.2 : ℕ) - p.1.1 = k + 1).card
  let endpointGood := (univ.filter fun p : EndpointPair d =>
    p.1.1 < p.1.2 ∧ (p.1.2 : ℕ) - p.1.1 = k + 1).card
  have hrestrict : Fintype.card Emb * windowCount N k i j = N.factorial * embGood := by
    have h := restriction_uniformFiber_ratio
      (i := i) (j := j) (fun f => embeddingWindowHas (k := k) f)
    rw [← windowCount_eq_restrictions hij] at h
    simpa [d, Emb, embGood] using h
  have hpattern : (d + 1).factorial * embGood = Fintype.card Emb * permGood := by
    have h := pattern_uniformFiber_ratio (α := Fin N)
      (fun τ : Equiv.Perm (Fin (d + 1)) =>
        let p := endpoints hd τ
        p.1.1 < p.1.2 ∧ (p.1.2 : ℕ) - p.1.1 = k + 1)
    have hfilter :
        (univ.filter fun f : Emb =>
          let p := endpoints hd (pattern f)
          p.1.1 < p.1.2 ∧ (p.1.2 : ℕ) - p.1.1 = k + 1).card = embGood := by
      apply congrArg Finset.card
      ext f
      simp only [mem_filter, mem_univ, true_and]
      simpa [endpointHasGap] using (embeddingWindowHas_iff_endpointHasGap (k := k) hd f).symm
    rw [hfilter] at h
    simpa [Emb, permGood] using h
  have hendpoints : d * (d + 1) * permGood = (d + 1).factorial * endpointGood := by
    simpa [permGood, endpointGood] using
      endpoints_uniformFiber_ratio hd (fun p : EndpointPair d =>
        p.1.1 < p.1.2 ∧ (p.1.2 : ℕ) - p.1.1 = k + 1)
  have hendpointCard : endpointGood = d - k := by
    dsimp only [endpointGood]
    exact card_goodEndpointPairs hk
  have : Nonempty Emb := ⟨windowEmbedding i j⟩
  have hpositive : 0 < Fintype.card Emb * (d + 1).factorial :=
    Nat.mul_pos Fintype.card_pos (Nat.factorial_pos _)
  have hbig :
      (Fintype.card Emb * (d + 1).factorial) *
          (d * (d + 1) * windowCount N k i j) =
        (Fintype.card Emb * (d + 1).factorial) * (N.factorial * (d - k)) := by
    calc
      _ = d * (d + 1) * (d + 1).factorial *
          (Fintype.card Emb * windowCount N k i j) := by ring
      _ = d * (d + 1) * (d + 1).factorial * (N.factorial * embGood) := by
        rw [hrestrict]
      _ = N.factorial * d * (d + 1) * ((d + 1).factorial * embGood) := by ring
      _ = N.factorial * d * (d + 1) * (Fintype.card Emb * permGood) := by
        rw [hpattern]
      _ = N.factorial * Fintype.card Emb * (d * (d + 1) * permGood) := by ring
      _ = N.factorial * Fintype.card Emb * ((d + 1).factorial * endpointGood) := by
        rw [hendpoints]
      _ = (Fintype.card Emb * (d + 1).factorial) *
          (N.factorial * (d - k)) := by rw [hendpointCard]; ring
  simpa [d] using Nat.eq_of_mul_eq_mul_left hpositive hbig

private theorem twoOrder_lt_iff {N : ℕ} (σ : Equiv.Perm (Fin N))
    (i j : TwoOrder σ) :
    i < j ↔ (show Fin N from i) < (show Fin N from j) ∧
      σ (show Fin N from i) < σ (show Fin N from j) := by
  change ((show Fin N from i) ≤ (show Fin N from j) ∧
      σ (show Fin N from i) ≤ σ (show Fin N from j)) ∧
      ¬ ((show Fin N from j) ≤ (show Fin N from i) ∧
        σ (show Fin N from j) ≤ σ (show Fin N from i)) ↔ _
  constructor
  · intro h
    have hij : (show Fin N from i) ≠ (show Fin N from j) := by
      intro heq
      apply h.2
      exact ⟨heq.ge, by rw [heq]⟩
    exact ⟨lt_of_le_of_ne h.1.1 hij, lt_of_le_of_ne h.1.2 (σ.injective.ne hij)⟩
  · intro h
    exact ⟨⟨h.1.le, h.2.le⟩, fun hji => (not_le_of_gt h.1) hji.1⟩

private theorem intervalCard_twoOrder {N : ℕ} (σ : Equiv.Perm (Fin N)) (i j : Fin N) :
    intervalCard (α := TwoOrder σ) i j =
      (univ.filter fun t : Fin N =>
        i < t ∧ t < j ∧ σ i < σ t ∧ σ t < σ j).card := by
  let i' : TwoOrder σ := i
  let j' : TwoOrder σ := j
  change (alexandrovInterval i' j').card =
    ((univ : Finset (TwoOrder σ)).filter fun t =>
      (show Fin N from i') < (show Fin N from t) ∧
      (show Fin N from t) < (show Fin N from j') ∧
      σ (show Fin N from i') < σ (show Fin N from t) ∧
      σ (show Fin N from t) < σ (show Fin N from j')).card
  apply congrArg Finset.card
  ext t
  rw [mem_alexandrovInterval]
  constructor
  · intro h
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    have h₁ := (twoOrder_lt_iff σ i' t).mp h.1
    have h₂ := (twoOrder_lt_iff σ t j').mp h.2
    exact ⟨h₁.1, h₂.1, h₁.2, h₂.2⟩
  · intro h
    have hp := (mem_filter.mp h).2
    exact ⟨(twoOrder_lt_iff σ i' t).mpr ⟨hp.1, hp.2.2.1⟩,
      (twoOrder_lt_iff σ t j').mpr ⟨hp.2.1, hp.2.2.2⟩⟩

private theorem intervalAbundance_twoOrder {N k : ℕ} (σ : Equiv.Perm (Fin N)) :
    intervalAbundance (TwoOrder σ) k =
      (univ.filter fun p : Fin N × Fin N =>
        p.1 < p.2 ∧ σ p.1 < σ p.2 ∧
          (univ.filter fun t : Fin N =>
            p.1 < t ∧ t < p.2 ∧ σ p.1 < σ t ∧ σ t < σ p.2).card = k).card := by
  unfold intervalAbundance
  change ((univ : Finset (Fin N × Fin N)).filter fun p =>
    (show TwoOrder σ from p.1) < (show TwoOrder σ from p.2) ∧
      intervalCard (α := TwoOrder σ) p.1 p.2 = k).card = _
  apply congrArg Finset.card
  ext p
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    have hlt := (twoOrder_lt_iff σ
      (show TwoOrder σ from p.1) (show TwoOrder σ from p.2)).mp h.1
    rw [intervalCard_twoOrder] at h
    exact ⟨hlt.1, hlt.2, h.2⟩
  · intro h
    have hlt := (twoOrder_lt_iff σ
      (show TwoOrder σ from p.1) (show TwoOrder σ from p.2)).mpr ⟨h.1, h.2.1⟩
    rw [intervalCard_twoOrder]
    exact ⟨hlt, h.2.2⟩

private theorem sum_intervalAbundance_eq_sum_windowCount (N k : ℕ) :
    ∑ σ : Equiv.Perm (Fin N), intervalAbundance (TwoOrder σ) k =
      ∑ p ∈ (univ.filter fun p : Fin N × Fin N => p.1 < p.2),
        windowCount N k p.1 p.2 := by
  classical
  simp_rw [intervalAbundance_twoOrder, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm (s := (univ : Finset (Equiv.Perm (Fin N))))
    (t := (univ : Finset (Fin N × Fin N)))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [windowCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  by_cases hlt : p.1 < p.2
  · simp only [true_and, hlt, ite_true]
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  · simp [hlt]

private theorem twice_card_perm_lt {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    2 * (univ.filter fun σ : Equiv.Perm (Fin N) => σ i < σ j).card = N.factorial := by
  classical
  let swapInputs := precompPerm (Equiv.swap i j)
  have hsymm :
      (univ.filter fun σ : Equiv.Perm (Fin N) => σ i < σ j).card =
        (univ.filter fun σ : Equiv.Perm (Fin N) => σ j < σ i).card := by
    apply card_filter_congr
      (fun σ : Equiv.Perm (Fin N) => σ i < σ j)
      (fun σ : Equiv.Perm (Fin N) => σ j < σ i)
      swapInputs
    intro σ
    simp [swapInputs, precompPerm]
  have hnot :
      (univ.filter fun σ : Equiv.Perm (Fin N) => ¬σ i < σ j).card =
        (univ.filter fun σ : Equiv.Perm (Fin N) => σ j < σ i).card := by
    apply congrArg Finset.card
    ext σ
    simp only [mem_filter, mem_univ, true_and]
    have hne : σ i ≠ σ j := σ.injective.ne hij
    omega
  calc
    2 * (univ.filter fun σ : Equiv.Perm (Fin N) => σ i < σ j).card =
        (univ.filter fun σ : Equiv.Perm (Fin N) => σ i < σ j).card +
          (univ.filter fun σ : Equiv.Perm (Fin N) => σ j < σ i).card := by
      omega
    _ = (univ.filter fun σ : Equiv.Perm (Fin N) => σ i < σ j).card +
          (univ.filter fun σ : Equiv.Perm (Fin N) => ¬σ i < σ j).card := by rw [hnot]
    _ = Fintype.card (Equiv.Perm (Fin N)) := card_filter_add_card_filter_not _
    _ = N.factorial := by
      simp only [Fintype.card_perm, Fintype.card_fin]

private theorem relationCount_twoOrder {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (univ.filter fun p : TwoOrder σ × TwoOrder σ => p.1 < p.2).card =
      (univ.filter fun p : Fin N × Fin N => p.1 < p.2 ∧ σ p.1 < σ p.2).card := by
  apply congrArg Finset.card
  ext p
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    exact mem_filter.mpr ⟨mem_univ _, (twoOrder_lt_iff σ p.1 p.2).mp h⟩
  · intro h
    exact (twoOrder_lt_iff σ p.1 p.2).mpr (mem_filter.mp h).2

private theorem sum_relations_eq_sum_perm_lt (N : ℕ) :
    ∑ σ : Equiv.Perm (Fin N),
        (univ.filter fun p : TwoOrder σ × TwoOrder σ => p.1 < p.2).card =
      ∑ p ∈ (univ.filter fun p : Fin N × Fin N => p.1 < p.2),
        (univ.filter fun σ : Equiv.Perm (Fin N) => σ p.1 < σ p.2).card := by
  classical
  simp_rw [relationCount_twoOrder]
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm (s := (univ : Finset (Equiv.Perm (Fin N))))
    (t := (univ : Finset (Fin N × Fin N)))]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hlt : p.1 < p.2 <;> simp [hlt]

private abbrev StrictPair (N : ℕ) :=
  {p : Fin N × Fin N // p.1 < p.2}

private abbrev WindowParameter (N : ℕ) :=
  Σ r : Fin (N - 1), Fin (N - (r + 1))

/-- A strict pair is equivalently a positive separation and a valid lower endpoint. -/
private def strictPairEquivWindowParameter (N : ℕ) :
    StrictPair N ≃ WindowParameter N where
  toFun p := ⟨⟨(p.1.2 : ℕ) - p.1.1 - 1, by
    have hp := p.property
    have hj := p.1.2.isLt
    change (p.1.2 : ℕ) - p.1.1 - 1 < N - 1
    omega⟩, ⟨p.1.1, by
      have hp := p.property
      have hj := p.1.2.isLt
      change (p.1.1 : ℕ) < N - ((p.1.2 : ℕ) - p.1.1 - 1 + 1)
      omega⟩⟩
  invFun q := ⟨(⟨q.2, by
    have hq := q.2.isLt
    have hr := q.1.isLt
    omega⟩, ⟨q.2 + q.1.1 + 1, by
      have hq := q.2.isLt
      have hr := q.1.isLt
      omega⟩), by
        change (q.2 : ℕ) < (q.2 : ℕ) + (q.1 : ℕ) + 1
        omega⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · rfl
    · change (p.1.1 : ℕ) + ((p.1.2 : ℕ) - p.1.1 - 1) + 1 = p.1.2
      have hp := p.property
      omega
  right_inv q := by
    rcases q with ⟨r, i⟩
    apply Sigma.ext
    · apply Fin.ext
      simp
      omega
    · have hri : (i : ℕ) + (r : ℕ) + 1 - i - 1 = r := by omega
      apply (Fin.heq_ext_iff (by
        change N - (((i : ℕ) + (r : ℕ) + 1 - i - 1) + 1) = N - ((r : ℕ) + 1)
        rw [hri])).2
      rfl

private theorem sum_strictPairs_by_distance (N : ℕ) (g : ℕ → ℚ) :
    ∑ p ∈ (univ.filter fun p : Fin N × Fin N => p.1 < p.2),
        g ((p.2 : ℕ) - p.1) =
      ∑ d ∈ Ioo 0 N, (N - d : ℚ) * g d := by
  classical
  let s := univ.filter fun p : Fin N × Fin N => p.1 < p.2
  let attachEquiv : {p // p ∈ s} ≃ StrictPair N := {
    toFun p := ⟨p, (mem_filter.mp p.property).2⟩
    invFun p := ⟨p, mem_filter.mpr ⟨mem_univ _, p.property⟩⟩
    left_inv p := by rfl
    right_inv p := by rfl }
  calc
    ∑ p ∈ s, g ((p.2 : ℕ) - p.1) =
        ∑ p : StrictPair N, g ((p.1.2 : ℕ) - p.1.1) := by
          rw [← s.sum_attach, s.attach_eq_univ]
          apply Fintype.sum_equiv attachEquiv
          intro p
          rfl
    _ = ∑ q : WindowParameter N, g (q.1.1 + 1) := by
      apply Fintype.sum_equiv (strictPairEquivWindowParameter N)
      intro p
      have hp := p.property
      change (p.1.1 : ℕ) < p.1.2 at hp
      change g ((p.1.2 : ℕ) - p.1.1) =
        g (((p.1.2 : ℕ) - p.1.1 - 1) + 1)
      congr 1
      omega
    _ = ∑ r : Fin (N - 1), ∑ _i : Fin (N - (r + 1)), g (r + 1) := by
      rw [Fintype.sum_sigma]
    _ = ∑ r : Fin (N - 1), (N - (r + 1) : ℚ) * g (r + 1) := by
      apply Finset.sum_congr rfl
      intro r hr
      calc
        ∑ _i : Fin (N - (r + 1)), g (r + 1) =
            (N - ((r : ℕ) + 1) : ℕ) * g (r + 1) := by simp
        _ = (N - (r + 1) : ℚ) * g (r + 1) := by
          have hr' := r.isLt
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
    _ = ∑ r ∈ range (N - 1), (N - (r + 1) : ℚ) * g (r + 1) := by
      simpa using Fin.sum_univ_eq_sum_range
        (fun r : ℕ => (N - (r + 1) : ℚ) * g (r + 1)) (N - 1)
    _ = ∑ d ∈ Ioo 0 N, (N - d : ℚ) * g d := by
      apply Finset.sum_bij (fun r _ => r + 1)
      · intro r hr
        simp only [mem_range] at hr
        apply mem_Ioo.mpr
        omega
      · intro r₁ hr₁ r₂ hr₂ h
        omega
      · intro d hd
        have hd' := mem_Ioo.mp hd
        refine ⟨d - 1, mem_range.mpr (by omega), by omega⟩
      · intro r hr
        norm_num

private theorem windowCount_eq_zero_of_distance_le {N k : ℕ} {i j : Fin N}
    (hij : i < j) (hki : (j : ℕ) - i ≤ k) : windowCount N k i j = 0 := by
  classical
  unfold windowCount
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro σ hσ hgood
  let interior := univ.filter fun t : Fin N =>
    i < t ∧ t < j ∧ σ i < σ t ∧ σ t < σ j
  have hsub : interior ⊆ Ioo i j := by
    intro t ht
    have h := (mem_filter.mp ht).2
    exact mem_Ioo.mpr ⟨h.1, h.2.1⟩
  have hcard := card_le_card hsub
  rw [Fin.card_Ioo] at hcard
  change _ ∧ interior.card = k at hgood
  have hkcard : k ≤ (j : ℕ) - i - 1 := hgood.2 ▸ hcard
  have hklt : k < (j : ℕ) - i := by omega
  exact (not_lt_of_ge hki hklt).elim

private theorem windowCount_cast {N k : ℕ} {i j : Fin N} (hij : i < j)
    (hk : k < (j : ℕ) - i) :
    (windowCount N k i j : ℚ) =
      N.factorial * (((j : ℕ) - i : ℚ) - k) /
        (((j : ℕ) - i) * ((j : ℕ) - i + 1)) := by
  have h := windowCount_spec N k hij hk
  have hdNat : 0 < (j : ℕ) - i := by omega
  have hcast : (((j : ℕ) - i : ℕ) : ℚ) = (j : ℚ) - i := by
    rw [Nat.cast_sub (by omega)]
  have hd : (0 : ℚ) < (j : ℕ) - i := by
    rw [← hcast]
    exact_mod_cast hdNat
  have hden : (((j : ℕ) - i : ℚ) * ((j : ℕ) - i + 1)) ≠ 0 :=
    mul_ne_zero (ne_of_gt hd) (ne_of_gt (add_pos hd (by norm_num)))
  apply (eq_div_iff hden).2
  have hc := congrArg (fun n : ℕ => (n : ℚ)) h
  push_cast at hc
  rw [Nat.cast_sub hk.le] at hc
  rw [hcast] at hc
  calc
    (windowCount N k i j : ℚ) *
        (((j : ℕ) - i : ℚ) * ((j : ℕ) - i + 1)) =
      (((j : ℕ) - i : ℚ) * ((j : ℕ) - i + 1)) * windowCount N k i j := by ring
    _ = N.factorial * (((j : ℕ) - i : ℚ) - k) := hc

private theorem sum_intervalAbundance_twoOrder_finite (N k : ℕ) :
    ∑ σ : Equiv.Perm (Fin N), (intervalAbundance (TwoOrder σ) k : ℚ) =
      N.factorial * ∑ d ∈ Ioo k N,
        (N - d : ℚ) * (d - k) / (d * (d + 1)) := by
  classical
  have hNat := sum_intervalAbundance_eq_sum_windowCount N k
  have hcast := congrArg (fun n : ℕ => (n : ℚ)) hNat
  rw [← Nat.cast_sum]
  rw [hcast]
  rw [Nat.cast_sum]
  let g : ℕ → ℚ := fun d => if k < d then
    N.factorial * (d - k : ℚ) / (d * (d + 1)) else 0
  have hpoint : ∀ p : Fin N × Fin N, p ∈ univ.filter (fun p => p.1 < p.2) →
      (windowCount N k p.1 p.2 : ℚ) = g ((p.2 : ℕ) - p.1) := by
    intro p hp
    have hlt := (mem_filter.mp hp).2
    by_cases hk : k < (p.2 : ℕ) - p.1
    · rw [windowCount_cast hlt hk]
      simp only [g]
      rw [Nat.cast_sub hlt.le]
      simp [hk]
    · rw [windowCount_eq_zero_of_distance_le hlt (by omega)]
      simp [g, hk]
  calc
    ∑ p ∈ univ.filter (fun p : Fin N × Fin N => p.1 < p.2),
        (windowCount N k p.1 p.2 : ℚ) =
      ∑ p ∈ univ.filter (fun p : Fin N × Fin N => p.1 < p.2),
        g ((p.2 : ℕ) - p.1) := by
          apply Finset.sum_congr rfl
          exact hpoint
    _ = ∑ d ∈ Ioo 0 N, (N - d : ℚ) * g d := sum_strictPairs_by_distance N g
    _ = ∑ d ∈ Ioo k N,
        (N - d : ℚ) * (N.factorial * (d - k) / (d * (d + 1))) := by
      have hfilter : (Ioo 0 N).filter (fun d => k < d) = Ioo k N := by
        ext d
        simp only [mem_filter, mem_Ioo]
        omega
      rw [← hfilter, sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hkd : k < d <;> simp [g, hkd]
    _ = N.factorial * ∑ d ∈ Ioo k N,
        (N - d : ℚ) * (d - k) / (d * (d + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

private theorem sum_inv_succ_Ioo {N k : ℕ} (hk : k < N) :
    ∑ d ∈ Ioo k N, ((d + 1 : ℕ) : ℚ)⁻¹ = harmonic N - harmonic (k + 1) := by
  have hrange := Finset.sum_range_add_sum_Ico
    (f := fun d : ℕ => (((d + 1 : ℕ) : ℚ)⁻¹)) (Nat.succ_le_iff.mpr hk)
  have hfinset : Ioo k N = Ico (k + 1) N := by
    ext d
    simp only [mem_Ioo, mem_Ico]
    omega
  rw [hfinset]
  unfold harmonic
  linarith

private theorem sum_inv_Ioo {N k : ℕ} (hk : k < N) :
    ∑ d ∈ Ioo k N, ((d : ℚ)⁻¹) = harmonic (N - 1) - harmonic k := by
  have hk' : k ≤ N - 1 := by omega
  have hrange := Finset.sum_range_add_sum_Ico
    (f := fun d : ℕ => (((d + 1 : ℕ) : ℚ)⁻¹)) hk'
  have hshift : ∑ d ∈ Ioo k N, ((d : ℚ)⁻¹) =
      ∑ r ∈ Ico k (N - 1), (((r + 1 : ℕ) : ℚ)⁻¹) := by
    apply Finset.sum_bij (fun d _ => d - 1)
    · intro d hd
      have h := mem_Ioo.mp hd
      apply mem_Ico.mpr
      omega
    · intro d₁ hd₁ d₂ hd₂ heq
      have h₁ := mem_Ioo.mp hd₁
      have h₂ := mem_Ioo.mp hd₂
      omega
    · intro r hr
      have h := mem_Ico.mp hr
      refine ⟨r + 1, mem_Ioo.mpr (by omega), by omega⟩
    · intro d hd
      have h := mem_Ioo.mp hd
      congr 2
      omega
  rw [hshift]
  unfold harmonic
  linarith

private theorem rational_window_sum {N k : ℕ} (hk : k < N) :
    ∑ d ∈ Ioo k N, (N - d : ℚ) * (d - k) / (d * (d + 1)) =
      -(N - k - 1 : ℕ) - N * k * (harmonic (N - 1) - harmonic k) +
        (N + 1) * (k + 1) * (harmonic N - harmonic (k + 1)) := by
  have hterm : ∀ d ∈ Ioo k N,
      (N - d : ℚ) * (d - k) / (d * (d + 1)) =
        -1 - N * k * (d : ℚ)⁻¹ + (N + 1) * (k + 1) * ((d + 1 : ℕ) : ℚ)⁻¹ := by
    intro d hd
    have hdpos : 0 < d := by have := (mem_Ioo.mp hd).1; omega
    field_simp
    push_cast
    ring
  calc
    ∑ d ∈ Ioo k N, (N - d : ℚ) * (d - k) / (d * (d + 1)) =
        ∑ d ∈ Ioo k N,
          (-1 - N * k * (d : ℚ)⁻¹ +
            (N + 1) * (k + 1) * ((d + 1 : ℕ) : ℚ)⁻¹) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = -(N - k - 1 : ℕ) - N * k * (harmonic (N - 1) - harmonic k) +
        (N + 1) * (k + 1) * (harmonic N - harmonic (k + 1)) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [sum_inv_Ioo hk, sum_inv_succ_Ioo hk]
      simp

private theorem rational_window_sum_closed {N k : ℕ} (hk : k < N) :
    ∑ d ∈ Ioo k N, (N - d : ℚ) * (d - k) / (d * (d + 1)) =
      (N + k + 1) * (harmonic N - harmonic (k + 1)) - 2 * N + 2 * k + 1 +
        N / (k + 1) := by
  have hNpos : 0 < N := (Nat.zero_le k).trans_lt hk
  have hN : harmonic (N - 1) = harmonic N - (N : ℚ)⁻¹ := by
    have hsucc := harmonic_succ (N - 1)
    rw [show N - 1 + 1 = N by omega] at hsucc
    linarith
  have hk' := harmonic_succ k
  rw [rational_window_sum hk, hN, hk']
  have hlen : ((N - k - 1 : ℕ) : ℚ) = (N : ℚ) - k - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNpos)
  have hk0 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [hlen]
  field_simp
  push_cast
  ring

/-- Closed harmonic-number form of the `k`th interval-abundance sum when `k < N`. -/
theorem sum_intervalAbundance_twoOrder_closed (N k : ℕ) (hk : k < N) :
    ∑ σ : Equiv.Perm (Fin N), (intervalAbundance (TwoOrder σ) k : ℚ) =
      N.factorial *
        ((N + k + 1) * (harmonic N - harmonic (k + 1)) - 2 * N + 2 * k + 1 +
          N / (k + 1)) := by
  rw [sum_intervalAbundance_twoOrder_finite, rational_window_sum_closed hk]

/-- Exact permutation sum of the `k`th interval abundance for finite two-orders.

The identity is a finite rational equality. It makes no probabilistic or continuum-limit claim. -/
theorem sum_intervalAbundance_twoOrder (N k : ℕ) :
    ∑ σ : Equiv.Perm (Fin N), (intervalAbundance (TwoOrder σ) k : ℚ) =
      N.factorial * ∑ d ∈ (range N).filter (k < ·),
        (((N - d) * (d - k) : ℕ) : ℚ) / (d * (d + 1)) := by
  rw [sum_intervalAbundance_twoOrder_finite]
  congr 1
  have hfinset : (range N).filter (k < ·) = Ioo k N := by
    ext d
    simp only [mem_filter, mem_range, mem_Ioo]
    omega
  rw [hfinset]
  apply Finset.sum_congr rfl
  intro d hd
  have h := mem_Ioo.mp hd
  rw [Nat.cast_mul, Nat.cast_sub h.2.le, Nat.cast_sub h.1.le]

/-- Exact permutation sum of the number of links in finite two-orders. -/
theorem sum_links_twoOrder (N : ℕ) :
    ∑ σ : Equiv.Perm (Fin N),
        ((univ.filter fun p : TwoOrder σ × TwoOrder σ => IsLink p.1 p.2).card : ℚ) =
      N.factorial * ((N + 1) * harmonic N - 2 * N) := by
  simp_rw [← intervalAbundance_zero]
  obtain rfl | hN := N.eq_zero_or_pos
  · simp [intervalAbundance, TwoOrder]
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact Fin.elim0 p.1
  · rw [sum_intervalAbundance_twoOrder_closed N 0 hN]
    rw [show harmonic (0 + 1) = 1 by norm_num [harmonic_succ]]
    norm_num
    ring_nf
    simp [Nat.factorial_ne_zero]

/-- Exact permutation sum of strict relations, equivalently the ordering fraction `1/2`. -/
theorem sum_relations_twoOrder (N : ℕ) :
    ∑ σ : Equiv.Perm (Fin N),
        ((univ.filter fun p : TwoOrder σ × TwoOrder σ => p.1 < p.2).card : ℚ) =
      N.factorial * (N.choose 2 / 2 : ℚ) := by
  have hNat := sum_relations_eq_sum_perm_lt N
  have hcast := congrArg (fun n : ℕ => (n : ℚ)) hNat
  rw [← Nat.cast_sum]
  rw [hcast]
  push_cast
  have hpoint : ∀ p : Fin N × Fin N, p ∈ univ.filter (fun p => p.1 < p.2) →
      ((univ.filter fun σ : Equiv.Perm (Fin N) => σ p.1 < σ p.2).card : ℚ) =
        N.factorial / 2 := by
    intro p hp
    have hlt := (mem_filter.mp hp).2
    have h := twice_card_perm_lt (ne_of_lt hlt)
    have hc := congrArg (fun n : ℕ => (n : ℚ)) h
    push_cast at hc
    linarith
  have hsum : ∑ d ∈ Ioo 0 N, (N - d : ℚ) = (N.choose 2 : ℚ) := by
    obtain rfl | hN := N.eq_zero_or_pos
    · simp
    · have hrev : ∑ d ∈ Ioo 0 N, (N - d : ℚ) = ∑ d ∈ Ioo 0 N, (d : ℚ) := by
        apply Finset.sum_bij (fun d _ => N - d)
        · intro d hd
          have h := mem_Ioo.mp hd
          apply mem_Ioo.mpr
          omega
        · intro d₁ hd₁ d₂ hd₂ heq
          have h₁ := mem_Ioo.mp hd₁
          have h₂ := mem_Ioo.mp hd₂
          omega
        · intro d hd
          have h := mem_Ioo.mp hd
          refine ⟨N - d, mem_Ioo.mpr (by omega), by omega⟩
        · intro d hd
          have h := mem_Ioo.mp hd
          rw [Nat.cast_sub h.2.le]
      rw [hrev]
      have hset : Ioo 0 N = (range N).erase 0 := by
        ext d
        simp only [mem_Ioo, mem_erase, mem_range]
        omega
      rw [hset]
      simp only [sum_erase, Nat.cast_zero]
      rw [Nat.choose_two_right]
      rw [← Nat.cast_sum]
      exact_mod_cast Finset.sum_range_id N
  calc
    ∑ p ∈ univ.filter (fun p : Fin N × Fin N => p.1 < p.2),
        ((univ.filter fun σ : Equiv.Perm (Fin N) => σ p.1 < σ p.2).card : ℚ) =
      ∑ p ∈ univ.filter (fun p : Fin N × Fin N => p.1 < p.2),
        (N.factorial : ℚ) / 2 := by
          apply Finset.sum_congr rfl
          exact hpoint
    _ = ∑ d ∈ Ioo 0 N, (N - d : ℚ) * ((N.factorial : ℚ) / 2) :=
      sum_strictPairs_by_distance N (fun _ => (N.factorial : ℚ) / 2)
    _ = N.factorial * (N.choose 2 / 2 : ℚ) := by rw [← Finset.sum_mul, hsum]; ring

/-- The permutation sum of the two-dimensional Benincasa--Dowker combination is exactly `N!`
for every nonempty two-order. -/
theorem sum_bdCombination2_twoOrder {N : ℕ} (hN : 1 ≤ N) :
    ∑ σ : Equiv.Perm (Fin N), bdCombination2 (TwoOrder σ) = (N.factorial : ℤ) := by
  by_cases hsmall : N < 3
  · have hcases : N = 1 ∨ N = 2 := by omega
    rcases hcases with rfl | rfl <;> decide
  · have h0 := sum_intervalAbundance_twoOrder_closed N 0 (by omega)
    have h1 := sum_intervalAbundance_twoOrder_closed N 1 (by omega)
    have h2 := sum_intervalAbundance_twoOrder_closed N 2 (by omega)
    have hcard : ∀ σ : Equiv.Perm (Fin N), Fintype.card (TwoOrder σ) = N := by
      intro σ
      let e : TwoOrder σ ≃ Fin N := Equiv.refl _
      simpa using Fintype.card_congr e
    apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
    push_cast
    simp_rw [bdCombination2]
    push_cast
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [hcard]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [Finset.sum_const, card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul]
    rw [h0, h1, h2]
    norm_num [harmonic_succ] at h0 h1 h2 ⊢
    ring

end RandomTwoOrder

end CausalSet
