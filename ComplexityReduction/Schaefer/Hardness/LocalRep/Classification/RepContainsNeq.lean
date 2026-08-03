/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Schaefer.Hardness.LocalRep.SAT.LogicalRelation
import ComplexityReduction.Schaefer.Hardness.LocalRep.Closure.Operations
import ComplexityReduction.Schaefer.Hardness.LocalRep.Closure.Rep
import ComplexityReduction.Schaefer.Hardness.LocalRep.Classification.WeakChar
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

namespace ComplexityReduction.Schaefer.Hardness.LocalRep

open LogRel

/-! ## Lemma 3.2: Disequality in Rep(S)

If S contains a relation that is neither weakly positive nor weakly negative,
then the disequality relation [x ≠ y] ∈ Rep(S).

This is a key step in Schaefer's classification: from ¬WP and ¬WN, we can
construct disequality, which then allows negated substitution.
-/

/-! ## Auxiliary Constructions for Lemma 3.2

These lemmas construct specific binary relations from witnesses of ¬WP and ¬WN.
-/

/-- From ¬WP witness, we can construct a binary projection that is not
    closed under AND (via substitution and quantification). -/
theorem binary_not_wp_of_not_wp {k : Nat} {R : LogRel k}
    (hNotWP : ¬ IsWeaklyPositive R) (_hk : 2 ≤ k) :
    ∃ (R' : LogRel 2), ∃ (π : Fin k → Fin 2 ⊕ Bool),
      substitute R π = R' ∧ ¬ IsWeaklyPositive R' := by
  obtain ⟨f, g, hf, hg, hfg⟩ := not_wp_iff.mp hNotWP
  set π : Fin k → Fin 2 ⊕ Bool := fun i =>
    if f i = true ∧ g i = false then Sum.inl ⟨0, by omega⟩
    else if f i = false ∧ g i = true then Sum.inl ⟨1, by omega⟩
    else Sum.inr (f i) with hπ_def
  have hπ : ∀ i, π i = (if f i = true ∧ g i = false then Sum.inl ⟨0, by omega⟩
    else if f i = false ∧ g i = true then Sum.inl ⟨1, by omega⟩
    else Sum.inr (f i)) := fun i => rfl
  have eq_f : substApply π (fun i : Fin 2 => if i.val = 0 then true else false) = f := by
    funext i; unfold substApply; rw [hπ]
    split_ifs with h1 h2 <;> simp_all
  have eq_g : substApply π (fun i : Fin 2 => if i.val = 0 then false else true) = g := by
    funext i; unfold substApply; rw [hπ]
    split_ifs with h1 h2
    · simp_all
    · simp_all
    · cases hfi : f i <;> simp_all
  have eq_fg : substApply π (fun _ : Fin 2 => false) = pointwiseAnd f g := by
    funext i; unfold substApply; rw [hπ]; unfold pointwiseAnd
    split_ifs with h1 h2
    · simp_all
    · simp_all
    · cases hfi : f i <;> simp_all
  exact ⟨substitute R π, π, rfl, by
    rw [not_wp_iff]
    exact ⟨_, _, by rw [mem_substitute, eq_f]; exact hf,
      by rw [mem_substitute, eq_g]; exact hg,
      by rw [mem_substitute]
         have harg : pointwiseAnd (fun i : Fin 2 => if i.val = 0 then true else false)
           (fun i : Fin 2 => if i.val = 0 then false else true) = fun _ => false := by
           native_decide
         have : substApply π (pointwiseAnd (fun i : Fin 2 => if i.val = 0 then true else false)
           (fun i : Fin 2 => if i.val = 0 then false else true)) =
           substApply π (fun _ => false) := congrArg (substApply π) harg
         rw [this, eq_fg]; exact hfg⟩⟩

/-- From ¬WN witness, we can construct a binary projection that is not
    closed under OR (via substitution and quantification). -/
theorem binary_not_wn_of_not_wn {k : Nat} {R : LogRel k}
    (hNotWN : ¬ IsWeaklyNegative R) (_hk : 2 ≤ k) :
    ∃ (R' : LogRel 2), ∃ (π : Fin k → Fin 2 ⊕ Bool),
      substitute R π = R' ∧ ¬ IsWeaklyNegative R' := by
  obtain ⟨f, g, hf, hg, hfg⟩ := not_wn_iff.mp hNotWN
  set π : Fin k → Fin 2 ⊕ Bool := fun i =>
    if f i = false ∧ g i = true then Sum.inl ⟨0, by omega⟩
    else if f i = true ∧ g i = false then Sum.inl ⟨1, by omega⟩
    else Sum.inr (f i) with hπ_def
  have hπ : ∀ i, π i = (if f i = false ∧ g i = true then Sum.inl ⟨0, by omega⟩
    else if f i = true ∧ g i = false then Sum.inl ⟨1, by omega⟩
    else Sum.inr (f i)) := fun i => rfl
  have eq_f : substApply π (fun i : Fin 2 => if i.val = 0 then false else true) = f := by
    funext i; unfold substApply; rw [hπ]
    split_ifs with h1 h2
    · simp_all
    · simp_all
    · cases hfi : f i <;> simp_all
  have eq_g : substApply π (fun i : Fin 2 => if i.val = 0 then true else false) = g := by
    funext i; unfold substApply; rw [hπ]
    split_ifs with h1 h2
    · simp_all
    · simp_all
    · cases hfi : f i <;> simp_all
  have eq_fg : substApply π (fun _ : Fin 2 => true) = pointwiseOr f g := by
    funext i; unfold substApply; rw [hπ]; unfold pointwiseOr
    split_ifs with h1 h2
    · simp_all
    · simp_all
    · cases hfi : f i <;> simp_all
  exact ⟨substitute R π, π, rfl, by
    rw [not_wn_iff]
    exact ⟨_, _, by rw [mem_substitute, eq_f]; exact hf,
      by rw [mem_substitute, eq_g]; exact hg,
      by rw [mem_substitute]
         have harg : pointwiseOr (fun i : Fin 2 => if i.val = 0 then false else true)
           (fun i : Fin 2 => if i.val = 0 then true else false) = fun _ => true := by
           native_decide
         have : substApply π (pointwiseOr (fun i : Fin 2 => if i.val = 0 then false else true)
           (fun i : Fin 2 => if i.val = 0 then true else false)) =
           substApply π (fun _ => true) := congrArg (substApply π) harg
         rw [this, eq_fg]; exact hfg⟩⟩

/-! ## Main Theorems: neq_in_rep_single and neq_in_rep -/

private theorem arity_ge_two_of_not_wp {k : Nat} {R : LogRel k}
    (hNotWP : ¬ IsWeaklyPositive R) : 2 ≤ k := by
  by_contra h
  push Not at h
  apply hNotWP
  intro f g hf hg
  interval_cases k
  · have : f = pointwiseAnd f g := by funext i; exact (i.elim0)
    rw [← this]; exact hf
  · have : pointwiseAnd f g ⟨0, by omega⟩ = f ⟨0, by omega⟩ ∨
           pointwiseAnd f g ⟨0, by omega⟩ = g ⟨0, by omega⟩ := by
      simp only [pointwiseAnd]
      cases hv : f ⟨0, by omega⟩ <;> cases hgv : g ⟨0, by omega⟩ <;> simp_all
    rcases this with h1 | h1
    · have heq : pointwiseAnd f g = f := by funext i; fin_cases i; exact h1
      rw [heq]; exact hf
    · have heq : pointwiseAnd f g = g := by funext i; fin_cases i; exact h1
      rw [heq]; exact hg

private theorem arity_ge_two_of_not_wn {k : Nat} {R : LogRel k}
    (hNotWN : ¬ IsWeaklyNegative R) : 2 ≤ k := by
  by_contra h
  push Not at h
  apply hNotWN
  intro f g hf hg
  interval_cases k
  · have : f = pointwiseOr f g := by funext i; exact (i.elim0)
    rw [← this]; exact hf
  · have : pointwiseOr f g ⟨0, by omega⟩ = f ⟨0, by omega⟩ ∨
           pointwiseOr f g ⟨0, by omega⟩ = g ⟨0, by omega⟩ := by
      simp only [pointwiseOr]
      cases hv : f ⟨0, by omega⟩ <;> cases hgv : g ⟨0, by omega⟩ <;> simp_all
    rcases this with h1 | h1
    · have heq : pointwiseOr f g = f := by funext i; fin_cases i; exact h1
      rw [heq]; exact hf
    · have heq : pointwiseOr f g = g := by funext i; fin_cases i; exact h1
      rw [heq]; exact hg

private theorem binary_intersect_eq (R₁ R₂ : LogRel 2) :
    substitute (conjoin R₁ R₂)
      (fun i : Fin 4 => Sum.inl (⟨i.val % 2, by omega⟩ : Fin 2)) = R₁ ∩ R₂ := by
  ext s
  simp only [mem_substitute, mem_conjoin, Finset.mem_inter]
  constructor
  · intro ⟨hl, hr⟩
    exact ⟨by convert hl using 1; funext i; simp [splitLeft, substApply]; fin_cases i <;> simp,
           by convert hr using 1; funext i; simp [splitRight, substApply]; fin_cases i <;> simp⟩
  · intro ⟨h1, h2⟩
    exact ⟨by convert h1 using 1; funext i; simp [splitLeft, substApply]; fin_cases i <;> simp,
           by convert h2 using 1; funext i; simp [splitRight, substApply]; fin_cases i <;> simp⟩

private theorem neqRel_subset_of_not_wp {R : LogRel 2} (h : ¬ IsWeaklyPositive R) :
    neqRel ⊆ R ∧ (fun _ : Fin 2 => false) ∉ R := by
  obtain ⟨f, g, hf, hg, hfg⟩ := not_wp_iff.mp h
  constructor
  · intro t ht
    rw [mem_neqRel] at ht
    have ht_form : (t ⟨0, by omega⟩ = true ∧ t ⟨1, by omega⟩ = false) ∨
                   (t ⟨0, by omega⟩ = false ∧ t ⟨1, by omega⟩ = true) := by
      cases h0 : t ⟨0, by omega⟩ <;> cases h1 : t ⟨1, by omega⟩ <;> simp_all
    cases hf0 : f ⟨0, by omega⟩ <;> cases hf1 : f ⟨1, by omega⟩ <;>
      cases hg0 : g ⟨0, by omega⟩ <;> cases hg1 : g ⟨1, by omega⟩
    all_goals first
      | (exfalso; apply hfg
         have : pointwiseAnd f g = f := by
           funext i; fin_cases i <;> simp_all [pointwiseAnd]
         rw [this]; exact hf)
      | (exfalso; apply hfg
         have : pointwiseAnd f g = g := by
           funext i; fin_cases i <;> simp_all [pointwiseAnd]
         rw [this]; exact hg)
      | (rcases ht_form with ⟨h0, h1⟩ | ⟨h0, h1⟩
         · have : t = f := by funext i; fin_cases i <;> simp_all
           rw [this]; exact hf
         · have : t = g := by funext i; fin_cases i <;> simp_all
           rw [this]; exact hg)
      | (rcases ht_form with ⟨h0, h1⟩ | ⟨h0, h1⟩
         · have : t = g := by funext i; fin_cases i <;> simp_all
           rw [this]; exact hg
         · have : t = f := by funext i; fin_cases i <;> simp_all
           rw [this]; exact hf)
  · intro hff
    apply hfg
    cases hf0 : f ⟨0, by omega⟩ <;> cases hf1 : f ⟨1, by omega⟩ <;>
      cases hg0 : g ⟨0, by omega⟩ <;> cases hg1 : g ⟨1, by omega⟩
    all_goals first
      | (have : pointwiseAnd f g = (fun _ => false) := by
           funext i; fin_cases i <;> simp_all [pointwiseAnd]
         rw [this]; exact hff)
      | (have : pointwiseAnd f g = f := by
           funext i; fin_cases i <;> simp_all [pointwiseAnd]
         rw [this]; exact hf)
      | (have : pointwiseAnd f g = g := by
           funext i; fin_cases i <;> simp_all [pointwiseAnd]
         rw [this]; exact hg)

private theorem neqRel_subset_of_not_wn {R : LogRel 2} (h : ¬ IsWeaklyNegative R) :
    neqRel ⊆ R ∧ (fun _ : Fin 2 => true) ∉ R := by
  obtain ⟨f, g, hf, hg, hfg⟩ := not_wn_iff.mp h
  constructor
  · intro t ht
    rw [mem_neqRel] at ht
    have ht_form : (t ⟨0, by omega⟩ = true ∧ t ⟨1, by omega⟩ = false) ∨
                   (t ⟨0, by omega⟩ = false ∧ t ⟨1, by omega⟩ = true) := by
      cases h0 : t ⟨0, by omega⟩ <;> cases h1 : t ⟨1, by omega⟩ <;> simp_all
    cases hf0 : f ⟨0, by omega⟩ <;> cases hf1 : f ⟨1, by omega⟩ <;>
      cases hg0 : g ⟨0, by omega⟩ <;> cases hg1 : g ⟨1, by omega⟩
    all_goals first
      | (exfalso; apply hfg
         have : pointwiseOr f g = f := by
           funext i; fin_cases i <;> simp_all [pointwiseOr]
         rw [this]; exact hf)
      | (exfalso; apply hfg
         have : pointwiseOr f g = g := by
           funext i; fin_cases i <;> simp_all [pointwiseOr]
         rw [this]; exact hg)
      | (rcases ht_form with ⟨h0, h1⟩ | ⟨h0, h1⟩
         · have : t = f := by funext i; fin_cases i <;> simp_all
           rw [this]; exact hf
         · have : t = g := by funext i; fin_cases i <;> simp_all
           rw [this]; exact hg)
      | (rcases ht_form with ⟨h0, h1⟩ | ⟨h0, h1⟩
         · have : t = g := by funext i; fin_cases i <;> simp_all
           rw [this]; exact hg
         · have : t = f := by funext i; fin_cases i <;> simp_all
           rw [this]; exact hf)
  · intro htt
    apply hfg
    cases hf0 : f ⟨0, by omega⟩ <;> cases hf1 : f ⟨1, by omega⟩ <;>
      cases hg0 : g ⟨0, by omega⟩ <;> cases hg1 : g ⟨1, by omega⟩
    all_goals first
      | (have : pointwiseOr f g = (fun _ => true) := by
           funext i; fin_cases i <;> simp_all [pointwiseOr]
         rw [this]; exact htt)
      | (have : pointwiseOr f g = f := by
           funext i; fin_cases i <;> simp_all [pointwiseOr]
         rw [this]; exact hf)
      | (have : pointwiseOr f g = g := by
           funext i; fin_cases i <;> simp_all [pointwiseOr]
         rw [this]; exact hg)

private theorem binary_inter_not_wp_not_wn_eq_neq {R₁ R₂ : LogRel 2}
    (h1 : ¬ IsWeaklyPositive R₁) (h2 : ¬ IsWeaklyNegative R₂) :
    R₁ ∩ R₂ = neqRel := by
  obtain ⟨hsub1, hff⟩ := neqRel_subset_of_not_wp h1
  obtain ⟨hsub2, htt⟩ := neqRel_subset_of_not_wn h2
  have h_sub : neqRel ⊆ R₁ ∩ R₂ := by
    intro t ht
    exact Finset.mem_inter.2 ⟨hsub1 ht, hsub2 ht⟩
  have h_sup : R₁ ∩ R₂ ⊆ neqRel := by
    intro t ht
    rw [Finset.mem_inter] at ht
    rw [mem_neqRel]
    intro heq
    cases hv : t ⟨0, by omega⟩
    · have ht_eq : t = fun _ => false := by
        funext i; fin_cases i
        · exact hv
        · have : t ⟨1, by omega⟩ = t ⟨0, by omega⟩ := heq.symm
          rw [hv] at this; exact this
      exact hff (ht_eq ▸ ht.1)
    · have ht_eq : t = fun _ => true := by
        funext i; fin_cases i
        · exact hv
        · have : t ⟨1, by omega⟩ = t ⟨0, by omega⟩ := heq.symm
          rw [hv] at this; exact this
      exact htt (ht_eq ▸ ht.2)
  exact Finset.Subset.antisymm h_sup h_sub

theorem neq_in_rep_single {S : Finset BundledLogRel}
    (R : BundledLogRel) (hR : ↑R ∈ S)
    (hNotWP : ¬ IsWeaklyPositive R.rel) (hNotWN : ¬ IsWeaklyNegative R.rel) :
    InRep S 2 neqRel := by
  have hk : 2 ≤ R.arity := arity_ge_two_of_not_wp hNotWP
  obtain ⟨R₁, π₁, hR₁eq, hR₁_not_wp⟩ := binary_not_wp_of_not_wp hNotWP hk
  obtain ⟨R₂, π₂, hR₂eq, hR₂_not_wn⟩ := binary_not_wn_of_not_wn hNotWN hk
  have hR₁_in_rep : InRep S 2 R₁ := hR₁eq ▸ InRep.subst R.rel π₁ (InRep.base R hR)
  have hR₂_in_rep : InRep S 2 R₂ := hR₂eq ▸ InRep.subst R.rel π₂ (InRep.base R hR)
  have h_eq : substitute (conjoin R₁ R₂)
      (fun i : Fin 4 => Sum.inl (⟨i.val % 2, by omega⟩ : Fin 2)) = neqRel := by
    rw [binary_intersect_eq]
    exact binary_inter_not_wp_not_wn_eq_neq hR₁_not_wp hR₂_not_wn
  rw [← h_eq]
  exact InRep.subst (conjoin R₁ R₂) _ (InRep.conj R₁ R₂ hR₁_in_rep hR₂_in_rep)

theorem neq_in_rep {S : Finset BundledLogRel}
    (R_WP : BundledLogRel) (hWP : ↑R_WP ∈ S) (hNotWP : ¬ IsWeaklyPositive R_WP.rel)
    (R_WN : BundledLogRel) (hWN : ↑R_WN ∈ S) (hNotWN : ¬ IsWeaklyNegative R_WN.rel) :
    InRep S 2 neqRel := by
  have hk_wp : 2 ≤ R_WP.arity := arity_ge_two_of_not_wp hNotWP
  have hk_wn : 2 ≤ R_WN.arity := arity_ge_two_of_not_wn hNotWN
  obtain ⟨R₁, π₁, hR₁eq, hR₁_not_wp⟩ := binary_not_wp_of_not_wp hNotWP hk_wp
  obtain ⟨R₂, π₂, hR₂eq, hR₂_not_wn⟩ := binary_not_wn_of_not_wn hNotWN hk_wn
  have hR₁_in_rep : InRep S 2 R₁ := hR₁eq ▸ InRep.subst R_WP.rel π₁ (InRep.base R_WP hWP)
  have hR₂_in_rep : InRep S 2 R₂ := hR₂eq ▸ InRep.subst R_WN.rel π₂ (InRep.base R_WN hWN)
  have h_eq : substitute (conjoin R₁ R₂)
      (fun i : Fin 4 => Sum.inl (⟨i.val % 2, by omega⟩ : Fin 2)) = neqRel := by
    rw [binary_intersect_eq]
    exact binary_inter_not_wp_not_wn_eq_neq hR₁_not_wp hR₂_not_wn
  rw [← h_eq]
  exact InRep.subst (conjoin R₁ R₂) _ (InRep.conj R₁ R₂ hR₁_in_rep hR₂_in_rep)

end LocalRep
