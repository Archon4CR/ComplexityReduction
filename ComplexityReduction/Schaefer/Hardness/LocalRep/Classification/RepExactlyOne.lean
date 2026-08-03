/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Schaefer.Hardness.LocalRep.SAT.LogicalRelation
import ComplexityReduction.Schaefer.Hardness.LocalRep.Closure.Operations
import ComplexityReduction.Schaefer.Hardness.LocalRep.Closure.Rep
import ComplexityReduction.Schaefer.Hardness.LocalRep.Classification.BijunctiveChar
import ComplexityReduction.Schaefer.Hardness.LocalRep.Classification.RepBinaryRels

namespace ComplexityReduction.Schaefer.Hardness.LocalRep

open LogRel

/-! ## Lemma 3.4: "Exactly One" in Rep(S)

If S contains a relation that is not bijunctive, and both [x≠y] and
all 3-element binary relations are in Rep(S), then the
"exactly one of x,y,z" relation is in Rep(S).
-/

/-! ### Helper: Non-bijunctive relations have arity ≥ 3 -/

set_option maxHeartbeats 800000 in
private theorem maj_in_triple_k1 : ∀ (f g h : Fin 1 → Bool),
    pointwiseMaj f g h = f ∨ pointwiseMaj f g h = g ∨ pointwiseMaj f g h = h := by
  native_decide

set_option maxHeartbeats 800000 in
private theorem maj_in_triple_k2 : ∀ (f g h : Fin 2 → Bool),
    pointwiseMaj f g h = f ∨ pointwiseMaj f g h = g ∨ pointwiseMaj f g h = h := by
  native_decide

private theorem not_bijunctive_arity_ge_3 {k : Nat} {R : LogRel k}
    (hNotBij : ¬ IsBijunctive R) : k ≥ 3 := by
  by_contra hlt
  push Not at hlt
  apply hNotBij
  intro f g h hf hg hh
  interval_cases k
  · have heq : pointwiseMaj f g h = f := funext (fun i : Fin 0 => Fin.elim0 i)
    rw [heq]; exact hf
  · rcases maj_in_triple_k1 f g h with h | h | h <;> rw [h] <;> assumption
  · rcases maj_in_triple_k2 f g h with h | h | h <;> rw [h] <;> assumption

/-! ### Key property: at each position, at most one of f,g,h differs from majority -/

private theorem maj_minority_unique (a b c : Bool) :
    let m := (a && b) || (b && c) || (a && c)
    (a ≠ m → b = m) ∧ (a ≠ m → c = m) ∧ (b ≠ m → c = m) := by
  cases a <;> cases b <;> cases c <;> simp

private theorem maj_diff_positions_disjoint {k : Nat} (f g h : Fin k → Bool) (i : Fin k) :
    f i ≠ pointwiseMaj f g h i → g i = pointwiseMaj f g h i := by
  intro hfi
  have := (maj_minority_unique (f i) (g i) (h i)).1
  simpa [pointwiseMaj] using this (by simpa [pointwiseMaj] using hfi)

private theorem maj_diff_positions_disjoint_fh {k : Nat} (f g h : Fin k → Bool) (i : Fin k) :
    f i ≠ pointwiseMaj f g h i → h i = pointwiseMaj f g h i := by
  intro hfi
  have := (maj_minority_unique (f i) (g i) (h i)).2.1
  simpa [pointwiseMaj] using this (by simpa [pointwiseMaj] using hfi)

private theorem maj_diff_positions_disjoint_gh {k : Nat} (f g h : Fin k → Bool) (i : Fin k) :
    g i ≠ pointwiseMaj f g h i → h i = pointwiseMaj f g h i := by
  intro hgi
  have := (maj_minority_unique (f i) (g i) (h i)).2.2
  simpa [pointwiseMaj] using this (by simpa [pointwiseMaj] using hgi)

/-! ### Witness pattern: three distinct positions -/

private theorem not_bijunctive_witness {k : Nat} {R : LogRel k}
    (hNotBij : ¬ IsBijunctive R) :
    ∃ f g h, f ∈ R ∧ g ∈ R ∧ h ∈ R ∧ pointwiseMaj f g h ∉ R ∧
      ∃ (i j l : Fin k), i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
        f i ≠ pointwiseMaj f g h i ∧
        g j ≠ pointwiseMaj f g h j ∧
        h l ≠ pointwiseMaj f g h l := by
  unfold IsBijunctive at hNotBij
  push Not at hNotBij
  obtain ⟨f, g, h, hf, hg, hh, hmaj⟩ := hNotBij
  refine ⟨f, g, h, hf, hg, hh, hmaj, ?_⟩
  have hfne : f ≠ pointwiseMaj f g h := fun heq => hmaj (heq ▸ hf)
  have hgne : g ≠ pointwiseMaj f g h := fun heq => hmaj (heq ▸ hg)
  have hhne : h ≠ pointwiseMaj f g h := fun heq => hmaj (heq ▸ hh)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hfne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hgne
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hhne
  have hij : i ≠ j := by
    intro heq; subst heq
    exact hj (maj_diff_positions_disjoint f g h i hi)
  have hil : i ≠ l := by
    intro heq; subst heq
    exact hl (maj_diff_positions_disjoint_fh f g h i hi)
  have hjl : j ≠ l := by
    intro heq; subst heq
    exact hl (maj_diff_positions_disjoint_gh f g h j hj)
  exact ⟨i, j, l, hij, hil, hjl, hi, hj, hl⟩

/-! ### Main construction -/

private def nandRel2 : LogRel 2 :=
  Finset.filter (fun t : Fin 2 → Bool => !(t ⟨0, by omega⟩ && t ⟨1, by omega⟩)) Finset.univ

private theorem nandRel2_card : nandRel2.card = 3 := by native_decide

private theorem atMostOne_inter_not_allFalse_eq_exactlyOne (R : LogRel 3)
    (h_tf : (fun i : Fin 3 => i.val == 0) ∈ R)
    (h_ft : (fun i : Fin 3 => i.val == 1) ∈ R)
    (h_ff_t : (fun i : Fin 3 => i.val == 2) ∈ R)
    (h_no_fff : (fun _ : Fin 3 => false) ∉ R)
    (h_nand01 : ∀ s ∈ R, ¬(s ⟨0, by omega⟩ = true ∧ s ⟨1, by omega⟩ = true))
    (h_nand02 : ∀ s ∈ R, ¬(s ⟨0, by omega⟩ = true ∧ s ⟨2, by omega⟩ = true))
    (h_nand12 : ∀ s ∈ R, ¬(s ⟨1, by omega⟩ = true ∧ s ⟨2, by omega⟩ = true)) :
    R = exactlyOneRel := by
  ext s
  constructor
  · intro hs
    have hne_fff : s ≠ fun _ => false := fun heq => h_no_fff (heq ▸ hs)
    have hn01 := h_nand01 s hs
    have hn02 := h_nand02 s hs
    have hn12 := h_nand12 s hs
    simp only [exactlyOneRel, Finset.mem_filter, Finset.mem_univ, true_and]
    cases h0 : s ⟨0, by omega⟩ <;> cases h1 : s ⟨1, by omega⟩ <;> cases h2 : s ⟨2, by omega⟩
    · exfalso; apply hne_fff; funext i; fin_cases i <;> assumption
    · simp
    · simp
    · exfalso; exact hn12 ⟨h1, h2⟩
    · simp
    · exfalso; exact hn02 ⟨h0, h2⟩
    · exfalso; exact hn01 ⟨h0, h1⟩
    · exfalso; exact hn01 ⟨h0, h1⟩
  · intro hs
    have h_cases : s = (fun i : Fin 3 => i.val == 0) ∨
                   s = (fun i : Fin 3 => i.val == 1) ∨
                   s = (fun i : Fin 3 => i.val == 2) := by
      have hmem := hs
      simp only [exactlyOneRel, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hmem
      cases h0eq : s ⟨0, by omega⟩ <;> cases h1eq : s ⟨1, by omega⟩ <;>
          cases h2eq : s ⟨2, by omega⟩
      · simp_all
      · exact Or.inr (Or.inr (funext (fun i => by fin_cases i <;> simp_all)))
      · exact Or.inr (Or.inl (funext (fun i => by fin_cases i <;> simp_all)))
      · simp_all
      · exact Or.inl (funext (fun i => by fin_cases i <;> simp_all))
      · simp_all
      · simp_all
      · simp_all
    rcases h_cases with rfl | rfl | rfl
    · exact h_tf
    · exact h_ft
    · exact h_ff_t

/-- Helper: substitute(conjoin R3 nandRel2, σ) where σ identifies first 3 positions
    and maps positions 3,4 to a,b gives the nand-filtered subset. -/
private theorem mem_nand_filter {R3 : LogRel 3} (a b : Fin 3) (_hab : a ≠ b)
    (σ : Fin (3 + 2) → Fin 3 ⊕ Bool)
    (hσ : ∀ p : Fin 3, σ ⟨p.val, by omega⟩ = Sum.inl p)
    (hσ3 : σ ⟨3, by omega⟩ = Sum.inl a)
    (hσ4 : σ ⟨4, by omega⟩ = Sum.inl b)
    (s : Fin 3 → Bool) :
    s ∈ substitute (conjoin R3 nandRel2) σ ↔
      s ∈ R3 ∧ ¬(s a = true ∧ s b = true) := by
  have hL : splitLeft (substApply σ s) = s := by
    funext p; unfold splitLeft substApply; simp only [hσ p]
  have hR0 : splitRight (substApply σ s) ⟨0, by omega⟩ = s a := by
    unfold splitRight substApply; simp only [hσ3]
  have hR1 : splitRight (substApply σ s) ⟨1, by omega⟩ = s b := by
    unfold splitRight substApply; simp only [hσ4]
  constructor
  · intro hs
    rw [mem_substitute] at hs
    have hc := mem_conjoin.mp hs
    constructor
    · have := hc.1; rw [hL] at this; exact this
    · have hR_mem := hc.2
      simp only [nandRel2, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.not_eq_true'] at hR_mem
      intro ⟨ha, hb⟩
      have : splitRight (substApply σ s) ⟨0, by omega⟩ &&
             splitRight (substApply σ s) ⟨1, by omega⟩ = true := by
        rw [hR0, hR1, ha, hb]; rfl
      simp_all
  · intro ⟨hR3, hNand⟩
    rw [mem_substitute]
    apply mem_conjoin.mpr
    constructor
    · rw [hL]; exact hR3
    · simp only [nandRel2, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true']
      cases ha : splitRight (substApply σ s) ⟨0, by omega⟩ <;>
        cases hb : splitRight (substApply σ s) ⟨1, by omega⟩
      · simp
      · simp
      · simp
      · exfalso
        exact hNand ⟨by rw [← hR0]; exact ha, by rw [← hR1]; exact hb⟩

set_option maxHeartbeats 400000 in
/-- If S contains a non-bijunctive relation and we already have [x≠y] ∈ Rep(S)
    and all 3-element binary relations in Rep(S), then the "exactly one"
    relation is in Rep(S).

    This is Lemma 3.4 of Schaefer's paper. -/
theorem exactlyOne_in_rep {S : Finset BundledLogRel}
    (R : BundledLogRel) (hR : ↑R ∈ S)
    (hNotBij : ¬ IsBijunctive R.rel) (hNeq : InRep S 2 neqRel)
    (hBinaryRels : ∀ (T : LogRel 2), T.card = 3 → InRep S 2 T) :
    InRep S 3 exactlyOneRel := by
  -- Step 1: Get witnesses with 3 distinct positions
  obtain ⟨f, g, h, hfR, hgR, hhR, hmajR, i, j, l, hij, hil, hjl, hfi, hgj, hhl⟩ :=
    not_bijunctive_witness hNotBij
  set m := pointwiseMaj f g h with m_def
  -- Step 2: Normalize R via partialNeg (negate where m is true)
  have hRep : InRep S R.arity R.rel := InRep.base R hR
  obtain ⟨Rneg, hRneg_rep, hRneg_mem⟩ := partialNeg_in_rep hRep hNeq (f := m)
  -- Normalized tuples
  have hfn : (fun p => Bool.xor (m p) (f p)) ∈ Rneg := by
    rw [hRneg_mem]; convert hfR using 1; funext p; simp
  have hgn : (fun p => Bool.xor (m p) (g p)) ∈ Rneg := by
    rw [hRneg_mem]; convert hgR using 1; funext p; simp
  have hhn : (fun p => Bool.xor (m p) (h p)) ∈ Rneg := by
    rw [hRneg_mem]; convert hhR using 1; funext p; simp
  have hzero : (fun _ : Fin R.arity => false) ∉ Rneg := by
    intro habs
    rw [hRneg_mem] at habs
    apply hmajR
    have : (fun i => Bool.xor (m i) false) = m := by funext p; simp
    rwa [this] at habs
  -- Supports are pairwise disjoint
  have hfg_disj : ∀ p, Bool.xor (m p) (f p) = true → Bool.xor (m p) (g p) = false := by
    intro p hp
    have hfp : f p ≠ m p := by intro heq; simp [heq] at hp
    have hgp := maj_diff_positions_disjoint f g h p (m_def ▸ hfp)
    simp [m_def, hgp]
  have hfh_disj : ∀ p, Bool.xor (m p) (f p) = true → Bool.xor (m p) (h p) = false := by
    intro p hp
    have hfp : f p ≠ m p := by intro heq; simp [heq] at hp
    have hhp := maj_diff_positions_disjoint_fh f g h p (m_def ▸ hfp)
    simp [m_def, hhp]
  have hgh_disj : ∀ p, Bool.xor (m p) (g p) = true → Bool.xor (m p) (h p) = false := by
    intro p hp
    have hgp : g p ≠ m p := by intro heq; simp [heq] at hp
    have hhp := maj_diff_positions_disjoint_gh f g h p (m_def ▸ hgp)
    simp [m_def, hhp]
  -- Step 3: Project using support-based substitution
  let fn := fun p => Bool.xor (m p) (f p)
  let gn := fun p => Bool.xor (m p) (g p)
  let hn := fun p => Bool.xor (m p) (h p)
  let π : Fin R.arity → Fin 3 ⊕ Bool := fun p =>
    if fn p then Sum.inl ⟨0, by omega⟩
    else if gn p then Sum.inl ⟨1, by omega⟩
    else if hn p then Sum.inl ⟨2, by omega⟩
    else Sum.inr false
  have hR3 := InRep.subst Rneg π hRneg_rep
  -- Membership characterization for the projected relation
  have hR3_mem : ∀ s : Fin 3 → Bool, s ∈ substitute Rneg π ↔
      (fun p => if fn p then s ⟨0, by omega⟩
                else if gn p then s ⟨1, by omega⟩
                else if hn p then s ⟨2, by omega⟩
                else false) ∈ Rneg := by
    intro s; rw [mem_substitute]; constructor
    · intro hh; convert hh using 1; funext p
      simp only [substApply, π, fn, gn, hn]
      split_ifs <;> rfl
    · intro hh; convert hh using 1; funext p
      simp only [substApply, π, fn, gn, hn]
      split_ifs <;> rfl
  -- R3 contains (T,F,F)
  have hR3_tf : (fun p : Fin 3 => p.val == 0) ∈ substitute Rneg π := by
    rw [hR3_mem]; convert hfn using 1; funext p
    simp only [fn, gn, hn]
    split_ifs with h1 h2 h3
    · exact h1.symm
    · exact (eq_false_of_ne_true h1).symm
    · exact (eq_false_of_ne_true h1).symm
    · exact (eq_false_of_ne_true h1).symm
  -- R3 contains (F,T,F)
  have hR3_ft : (fun p : Fin 3 => p.val == 1) ∈ substitute Rneg π := by
    rw [hR3_mem]; convert hgn using 1; funext p
    simp only [fn, gn, hn]
    split_ifs with h1 h2 h3
    · exact (hfg_disj p h1).symm
    · exact h2.symm
    · exact (eq_false_of_ne_true h2).symm
    · exact (eq_false_of_ne_true h2).symm
  -- R3 contains (F,F,T)
  have hR3_fft : (fun p : Fin 3 => p.val == 2) ∈ substitute Rneg π := by
    rw [hR3_mem]; convert hhn using 1; funext p
    simp only [fn, gn, hn]
    split_ifs with h1 h2 h3
    · exact (hfh_disj p h1).symm
    · exact (hgh_disj p h2).symm
    · exact h3.symm
    · exact (eq_false_of_ne_true h3).symm
  -- R3 does NOT contain (F,F,F)
  have hR3_no_fff : (fun _ : Fin 3 => false) ∉ substitute Rneg π := by
    rw [hR3_mem]
    have heq : (fun p : Fin R.arity => if fn p then (fun _ : Fin 3 => false) ⟨0, by omega⟩
                else if gn p then (fun _ : Fin 3 => false) ⟨1, by omega⟩
                else if hn p then (fun _ : Fin 3 => false) ⟨2, by omega⟩
                else false) = (fun _ : Fin R.arity => false) := by
      funext p; simp only [fn, gn, hn]; split_ifs <;> rfl
    rw [heq]; exact hzero
  -- Step 4: Intersect with nand constraints to get exactlyOneRel
  have hnand_card : nandRel2.card = 3 := nandRel2_card
  have hNand := hBinaryRels nandRel2 hnand_card
  -- Define substitution maps for nand intersections
  let σ01 : Fin (3 + 2) → Fin 3 ⊕ Bool := fun q =>
    if h : q.val < 3 then Sum.inl ⟨q.val, h⟩
    else if q.val = 3 then Sum.inl ⟨0, by omega⟩
    else Sum.inl ⟨1, by omega⟩
  let σ02 : Fin (3 + 2) → Fin 3 ⊕ Bool := fun q =>
    if h : q.val < 3 then Sum.inl ⟨q.val, h⟩
    else if q.val = 3 then Sum.inl ⟨0, by omega⟩
    else Sum.inl ⟨2, by omega⟩
  let σ12 : Fin (3 + 2) → Fin 3 ⊕ Bool := fun q =>
    if h : q.val < 3 then Sum.inl ⟨q.val, h⟩
    else if q.val = 3 then Sum.inl ⟨1, by omega⟩
    else Sum.inl ⟨2, by omega⟩
  -- Build the InRep chain
  have hI1 := InRep.subst _ σ01 (InRep.conj _ nandRel2 hR3 hNand)
  have hI2 := InRep.subst _ σ02 (InRep.conj _ nandRel2 hI1 hNand)
  have hI3 := InRep.subst _ σ12 (InRep.conj _ nandRel2 hI2 hNand)
  -- Step 5: Show the final result = exactlyOneRel
  set R_final := substitute (conjoin (substitute (conjoin (substitute
    (conjoin (substitute Rneg π) nandRel2) σ01) nandRel2) σ02) nandRel2) σ12
  suffices heq : R_final = exactlyOneRel by rw [← heq]; exact hI3
  -- Prove membership characterization of R_final
  have hσ01 : ∀ p : Fin 3, σ01 ⟨p.val, by omega⟩ = Sum.inl p := by
    intro p; simp [σ01, show p.val < 3 from p.isLt]
  have hσ02 : ∀ p : Fin 3, σ02 ⟨p.val, by omega⟩ = Sum.inl p := by
    intro p; simp [σ02, show p.val < 3 from p.isLt]
  have hσ12 : ∀ p : Fin 3, σ12 ⟨p.val, by omega⟩ = Sum.inl p := by
    intro p; simp [σ12, show p.val < 3 from p.isLt]
  have hfinal_mem : ∀ s : Fin 3 → Bool, s ∈ R_final ↔
      s ∈ substitute Rneg π ∧
      ¬(s (0 : Fin 3) = true ∧ s (1 : Fin 3) = true) ∧
      ¬(s (0 : Fin 3) = true ∧ s (2 : Fin 3) = true) ∧
      ¬(s (1 : Fin 3) = true ∧ s (2 : Fin 3) = true) := by
    intro s
    simp only [R_final]
    have h12 := @mem_nand_filter (substitute (conjoin (substitute (conjoin
      (substitute Rneg π) nandRel2) σ01) nandRel2) σ02)
      (1 : Fin 3) (2 : Fin 3) (by decide) σ12 hσ12
      (by simp [σ12]) (by simp [σ12]) s
    rw [h12]
    have h02 := @mem_nand_filter (substitute (conjoin (substitute Rneg π) nandRel2) σ01)
      (0 : Fin 3) (2 : Fin 3) (by decide) σ02 hσ02
      (by simp [σ02]) (by simp [σ02]) s
    rw [h02]
    have h01 := @mem_nand_filter (substitute Rneg π)
      (0 : Fin 3) (1 : Fin 3) (by decide) σ01 hσ01
      (by simp [σ01]) (by simp [σ01]) s
    rw [h01]; simp only [and_assoc]
  -- Apply the helper theorem
  apply atMostOne_inter_not_allFalse_eq_exactlyOne
  · rw [hfinal_mem]; exact ⟨hR3_tf, by decide, by decide, by decide⟩
  · rw [hfinal_mem]; exact ⟨hR3_ft, by decide, by decide, by decide⟩
  · rw [hfinal_mem]; exact ⟨hR3_fft, by decide, by decide, by decide⟩
  · intro habs; rw [hfinal_mem] at habs; exact hR3_no_fff habs.1
  · intro s hs; rw [hfinal_mem] at hs; exact hs.2.1
  · intro s hs; rw [hfinal_mem] at hs; exact hs.2.2.1
  · intro s hs; rw [hfinal_mem] at hs; exact hs.2.2.2

end LocalRep
