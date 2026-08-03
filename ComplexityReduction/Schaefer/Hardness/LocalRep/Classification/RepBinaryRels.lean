/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Schaefer.Hardness.LocalRep.SAT.LogicalRelation
import ComplexityReduction.Schaefer.Hardness.LocalRep.Closure.Operations
import ComplexityReduction.Schaefer.Hardness.LocalRep.Closure.Rep
import ComplexityReduction.Schaefer.Hardness.LocalRep.Classification.AffineChar
import ComplexityReduction.Schaefer.Hardness.LocalRep.Classification.RepContainsNeq
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

namespace ComplexityReduction.Schaefer.Hardness.LocalRep

open LogRel

/-! ## Lemma 3.3: All 3-Element Binary Relations in Rep(S)

If [x ≠ y] ∈ Rep(S) and S contains a relation that is not affine,
then every 3-element binary relation is in Rep(S).

With [x ≠ y] available, we can simulate negated variables, making the
negated substitution operation derivable. Combined with non-affinity,
this produces all small binary relations.
-/

/-- A binary relation has exactly 3 elements. -/
def hasCard3 (R : LogRel 2) : Prop := R.card = 3

/-- Negate a single variable at position j in a relation.
    Result: {s | (s with position j negated) ∈ R}. -/
def negateAt {m : Nat} (R : LogRel m) (j : Fin m) : LogRel m :=
  Finset.filter (fun s : Fin m → Bool =>
    (fun i => if i = j then !(s j) else s i) ∈ R) Finset.univ

/-- Negating position j of R is in InRep when neqRel is available.
    Construction: conjoin R neqRel (arity m+2), substitute to identify
    R's position j with neqRel's first position and put neqRel's second
    at position j, then existentially quantify the shared variable. -/
theorem negateAt_in_rep {S : Finset BundledLogRel}
    {m : Nat} {R : LogRel m} (j : Fin m)
    (hR : InRep S m R) (hNeq : InRep S 2 neqRel) :
    InRep S m (negateAt R j) := by
  let π : Fin (m + 2) → Fin (m + 1) ⊕ Bool := fun i =>
    if h : i.val < m then
      if i.val = j.val then Sum.inl ⟨m, by omega⟩
      else Sum.inl ⟨i.val, by omega⟩
    else if i.val = m then Sum.inl ⟨m, by omega⟩
    else Sum.inl ⟨j.val, by omega⟩
  have hConj := InRep.conj R neqRel hR hNeq
  have hSubst := InRep.subst (conjoin R neqRel) π hConj
  have hExist := InRep.existential _ hSubst
  suffices heq : existentialQuantify (substitute (conjoin R neqRel) π) = negateAt R j by
    rw [← heq]; exact hExist
  ext s
  simp only [mem_existentialQuantify, mem_substitute, mem_conjoin, mem_neqRel]
  show (∃ b, splitLeft (substApply π (extendWith s b)) ∈ R ∧
    splitRight (substApply π (extendWith s b)) ⟨0, by omega⟩ ≠
    splitRight (substApply π (extendWith s b)) ⟨1, by omega⟩) ↔
    s ∈ negateAt R j
  simp only [negateAt, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, hRmem, hNeqmem⟩
    suffices hsuff : (fun i : Fin m => if i = j then !(s j) else s i) ∈ R by exact hsuff
    suffices hb : b = !(s j) by
      subst hb
      convert hRmem using 1
      funext i
      simp [splitLeft, substApply, extendWith, π]
      split_ifs <;> simp_all [Fin.ext_iff]
    -- b ≠ s j means b = !(s j)
    simp [splitRight, substApply, extendWith, π] at hNeqmem
    exact Bool.eq_not_iff.mpr hNeqmem
  · intro hmem
    exact ⟨!(s j), by
      constructor
      · convert hmem using 1
        funext i
        simp [splitLeft, substApply, extendWith, π]
        split_ifs <;> simp_all [Fin.ext_iff]
      · simp [splitRight, substApply, extendWith, π]⟩

/-- Helper: the "complement" of a relation (negate all variables) is in Rep
    when neqRel is available.

    Proof: negate variables one at a time (positions 0, 1, ..., m-1),
    using negateAt_in_rep at each step. -/
private theorem complement_in_rep {S : Finset BundledLogRel}
    {m : Nat} {T : LogRel m}
    (hT : InRep S m T) (hNeq : InRep S 2 neqRel) :
    InRep S m (negSubstitute T (fun i => Sum.inl i)) := by
  -- Iteratively negate positions 0, 1, ..., m-1.
  -- Key lemma: for all k ≤ m, there exists U_k ∈ InRep with
  --   s ∈ U_k ↔ (fun i => if i.val < k then !(s i) else s i) ∈ T
  suffices key : ∀ k (hk : k ≤ m), ∃ U : LogRel m, InRep S m U ∧
    (∀ s : Fin m → Bool,
      s ∈ U ↔ (fun i : Fin m => if i.val < k then !(s i) else s i) ∈ T) by
    obtain ⟨U, hU, hUeq⟩ := key m (le_refl m)
    suffices heq : U = negSubstitute T (fun i => Sum.inl i) by rw [← heq]; exact hU
    ext s; rw [hUeq s]; simp only [mem_negSubstitute]
    suffices hsuff : (fun i : Fin m => if (i : Fin m).val < m then !(s i) else s i) =
      negSubstApply (fun i => Sum.inl i) s by rw [hsuff]
    funext i; simp [i.isLt, negSubstApply]
  intro k hk
  induction k with
  | zero => exact ⟨T, hT, fun s => by simp⟩
  | succ n ih =>
    obtain ⟨U, hU, hUeq⟩ := ih (by omega)
    have hn_lt : n < m := by omega
    refine ⟨negateAt U ⟨n, hn_lt⟩, negateAt_in_rep ⟨n, hn_lt⟩ hU hNeq, fun s => ?_⟩
    simp only [negateAt, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hUeq]
    constructor <;> intro h
    · convert h using 1
      funext i
      by_cases hi1 : i.val < n
      · have hne : (i : Fin m) ≠ ⟨n, hn_lt⟩ := by intro heq; simp [Fin.ext_iff] at heq; omega
        simp [hi1, show i.val < n + 1 from by omega, hne]
      · by_cases hi2 : i.val = n
        · have heq : (i : Fin m) = ⟨n, hn_lt⟩ := Fin.ext hi2
          simp [heq, show n < n + 1 from by omega]
        · have hne : (i : Fin m) ≠ ⟨n, hn_lt⟩ := by intro heq; simp [Fin.ext_iff] at heq; exact hi2 heq
          simp [show ¬(i.val < n + 1) from by omega, hi1, hne]
    · convert h using 1
      funext i
      by_cases hi1 : i.val < n
      · have hne : (i : Fin m) ≠ ⟨n, hn_lt⟩ := by intro heq; simp [Fin.ext_iff] at heq; omega
        simp [hi1, show i.val < n + 1 from by omega, hne]
      · by_cases hi2 : i.val = n
        · have heq : (i : Fin m) = ⟨n, hn_lt⟩ := Fin.ext hi2
          simp [heq, show n < n + 1 from by omega]
        · have hne : (i : Fin m) ≠ ⟨n, hn_lt⟩ := by intro heq; simp [Fin.ext_iff] at heq; exact hi2 heq
          simp [show ¬(i.val < n + 1) from by omega, hi1, hne]

/-- With [x ≠ y] in Rep, negated substitution becomes derivable:
    if R ∈ Rep(S) then negSubstitute R π ∈ Rep(S).

    The proof decomposes negSubstitute R π as the complement of substitute R π:
    negSubstitute R π = negSubstitute (substitute R π) (fun i => Sum.inl i). -/
theorem negSubst_in_rep_of_neq {S : Finset BundledLogRel}
    {k m : Nat} {R : LogRel k} {π : Fin k → Fin m ⊕ Bool}
    (hR : InRep S k R) (hNeq : InRep S 2 neqRel) :
    InRep S m (negSubstitute R π) := by
  -- Key identity: negSubstitute R π = negSubstitute (substitute R π) (fun i => Sum.inl i)
  have heq : negSubstitute R π = negSubstitute (substitute R π) (fun i => Sum.inl i) := by
    ext s
    simp only [mem_negSubstitute, mem_substitute]
    show negSubstApply π s ∈ R ↔ substApply π (fun j => !(s j)) ∈ R
    suffices h : negSubstApply π s = substApply π (fun j => !(s j)) by rw [h]
    funext i
    simp [negSubstApply, substApply]
  rw [heq]
  exact complement_in_rep (InRep.subst R π hR) hNeq

/-- ¬x ∨ y (implication) -/
private def implRel2 : LogRel 2 :=
  Finset.filter (fun t : Fin 2 → Bool => !(t ⟨0, by omega⟩) || t ⟨1, by omega⟩) Finset.univ
/-- x ∨ ¬y (reverse implication) -/
private def revImplRel : LogRel 2 :=
  Finset.filter (fun t : Fin 2 → Bool => t ⟨0, by omega⟩ || !(t ⟨1, by omega⟩)) Finset.univ
/-- ¬x ∨ ¬y (nand) -/
private def nandRel2 : LogRel 2 :=
  Finset.filter (fun t : Fin 2 → Bool => !(t ⟨0, by omega⟩) || !(t ⟨1, by omega⟩)) Finset.univ

private theorem implRel2_eq : implRel2 = negateAt orRel ⟨0, by omega⟩ := by native_decide
private theorem revImplRel_eq : revImplRel = negateAt orRel ⟨1, by omega⟩ := by native_decide
private theorem nandRel2_eq : nandRel2 = negateAt (negateAt orRel ⟨0, by omega⟩) ⟨1, by omega⟩ := by
  native_decide

private theorem negateAt_implRel2_0 : negateAt implRel2 ⟨0, by omega⟩ = orRel := by native_decide
private theorem negateAt_revImplRel_1 : negateAt revImplRel ⟨1, by omega⟩ = orRel := by native_decide
private theorem negateAt_nandRel2_0 : negateAt nandRel2 ⟨0, by omega⟩ = revImplRel := by native_decide
private theorem nandRel2_eq2 : nandRel2 = negateAt implRel2 ⟨1, by omega⟩ := by native_decide

set_option maxHeartbeats 800000 in
/-- Every 3-element binary relation equals orRel after possibly negating variables. -/
private theorem card3_eq_orRel_variant (T : LogRel 2) (hT : T.card = 3) :
    T = orRel ∨ T = implRel2 ∨ T = revImplRel ∨ T = nandRel2 := by
  have key : ∀ T : LogRel 2,
      T.card ≠ 3 ∨ T = orRel ∨ T = implRel2 ∨ T = revImplRel ∨ T = nandRel2 := by
    native_decide
  exact (key T).resolve_left (by omega)

set_option maxHeartbeats 800000 in
/-- A non-affine binary relation has exactly 3 elements. -/
private theorem not_affine_binary_card_three (T : LogRel 2) (h : ¬ IsAffine T) :
    T.card = 3 := by
  have key : ∀ T : LogRel 2,
      (∀ f ∈ T, ∀ g ∈ T, ∀ h ∈ T, pointwiseTernaryXor f g h ∈ T) ∨ T.card = 3 := by
    native_decide
  have hNotClosed : ¬(∀ f ∈ T, ∀ g ∈ T, ∀ h ∈ T, pointwiseTernaryXor f g h ∈ T) := by
    intro hc; exact h (fun {f} {g} {h} hf hg hh => hc f hf g hg h hh)
  exact (key T).resolve_left hNotClosed

/-- The WP-style substitution: maps coords where a=T,b=F to var 0,
    coords where a=F,b=T to var 1, else constant a i. -/
private def wpSubst {k : Nat} (a b : Fin k → Bool) : Fin k → Fin 2 ⊕ Bool := fun i =>
  if a i = true ∧ b i = false then Sum.inl ⟨0, by omega⟩
  else if a i = false ∧ b i = true then Sum.inl ⟨1, by omega⟩
  else Sum.inr (a i)

private theorem wpSubst_img_a {k : Nat} (a b : Fin k → Bool) :
    substApply (wpSubst a b) (fun j : Fin 2 => if j.val = 0 then true else false) = a := by
  funext i; simp [substApply, wpSubst]; split_ifs <;> simp_all

private theorem wpSubst_img_b {k : Nat} (a b : Fin k → Bool) :
    substApply (wpSubst a b) (fun j : Fin 2 => if j.val = 0 then false else true) = b := by
  funext i; simp only [substApply, wpSubst]
  cases ha : a i <;> cases hb : b i <;> simp

private theorem wpSubst_img_and {k : Nat} (a b : Fin k → Bool) :
    substApply (wpSubst a b) (fun _ : Fin 2 => false) = pointwiseAnd a b := by
  funext i; simp [substApply, wpSubst, pointwiseAnd]; split_ifs <;> simp_all

private theorem wpSubst_img_or {k : Nat} (a b : Fin k → Bool) :
    substApply (wpSubst a b) (fun _ : Fin 2 => true) = pointwiseOr a b := by
  funext i; simp only [substApply, wpSubst, pointwiseOr]
  cases ha : a i <;> cases hb : b i <;> simp

/-- The ternary projection substitution: maps coordinates based on (a_i, b_i) patterns. -/
private def ternaryProj {k : Nat} (a b : Fin k → Bool) : Fin k → Fin 3 ⊕ Bool := fun i =>
  if a i = true ∧ b i = false then Sum.inl ⟨0, by omega⟩
  else if a i = false ∧ b i = true then Sum.inl ⟨1, by omega⟩
  else if a i = true ∧ b i = true then Sum.inl ⟨2, by omega⟩
  else Sum.inr false

private theorem ternaryProj_maps_a {k : Nat} (a b : Fin k → Bool) :
    substApply (ternaryProj a b) (fun j : Fin 3 =>
      if j.val = 0 then true else if j.val = 2 then true else false) = a := by
  funext i; simp [substApply, ternaryProj]
  cases ha : a i <;> cases hb : b i <;> simp_all

private theorem ternaryProj_maps_b {k : Nat} (a b : Fin k → Bool) :
    substApply (ternaryProj a b) (fun j : Fin 3 =>
      if j.val = 1 then true else if j.val = 2 then true else false) = b := by
  funext i; simp [substApply, ternaryProj]
  cases ha : a i <;> cases hb : b i <;> simp_all

private theorem ternaryProj_maps_zero {k : Nat} (a b : Fin k → Bool) :
    substApply (ternaryProj a b) (fun _ : Fin 3 => false) = constFalse := by
  funext i; simp [substApply, ternaryProj, constFalse]
  split_ifs <;> simp_all

private theorem ternaryProj_maps_xor {k : Nat} (a b : Fin k → Bool) :
    substApply (ternaryProj a b) (fun j : Fin 3 =>
      if j.val = 0 then true else if j.val = 1 then true else false) =
    pointwiseTernaryXor constFalse a b := by
  funext i; simp [substApply, ternaryProj, pointwiseTernaryXor, constFalse]
  cases ha : a i <;> cases hb : b i <;> simp_all

private theorem ternaryProj_not_affine {k : Nat} {R : LogRel k} {a b : Fin k → Bool}
    (h0 : constFalse ∈ R) (ha : a ∈ R) (hb : b ∈ R)
    (hxor : pointwiseTernaryXor constFalse a b ∉ R) :
    ¬ IsAffine (substitute R (ternaryProj a b)) := by
  rw [not_affine_iff]
  have hxor_eq : pointwiseTernaryXor (fun _ : Fin 3 => false)
      (fun j : Fin 3 => if j.val = 0 then true else if j.val = 2 then true else false)
      (fun j : Fin 3 => if j.val = 1 then true else if j.val = 2 then true else false) =
      (fun j : Fin 3 => if j.val = 0 then true else if j.val = 1 then true else false) := by
    funext j; simp [pointwiseTernaryXor]; fin_cases j <;> simp
  refine ⟨fun _ => false,
          fun j => if j.val = 0 then true else if j.val = 2 then true else false,
          fun j => if j.val = 1 then true else if j.val = 2 then true else false,
          ?_, ?_, ?_, ?_⟩
  · rw [mem_substitute, ternaryProj_maps_zero]; exact h0
  · rw [mem_substitute, ternaryProj_maps_a]; exact ha
  · rw [mem_substitute, ternaryProj_maps_b]; exact hb
  · rw [mem_substitute, hxor_eq, ternaryProj_maps_xor]; exact hxor

/-- Negate variables at positions where f is true. Result is in InRep.
    Uses iterative application of negateAt. -/
theorem partialNeg_in_rep {S : Finset BundledLogRel}
    {m : Nat} {R : LogRel m} {f : Fin m → Bool}
    (hR : InRep S m R) (hNeq : InRep S 2 neqRel) :
    ∃ U : LogRel m, InRep S m U ∧
      (∀ t : Fin m → Bool, t ∈ U ↔
        (fun i => Bool.xor (f i) (t i)) ∈ R) := by
  suffices key : ∀ n (hn : n ≤ m), ∃ U : LogRel m, InRep S m U ∧
    (∀ t : Fin m → Bool, t ∈ U ↔
      (fun i : Fin m => if i.val < n then Bool.xor (f i) (t i) else t i) ∈ R) by
    obtain ⟨U, hU, hUeq⟩ := key m (le_refl m)
    exact ⟨U, hU, fun t => by
      rw [hUeq]; constructor <;> intro h
      · have heq : (fun i : Fin m => if i.val < m then Bool.xor (f i) (t i) else t i) =
            fun i => Bool.xor (f i) (t i) := funext (fun i => by simp [i.isLt])
        rw [heq] at h; exact h
      · have heq : (fun i : Fin m => if i.val < m then Bool.xor (f i) (t i) else t i) =
            fun i => Bool.xor (f i) (t i) := funext (fun i => by simp [i.isLt])
        rw [heq]; exact h⟩
  intro n hn
  induction n with
  | zero =>
    exact ⟨R, hR, fun t => by
      have heq : (fun i : Fin m => if i.val < 0 then Bool.xor (f i) (t i) else t i) = t :=
        funext (fun i => by simp)
      rw [heq]⟩
  | succ k ih =>
    obtain ⟨U, hU, hUeq⟩ := ih (by omega)
    have hk_lt : k < m := by omega
    by_cases hfk : f ⟨k, hk_lt⟩ = true
    · refine ⟨negateAt U ⟨k, hk_lt⟩, negateAt_in_rep ⟨k, hk_lt⟩ hU hNeq, fun t => ?_⟩
      simp only [negateAt, Finset.mem_filter, Finset.mem_univ, true_and, hUeq]
      constructor <;> intro h
      · convert h using 1; funext i
        by_cases hik : i = ⟨k, hk_lt⟩
        · subst hik; simp [Nat.lt_succ_of_le (le_refl k), hfk]
        · have hival : i.val ≠ k := fun h => hik (Fin.ext h)
          simp only [hik, ite_false]
          by_cases hi : i.val < k
          · have : i.val < k + 1 := by omega
            simp [hi, this]
          · have : ¬(i.val < k + 1) := by omega
            simp [hi, this]
      · convert h using 1; funext i
        by_cases hik : i = ⟨k, hk_lt⟩
        · subst hik; simp [Nat.lt_succ_of_le (le_refl k), hfk]
        · have hival : i.val ≠ k := fun h => hik (Fin.ext h)
          simp only [hik, ite_false]
          by_cases hi : i.val < k
          · have : i.val < k + 1 := by omega
            simp [hi, this]
          · have : ¬(i.val < k + 1) := by omega
            simp [hi, this]
    · have hfk_false : f ⟨k, hk_lt⟩ = false := by cases h : f ⟨k, hk_lt⟩ <;> simp_all
      refine ⟨U, hU, fun t => ?_⟩
      rw [hUeq]
      constructor <;> intro h
      · convert h using 1; funext i
        by_cases hi : i.val < k
        · simp [hi, show i.val < k + 1 from by omega]
        · by_cases hik : i.val = k
          · have : i = ⟨k, hk_lt⟩ := Fin.ext hik
            subst this; simp [show k < k + 1 from by omega, hfk_false]
          · simp [hi, show ¬(i.val < k + 1) from by omega]
      · convert h using 1; funext i
        by_cases hi : i.val < k
        · simp [hi, show i.val < k + 1 from by omega]
        · by_cases hik : i.val = k
          · have : i = ⟨k, hk_lt⟩ := Fin.ext hik
            subst this; simp [show k < k + 1 from by omega, hfk_false]
          · simp [hi, show ¬(i.val < k + 1) from by omega]

set_option maxHeartbeats 400000000 in
/-- For any non-affine ternary relation, one of 6 specific operations produces
    a 3-element binary relation. Proven by exhaustive enumeration. -/
private theorem ternary_affine_or_reduces :
    ∀ R : Finset (Fin 3 → Bool),
      (∀ f ∈ R, ∀ g ∈ R, ∀ h ∈ R, pointwiseTernaryXor f g h ∈ R) ∨
      (existentialQuantify R).card = 3 ∨
      (existentialQuantify (substitute R (fun i : Fin 3 =>
        Sum.inl (⟨(i.val + 1) % 3, by omega⟩ : Fin 3)))).card = 3 ∨
      (existentialQuantify (substitute R (fun i : Fin 3 =>
        Sum.inl (⟨(i.val + 2) % 3, by omega⟩ : Fin 3)))).card = 3 ∨
      (substitute R (fun i : Fin 3 => if i.val = 0 then Sum.inl (0 : Fin 2)
        else if i.val = 1 then Sum.inl 1 else Sum.inr false)).card = 3 ∨
      (substitute R (fun i : Fin 3 => if i.val = 0 then Sum.inl (0 : Fin 2)
        else if i.val = 1 then Sum.inl 1 else Sum.inl 0)).card = 3 ∨
      (substitute R (fun i : Fin 3 => if i.val = 0 then Sum.inl (0 : Fin 2)
        else if i.val = 1 then Sum.inl 1 else Sum.inr true)).card = 3 := by
  native_decide

/-- Helper: apply one of the 6 ternary→binary operations and show result is in InRep. -/
private theorem ternary_to_binary_in_rep {S : Finset BundledLogRel}
    {R3 : LogRel 3} (hR3 : InRep S 3 R3) (hNotAff : ¬ IsAffine R3) :
    ∃ T : LogRel 2, T.card = 3 ∧ InRep S 2 T := by
  have h := ternary_affine_or_reduces R3
  rcases h with hAff | h1 | h2 | h3 | h4 | h5 | h6
  · exact absurd (fun {f} {g} {h} hf hg hh => hAff f hf g hg h hh) hNotAff
  · exact ⟨_, h1, InRep.existential R3 hR3⟩
  · exact ⟨_, h2, InRep.existential _ (InRep.subst R3 _ hR3)⟩
  · exact ⟨_, h3, InRep.existential _ (InRep.subst R3 _ hR3)⟩
  · exact ⟨_, h4, InRep.subst R3 _ hR3⟩
  · exact ⟨_, h5, InRep.subst R3 _ hR3⟩
  · exact ⟨_, h6, InRep.subst R3 _ hR3⟩

/-- If S contains a non-affine relation and [x≠y] ∈ Rep(S),
    then all binary relations with 3 elements are in Rep(S). -/
theorem three_element_binary_in_rep {S : Finset BundledLogRel}
    (R : BundledLogRel) (hR : ↑R ∈ S)
    (hNotAff : ¬ IsAffine R.rel) (hNeq : InRep S 2 neqRel) :
    ∀ (T : LogRel 2), T.card = 3 → InRep S 2 T := by
  intro T hT
  -- Step 1: Extract non-affine witnesses
  obtain ⟨f, g, h, hf, hg, hh, hfgh⟩ := not_affine_iff.mp hNotAff
  -- Step 2: Normalize by XOR with f to get constFalse in the relation
  obtain ⟨R', hR'_rep, hR'_mem⟩ := partialNeg_in_rep (InRep.base R hR) hNeq (f := f)
  have h0_in : constFalse ∈ R' := by
    rw [hR'_mem]; convert hf using 1; funext i; simp [constFalse]
  have ha_in : (fun i => Bool.xor (f i) (g i)) ∈ R' := by
    rw [hR'_mem]; convert hg using 1; funext i
    simp
  have hb_in : (fun i => Bool.xor (f i) (h i)) ∈ R' := by
    rw [hR'_mem]; convert hh using 1; funext i
    simp
  have hxor_not_in : pointwiseTernaryXor constFalse
      (fun i => Bool.xor (f i) (g i)) (fun i => Bool.xor (f i) (h i)) ∉ R' := by
    rw [hR'_mem]
    intro hmem
    apply hfgh
    have heq : (fun i => Bool.xor (f i) (pointwiseTernaryXor constFalse
        (fun i => Bool.xor (f i) (g i)) (fun i => Bool.xor (f i) (h i)) i)) =
        pointwiseTernaryXor f g h := by
      funext i; simp [pointwiseTernaryXor, constFalse]
      cases f i <;> cases g i <;> cases h i <;> simp
    rw [heq] at hmem; exact hmem
  -- Step 3: Project to ternary non-affine relation
  set a := fun i => Bool.xor (f i) (g i)
  set b := fun i => Bool.xor (f i) (h i)
  have hR3_not_aff := ternaryProj_not_affine h0_in ha_in hb_in hxor_not_in
  have hR3_rep : InRep S 3 (substitute R' (ternaryProj a b)) := InRep.subst R' _ hR'_rep
  -- Step 4: Get a card-3 binary relation
  obtain ⟨T', hT'_card, hT'_rep⟩ := ternary_to_binary_in_rep hR3_rep hR3_not_aff
  -- Step 5: From any card-3 binary, derive all card-3 binary via negateAt
  have hT'_variant := card3_eq_orRel_variant T' hT'_card
  -- T is also a variant of orRel
  have hT_variant := card3_eq_orRel_variant T hT
  -- Show all variants are in InRep given one variant is
  suffices hall : ∀ V : LogRel 2, V.card = 3 → InRep S 2 V from hall T hT
  intro V hV
  have hV_variant := card3_eq_orRel_variant V hV
  -- We need orRel and all its negations in InRep
  -- First get orRel in InRep from T'
  have hOrRep : InRep S 2 orRel := by
    rcases hT'_variant with h | h | h | h <;> rw [h] at hT'_rep
    · exact hT'_rep
    · -- T' = implRel2, negate position 0 to get orRel
      have h1 := negateAt_in_rep ⟨0, by omega⟩ hT'_rep hNeq
      rw [negateAt_implRel2_0] at h1; exact h1
    · -- T' = revImplRel, negate position 1 to get orRel
      have h1 := negateAt_in_rep ⟨1, by omega⟩ hT'_rep hNeq
      rw [negateAt_revImplRel_1] at h1; exact h1
    · -- T' = nandRel2, negate position 0 then 1 to get orRel
      have h1 := negateAt_in_rep ⟨0, by omega⟩ hT'_rep hNeq
      rw [negateAt_nandRel2_0] at h1
      have h2 := negateAt_in_rep ⟨1, by omega⟩ h1 hNeq
      rw [negateAt_revImplRel_1] at h2; exact h2
  -- Now derive V from orRel
  rcases hV_variant with h | h | h | h <;> rw [h]
  · exact hOrRep
  · -- implRel2 = negateAt orRel 0
    rw [implRel2_eq]; exact negateAt_in_rep ⟨0, by omega⟩ hOrRep hNeq
  · -- revImplRel = negateAt orRel 1
    rw [revImplRel_eq]; exact negateAt_in_rep ⟨1, by omega⟩ hOrRep hNeq
  · -- nandRel2 = negateAt implRel2 1
    rw [nandRel2_eq2]
    have hImpl := (by rw [implRel2_eq]; exact negateAt_in_rep ⟨0, by omega⟩ hOrRep hNeq :
      InRep S 2 implRel2)
    exact negateAt_in_rep ⟨1, by omega⟩ hImpl hNeq

/-- A specific important construction: with [x≠y] and a non-affine relation,
    we can construct the OR relation. -/
theorem or_in_rep_of_neq_and_not_affine {S : Finset BundledLogRel}
    (R : BundledLogRel) (hR : ↑R ∈ S)
    (hNotAff : ¬ IsAffine R.rel) (hNeq : InRep S 2 neqRel) :
    InRep S 2 orRel := by
  have h : orRel.card = 3 := by native_decide
  exact three_element_binary_in_rep R hR hNotAff hNeq orRel h

/-- With [x≠y] in Rep, we can construct the unary NOT relation. -/
theorem not_in_rep_of_neq {S : Finset BundledLogRel}
    (hNeq : InRep S 2 neqRel) :
    InRep S 1 notRel := by
  -- notRel(x) = substitute neqRel π where π 0 = inl 0, π 1 = inr true
  let π : Fin 2 → Fin 1 ⊕ Bool := fun i =>
    if i = 0 then Sum.inl 0 else Sum.inr true
  suffices h : substitute neqRel π = notRel by
    rw [← h]; exact InRep.subst neqRel π hNeq
  native_decide

/-- With [x≠y] in Rep, we can construct the all-true unary relation. -/
theorem allTrue_in_rep_of_neq {S : Finset BundledLogRel}
    (hNeq : InRep S 2 neqRel) :
    InRep S 1 allTrueRel := by
  -- allTrueRel(x) = substitute neqRel π where π 0 = inl 0, π 1 = inr false
  -- This gives: s 0 ≠ false, i.e., s 0 = true
  let π : Fin 2 → Fin 1 ⊕ Bool := fun i =>
    if i = 0 then Sum.inl 0 else Sum.inr false
  suffices h : substitute neqRel π = allTrueRel by
    rw [← h]; exact InRep.subst neqRel π hNeq
  native_decide

end LocalRep
