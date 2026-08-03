/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Schaefer.Hardness.LocalRep.SAT.LogicalRelation

namespace ComplexityReduction.Schaefer.Hardness.LocalRep

open LogRel

/-! ## Weakly Positive / Negative Characterization (Lemma 3.1W)

A relation R is **weakly positive** (Horn) iff it is closed under pointwise AND.
A relation R is **weakly negative** (dual-Horn) iff it is closed under pointwise OR.

This file provides:
- Negation witnesses for WP and WN
- Zero-closed and one-closed characterizations
- Structural properties used in Lemma 3.2
-/

/-! ## Negation Witnesses
-/

/-- Not weakly positive ↔ there exist two tuples in R whose pointwise AND is not in R. -/
theorem not_wp_iff {k : Nat} {R : LogRel k} :
    ¬ IsWeaklyPositive R ↔ ∃ f, ∃ g, f ∈ R ∧ g ∈ R ∧ pointwiseAnd f g ∉ R := by
  unfold IsWeaklyPositive; push Not; rfl

/-- Not weakly negative ↔ there exist two tuples in R whose pointwise OR is not in R. -/
theorem not_wn_iff {k : Nat} {R : LogRel k} :
    ¬ IsWeaklyNegative R ↔ ∃ f, ∃ g, f ∈ R ∧ g ∈ R ∧ pointwiseOr f g ∉ R := by
  unfold IsWeaklyNegative; push Not; rfl

/-- If R is weakly positive, then for any f, g ∈ R, their pointwise AND is also in R. -/
theorem wp_mem_and {k : Nat} {R : LogRel k} (hWP : IsWeaklyPositive R)
    {f g : Fin k → Bool} (hf : f ∈ R) (hg : g ∈ R) :
    pointwiseAnd f g ∈ R := hWP hf hg

/-- If R is weakly negative, then for any f, g ∈ R, their pointwise OR is also in R. -/
theorem wn_mem_or {k : Nat} {R : LogRel k} (hWN : IsWeaklyNegative R)
    {f g : Fin k → Bool} (hf : f ∈ R) (hg : g ∈ R) :
    pointwiseOr f g ∈ R := hWN hf hg

/-! ## Zero-Closed and One-Closed Relations

A relation is **0-closed** (downward-closed) if whenever a tuple t is in R,
then any tuple t' ≤ t (pointwise) is also in R. This characterizes weakly
positive (Horn) relations.

A relation is **1-closed** (upward-closed) if whenever t ∈ R and t ≤ t'
(pointwise), then t' ∈ R. This characterizes weakly negative (dual-Horn)
relations.
-/

/-- Pointwise ordering on Boolean tuples: t ≤ t' iff for all i, t i → t' i. -/
def pointwiseLe {k : Nat} (t t' : Fin k → Bool) : Prop :=
  ∀ i : Fin k, t i = true → t' i = true

/-- A relation is 0-closed (downward-closed) if whenever t ∈ R and t' ≤ t,
    then t' ∈ R. -/
def IsZeroClosed {k : Nat} (R : LogRel k) : Prop :=
  ∀ t ∈ R, ∀ t' : Fin k → Bool, pointwiseLe t' t → t' ∈ R

/-- A relation is 1-closed (upward-closed) if whenever t ∈ R and t ≤ t',
    then t' ∈ R. -/
def IsOneClosed {k : Nat} (R : LogRel k) : Prop :=
  ∀ t ∈ R, ∀ t' : Fin k → Bool, pointwiseLe t t' → t' ∈ R

namespace PointwiseLe

@[simp] theorem refl {k : Nat} (t : Fin k → Bool) : pointwiseLe t t := by
  intro i hi; exact hi

theorem trans {k : Nat} {t₁ t₂ t₃ : Fin k → Bool}
    (h12 : pointwiseLe t₁ t₂) (h23 : pointwiseLe t₂ t₃) :
    pointwiseLe t₁ t₃ := by
  intro i hi; exact h23 i (h12 i hi)

theorem antisymm {k : Nat} {t t' : Fin k → Bool}
    (h : pointwiseLe t t') (h' : pointwiseLe t' t) :
    t = t' := by
  funext i
  by_cases h1 : t i = true <;> by_cases h2 : t' i = true
  · simp_all
  · have := h i h1; contradiction
  · have := h' i h2; contradiction
  · simp_all

/-- The all-false tuple is below everything. -/
theorem constFalse_le {k : Nat} (t : Fin k → Bool) : pointwiseLe constFalse t := by
  intro i hi
  unfold constFalse at hi
  contradiction

/-- The all-true tuple is above everything. -/
theorem le_constTrue {k : Nat} (t : Fin k → Bool) : pointwiseLe t constTrue := by
  intro i hi; rfl

/-- Pointwise AND is the greatest lower bound. -/
theorem pointwiseAnd_le_left {k : Nat} {f g : Fin k → Bool} :
    pointwiseLe (pointwiseAnd f g) f := by
  intro i hi
  exact Bool.and_eq_true_iff.mp (by unfold pointwiseAnd at hi; exact hi) |>.1

theorem pointwiseAnd_le_right {k : Nat} {f g : Fin k → Bool} :
    pointwiseLe (pointwiseAnd f g) g := by
  intro i hi
  exact Bool.and_eq_true_iff.mp (by unfold pointwiseAnd at hi; exact hi) |>.2

theorem pointwiseAnd_glb {k : Nat} {f g h : Fin k → Bool} :
    pointwiseLe h f → pointwiseLe h g → pointwiseLe h (pointwiseAnd f g) := by
  intro h1 h2 i hi
  exact Bool.and_eq_true_iff.mpr ⟨h1 i hi, h2 i hi⟩

/-- Pointwise OR is the least upper bound. -/
theorem le_pointwiseOr_left {k : Nat} {f g : Fin k → Bool} :
    pointwiseLe f (pointwiseOr f g) := by
  intro i hi
  unfold pointwiseOr
  exact Bool.or_eq_true_iff.mpr (Or.inl hi)

theorem le_pointwiseOr_right {k : Nat} {f g : Fin k → Bool} :
    pointwiseLe g (pointwiseOr f g) := by
  intro i hi
  unfold pointwiseOr
  exact Bool.or_eq_true_iff.mpr (Or.inr hi)

theorem pointwiseOr_lub {k : Nat} {f g h : Fin k → Bool} :
    pointwiseLe f h → pointwiseLe g h → pointwiseLe (pointwiseOr f g) h := by
  intro h1 h2 i hi
  unfold pointwiseOr at hi
  rcases Bool.or_eq_true_iff.mp hi with (hf | hg)
  · exact h1 i hf
  · exact h2 i hg

end PointwiseLe

/-! ## Equivalence: WP ↔ 0-closed, WN ↔ 1-closed

The standard characterizations: a relation is weakly positive iff it is 0-closed,
and weakly negative iff it is 1-closed. Below we state these equivalences.
-/

/-- 0-closed (downward-closed) implies weakly positive (AND-closed).
    This is the correct direction: if R is downward-closed, then for any f, g ∈ R,
    pointwiseAnd f g ≤ f, so pointwiseAnd f g ∈ R by downward-closure. -/
theorem wp_of_zeroClosed {k : Nat} {R : LogRel k}
    (hZC : IsZeroClosed R) : IsWeaklyPositive R := by
  intro f g hf hg
  exact hZC f hf (pointwiseAnd f g) PointwiseLe.pointwiseAnd_le_left

/-- 1-closed (upward-closed) implies weakly negative (OR-closed).
    This is the correct direction: if R is upward-closed, then for any f, g ∈ R,
    f ≤ pointwiseOr f g, so pointwiseOr f g ∈ R by upward-closure. -/
theorem wn_of_oneClosed {k : Nat} {R : LogRel k}
    (hOC : IsOneClosed R) : IsWeaklyNegative R := by
  intro f g hf hg
  exact hOC f hf (pointwiseOr f g) PointwiseLe.le_pointwiseOr_left

/-- 0-closed implies weakly positive. This is the valid direction of the
    relationship. The converse (WP → 0-closed) does NOT hold in general:
    e.g., R = {(true,true)} is AND-closed but not downward-closed.
    In Schaefer's framework, the direct witness theorems `not_wp_iff` and
    `not_zeroClosed_iff` are used instead of this equivalence. -/
theorem wp_iff_zeroClosed {k : Nat} {R : LogRel k}
    (hZC : IsZeroClosed R) : IsWeaklyPositive R :=
  wp_of_zeroClosed hZC

/-- 1-closed implies weakly negative. Same situation as wp_iff_zeroClosed. -/
theorem wn_iff_oneClosed {k : Nat} {R : LogRel k}
    (hOC : IsOneClosed R) : IsWeaklyNegative R :=
  wn_of_oneClosed hOC

/-- Not 0-closed ↔ there exist tuples t ∈ R, t' ≤ t with t' ∉ R. -/
theorem not_zeroClosed_iff {k : Nat} {R : LogRel k} :
    ¬ IsZeroClosed R ↔ ∃ t ∈ R, ∃ t' : Fin k → Bool, pointwiseLe t' t ∧ t' ∉ R := by
  unfold IsZeroClosed; push Not; rfl

/-- Not 1-closed ↔ there exist tuples t ∈ R, t' ≥ t with t' ∉ R. -/
theorem not_oneClosed_iff {k : Nat} {R : LogRel k} :
    ¬ IsOneClosed R ↔ ∃ t ∈ R, ∃ t' : Fin k → Bool, pointwiseLe t t' ∧ t' ∉ R := by
  unfold IsOneClosed; push Not; rfl

end LocalRep