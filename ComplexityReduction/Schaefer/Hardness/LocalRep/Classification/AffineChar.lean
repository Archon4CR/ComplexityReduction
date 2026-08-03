/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Bool.Basic
import ComplexityReduction.Schaefer.Hardness.LocalRep.SAT.LogicalRelation
import ComplexityReduction.Schaefer.Hardness.LocalRep.Closure.Complementive

namespace ComplexityReduction.Schaefer.Hardness.LocalRep

open LogRel

/-! ## Affine Characterization (Lemma 3.1A)

A relation R is **affine** iff it is closed under ternary XOR (x ⊕ y ⊕ z),
equivalently iff R is the solution set of a system of linear equations over GF(2).
This file provides:
- The Bool ↔ ZMod 2 bridge
- Negation witness: ¬IsAffine R ↔ ∃ f,g,h ∈ R with f⊕g⊕h ∉ R
- Key structural properties of affine relations
-/

/-- Convert a Bool to ZMod 2: false ↦ 0, true ↦ 1. -/
def boolToZMod2 (b : Bool) : ZMod 2 := if b then 1 else 0

/-- Convert ZMod 2 to Bool: 0 ↦ false, nonzero ↦ true. -/
def zMod2ToBool (z : ZMod 2) : Bool := decide (z ≠ 0)

namespace BoolToZMod2

@[simp] theorem false_eq : boolToZMod2 false = 0 := by
  unfold boolToZMod2; simp

@[simp] theorem true_eq : boolToZMod2 true = 1 := by
  unfold boolToZMod2; simp

theorem injective : Function.Injective boolToZMod2 := by
  intro a b h; cases a <;> cases b <;> simp_all

theorem xor_eq_add (a b : Bool) :
    boolToZMod2 (Bool.xor a b) = boolToZMod2 a + boolToZMod2 b := by
  cases a <;> cases b <;> simp [boolToZMod2, Bool.xor]; decide

end BoolToZMod2

namespace ZMod2ToBool

@[simp] theorem zero_eq : zMod2ToBool 0 = false := by
  unfold zMod2ToBool; simp

@[simp] theorem one_eq : zMod2ToBool 1 = true := by
  unfold zMod2ToBool; simp

@[simp] theorem left_inv (b : Bool) : zMod2ToBool (boolToZMod2 b) = b := by
  cases b <;> simp

end ZMod2ToBool

/-! ## Negation Witness for Affine Relations

The key structural fact: ¬IsAffine R ↔ ∃ f,g,h ∈ R with f⊕g⊕h ∉ R.
This follows directly by pushing negation through the universal quantifier.
-/

/-- Not affine ↔ there exist three tuples in R whose ternary XOR is not in R. -/
theorem not_affine_iff {k : Nat} {R : LogRel k} :
    ¬ IsAffine R ↔ ∃ f, ∃ g, ∃ h, f ∈ R ∧ g ∈ R ∧ h ∈ R ∧ pointwiseTernaryXor f g h ∉ R := by
  unfold IsAffine; push Not; rfl

/-- If R is affine, then for any f, g, h ∈ R, their ternary XOR is also in R. -/
theorem affine_mem_ternary_xor {k : Nat} {R : LogRel k} (hAff : IsAffine R)
    {f g h : Fin k → Bool} (hf : f ∈ R) (hg : g ∈ R) (hh : h ∈ R) :
    pointwiseTernaryXor f g h ∈ R := hAff hf hg hh

/-- If R is affine and f, g ∈ R, then f⊕g⊕g = f ∈ R (obvious, but shows
    ternary XOR "cancels" the second argument when repeated). -/
theorem affine_xor_self_cancel {k : Nat} {R : LogRel k} (hAff : IsAffine R)
    {f g : Fin k → Bool} (hf : f ∈ R) (hg : g ∈ R) :
    pointwiseTernaryXor f g g ∈ R :=
  hAff hf hg hg

/-- If R is affine, then the "difference" operation f⊕g⊕h preserves membership.
    That is, pointwiseTernaryXor acts as an affine combination in the group
    (ZMod 2)^k, and R is closed under this operation. -/
theorem affine_ternary_xor_assoc {k : Nat} {R : LogRel k} (hAff : IsAffine R)
    {a b c d : Fin k → Bool} (ha : a ∈ R) (hb : b ∈ R)
    (hc : c ∈ R) (hd : d ∈ R) :
    pointwiseTernaryXor (pointwiseTernaryXor a b c) d (pointwiseTernaryXor a b d) ∈ R := by
  exact hAff (hAff ha hb hc) hd (hAff ha hb hd)

/--
If R is affine and contains a, complement a, and constTrue, then constFalse ∈ R.

Proof: pointwiseTernaryXor a (complement a) constTrue = constFalse, since at each
position i, XOR(a_i, ¬a_i, true) counts 2 trues (if a_i=T: T,F,T → 2 true → false;
if a_i=F: F,T,T → 2 true → false). So the result is all-false.

Note: The version without constTrue is false (counterexample: R = {(T,F), (F,T)}).
-/
theorem affine_of_complement_pair_zero_valid {k : Nat} {R : LogRel k}
    (hAff : IsAffine R) {a : Fin k → Bool} (ha : a ∈ R)
    (hac : complement a ∈ R) (hOne : constTrue ∈ R) :
    constFalse ∈ R := by
  have key : pointwiseTernaryXor a (complement a) constTrue = constFalse := by
    funext i
    unfold pointwiseTernaryXor complement constTrue constFalse
    cases a i <;> simp
  rw [← key]
  exact hAff ha hac hOne

/-! ## Affine Subspace Characterization (Deferred)

The full characterization states: IsAffine R ↔ R is a coset (affine subspace) of
(ZMod 2)^k. This requires substantial linear algebra infrastructure and is deferred.
The forward direction (affine → subspace) uses the fact that the set
{f ⊕ g ⊕ h : f,g,h ∈ R} stabilizes to a subspace, and the backward direction
(trivially) follows from closure of affine subspaces under (a+b+c) in ZMod 2.
-/

end LocalRep