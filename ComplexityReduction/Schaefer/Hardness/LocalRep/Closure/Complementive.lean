/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Schaefer.Hardness.LocalRep.SAT.LogicalRelation

namespace ComplexityReduction.Schaefer.Hardness.LocalRep

open LogRel

/-! ## Complementive Relations

A logical relation R is **complementive** if for every tuple t ∈ R,
the bitwise complement of t is also in R. This is equivalent to
R being closed under the complementation operation on Boolean tuples.

Complementive relations play a role in the classification theorem:
a relation is complementive iff it contains both a 0-valid and 1-valid
"partner" tuple, which connects to the weakly positive / weakly negative
properties.
-/

/-- The bitwise complement of a Boolean tuple. -/
def complement {k : Nat} (t : Fin k → Bool) : Fin k → Bool :=
  fun i => !(t i)

/-- A relation is complementive if it is closed under complement:
    for every tuple t ∈ R, the complement of t is also in R. -/
def IsComplementive {k : Nat} (R : LogRel k) : Prop :=
  ∀ t ∈ R, complement t ∈ R

namespace IsComplementive

/-- A relation is complementive iff it equals its own complement set. -/
theorem iff_complement_eq_self {k : Nat} (R : LogRel k) :
    IsComplementive R ↔ Finset.filter (fun t => complement t ∈ R) R = R := by
  constructor
  · intro h
    apply Finset.filter_true_of_mem
    intro t ht
    exact h t ht
  · intro h t ht
    have hmem : t ∈ Finset.filter (fun t => complement t ∈ R) R := by rw [h]; exact ht
    exact (Finset.mem_filter.mp hmem).2

/-- The empty relation is complementive (vacuously true). -/
theorem empty : IsComplementive (∅ : LogRel 0) := by
  intro t ht; simp at ht

/-- Complementive relations are symmetric with respect to 0 and 1:
    if (a₁,...,aₖ) ∈ R, then (¬a₁,...,¬aₖ) ∈ R.
    In particular, if R contains the all-true tuple, it contains
    the all-false tuple, and vice versa. -/
theorem zero_one_symmetric {k : Nat} {R : LogRel k}
    (h : IsComplementive R) :
    constTrue ∈ R ↔ constFalse ∈ R := by
  have hc1 : complement (constTrue : Fin k → Bool) = constFalse := by
    funext i; simp [complement, constTrue, constFalse]
  have hc2 : complement (constFalse : Fin k → Bool) = constTrue := by
    funext i; simp [complement, constTrue, constFalse]
  constructor
  · intro ht; rw [← hc1]; exact h constTrue ht
  · intro hf; rw [← hc2]; exact h constFalse hf

end IsComplementive

/-- The complement closure: the union of R and the set of complements of tuples in R. -/
def complementClosure {k : Nat} (R : LogRel k) : LogRel k :=
  R ∪ Finset.filter (fun t => complement t ∈ R) Finset.univ

theorem mem_complementClosure {k : Nat} {R : LogRel k} {t : Fin k → Bool} :
    t ∈ complementClosure R ↔ t ∈ R ∨ complement t ∈ R := by
  simp [complementClosure, Finset.mem_union, Finset.mem_filter, Finset.mem_univ]

end LocalRep