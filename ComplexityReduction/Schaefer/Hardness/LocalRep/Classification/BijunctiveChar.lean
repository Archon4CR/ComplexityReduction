/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Schaefer.Hardness.LocalRep.SAT.LogicalRelation
import ComplexityReduction.Schaefer.Hardness.LocalRep.Closure.Operations

namespace ComplexityReduction.Schaefer.Hardness.LocalRep

open LogRel

/-! ## Bijunctive Characterization (Lemma 3.1B)

A relation R is **bijunctive** iff it is closed under the majority operation
(pointwiseMaj), equivalently iff R can be expressed as a conjunction of
2-literal clauses (2-SAT formulas).

This file provides:
- Negation witness: ¬IsBijunctive R ↔ ∃ f,g,h ∈ R with maj(f,g,h) ∉ R
- Change set definition and properties
- The full bijunctive characterization (deferred)
-/

/-! ## Negation Witness for Bijunctive Relations
-/

/-- Not bijunctive ↔ there exist three tuples in R whose majority is not in R. -/
theorem not_bijunctive_iff {k : Nat} {R : LogRel k} :
    ¬ IsBijunctive R ↔ ∃ f, ∃ g, ∃ h, f ∈ R ∧ g ∈ R ∧ h ∈ R ∧ pointwiseMaj f g h ∉ R := by
  unfold IsBijunctive; push Not; rfl

/-- If R is bijunctive, then for any f, g, h ∈ R, their majority is also in R. -/
theorem bijunctive_mem_maj {k : Nat} {R : LogRel k} (hBij : IsBijunctive R)
    {f g h : Fin k → Bool} (hf : f ∈ R) (hg : g ∈ R) (hh : h ∈ R) :
    pointwiseMaj f g h ∈ R := hBij hf hg hh

/-! ## Change Sets

The **change set** between two tuples f, g : Fin k → Bool is the set of
positions where they differ. A relation R is bijunctive iff for every triple
of tuples in R, the majority is also in R. Equivalently, R is bijunctive iff
it is characterized by its "2-variable" restrictions.
-/

/-- The change set (set of differing positions) between two tuples. -/
def changeSet {k : Nat} (f g : Fin k → Bool) : Finset (Fin k) :=
  Finset.filter (fun i => f i ≠ g i) Finset.univ

/-- The change set is symmetric. -/
theorem changeSet_symm {k : Nat} (f g : Fin k → Bool) :
    changeSet f g = changeSet g f := by
  unfold changeSet
  ext i
  simp [Finset.mem_filter, Finset.mem_univ, ne_comm]

/-- The change set of a tuple with itself is empty. -/
@[simp] theorem changeSet_self {k : Nat} (f : Fin k → Bool) :
    changeSet f f = ∅ := by
  unfold changeSet
  ext i
  simp

/-- Positions in the change set are exactly where the tuples differ. -/
@[simp] theorem mem_changeSet {k : Nat} {f g : Fin k → Bool} {i : Fin k} :
    i ∈ changeSet f g ↔ f i ≠ g i := by
  unfold changeSet; simp [Finset.mem_filter, Finset.mem_univ]

/-! ## Bijunctive Characterization via Change Sets (Deferred)

The full characterization: R is bijunctive iff for every restriction of k-2
variables to constants, the resulting binary relation is a 2-SAT relation
(i.e., expressible as conjunction of 2-literal clauses).

This characterization connects to the "change set" notion: a bijunctive relation
R has the property that for every triple a, b, c with pairwise change sets
of size at most 2, the majority must be in R. The deep characterization
(2-SAT representability) is deferred.
-/

/-- A binary relation obtained from a k-ary relation R by fixing k-2 of the
    variables to constants. This is the "2-variable restriction" of R obtained
    by substituting constant values for all but 2 variables. -/
def binaryRestriction {k : Nat} (R : LogRel k) (f : Fin k → Fin 2 ⊕ Bool) :
    LogRel 2 :=
  substitute R f

/-- If R is bijunctive, then every binary restriction of R is also bijunctive.
    Proof deferred: requires lifting majority through substitution. -/
theorem bijunctive_of_bijunctive_binaryRestriction {k : Nat} {R : LogRel k}
    (hBij : IsBijunctive R) (f : Fin k → Fin 2 ⊕ Bool) :
    IsBijunctive (binaryRestriction R f) := by
  unfold binaryRestriction
  intro a b c ha hb hc
  rw [mem_substitute] at ha hb hc ⊢
  have key : substApply f (pointwiseMaj a b c) = pointwiseMaj (substApply f a) (substApply f b) (substApply f c) := by
    funext i
    simp [substApply, pointwiseMaj]
    cases f i with
    | inl j => rfl
    | inr b => simp [Bool.or_self, Bool.and_self]
  rw [key]
  exact hBij ha hb hc

end LocalRep
