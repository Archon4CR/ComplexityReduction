/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Polymorphisms.Bool
import ComplexityReduction.CSP.SatLike
import ComplexityReduction.Certificates.CostedMap
import ComplexityReduction.Core.NPClass

/-!
Generic empty-relation preprocessing for finite Boolean CSP languages.

If a formula uses an empty relation, it is immediately unsatisfiable.  Otherwise
the formula restricts to the sublanguage of nonempty relations.  This is a
syntax-level preprocessing layer for any Boolean CSP route; Schaefer's final
dichotomy wrapper reuses it through compatibility names.
-/

namespace ComplexityReduction
namespace CSP
namespace Preprocessing

/-- The language has at least one empty relation symbol. -/
def HasEmptyRelation (Γ : BoolLanguage) : Prop :=
  ∃ s : Γ.Symbol, ¬ (Γ.relationOf s).Nonempty

/-- A constraint uses an empty relation. -/
def ConstraintUsesEmptyRelation {Γ : BoolLanguage} (c : Constraint Γ) : Prop :=
  ¬ (Constraint.relation c).Nonempty

/-- A formula contains at least one constraint over an empty relation. -/
def FormulaContainsEmptyRelation {Γ : BoolLanguage} (φ : Formula Γ) : Prop :=
  ∃ c ∈ φ, ConstraintUsesEmptyRelation c

noncomputable instance hasEmptyRelationDecidable (Γ : BoolLanguage) :
    Decidable (HasEmptyRelation Γ) := by
  classical
  infer_instance

noncomputable instance formulaContainsEmptyRelationDecidable {Γ : BoolLanguage}
    (φ : Formula Γ) : Decidable (FormulaContainsEmptyRelation φ) := by
  classical
  infer_instance

/-- A finite language either has an empty relation or all of its relations are nonempty. -/
theorem hasEmptyRelation_or_allRelationsNonempty (Γ : BoolLanguage) :
    HasEmptyRelation Γ ∨ AllRelationsNonempty Γ := by
  classical
  by_cases h : HasEmptyRelation Γ
  · exact Or.inl h
  · exact Or.inr (by
      intro s
      by_contra hs
      exact h ⟨s, hs⟩)

/-- If a constraint uses an empty relation, no assignment can satisfy it. -/
theorem constraint_unsat_of_empty_relation {Γ : BoolLanguage}
    {c : Constraint Γ} (hEmpty : ConstraintUsesEmptyRelation c)
    (a : SAT.Assignment) :
    ¬ Constraint.Satisfies c a := by
  intro hSat
  exact hEmpty ⟨c.assignmentTuple a, hSat⟩

/-- If a formula contains an empty-relation constraint, it is unsatisfiable. -/
theorem formula_unsat_of_containsEmptyRelation {Γ : BoolLanguage}
    {φ : Formula Γ} (hEmpty : FormulaContainsEmptyRelation φ) :
    ¬ Formula.Satisfiable φ := by
  rintro ⟨a, hSat⟩
  rcases hEmpty with ⟨c, hc, hcEmpty⟩
  exact constraint_unsat_of_empty_relation hcEmpty a (hSat c hc)

/-- If no empty-relation constraint is present, every used constraint has a nonempty relation. -/
theorem all_constraints_nonempty_of_not_containsEmptyRelation {Γ : BoolLanguage}
    {φ : Formula Γ} (hNoEmpty : ¬ FormulaContainsEmptyRelation φ) :
    ∀ c ∈ φ, (Constraint.relation c).Nonempty := by
  intro c hc
  by_contra hEmpty
  exact hNoEmpty ⟨c, hc, hEmpty⟩

/-- Symbols of the sublanguage consisting only of nonempty relations. -/
abbrev NonemptySymbol (Γ : BoolLanguage) : Type :=
  { s : Γ.Symbol // (Γ.relationOf s).Nonempty }

/-- The sublanguage obtained by deleting every empty relation symbol. -/
noncomputable def nonemptySubLanguage (Γ : BoolLanguage) : BoolLanguage where
  Symbol := NonemptySymbol Γ
  finiteSymbol := by
    classical
    infer_instance
  relationOf s := Γ.relationOf s.1

/-- The nonempty sublanguage satisfies the nonempty-relation precondition. -/
theorem nonemptySubLanguage_allRelationsNonempty (Γ : BoolLanguage) :
    AllRelationsNonempty (nonemptySubLanguage Γ) := by
  intro s
  exact s.2

/-- Lift one constraint over the nonempty sublanguage back to the original language. -/
def liftNonemptyConstraint {Γ : BoolLanguage}
    (c : Constraint (nonemptySubLanguage Γ)) : Constraint Γ where
  symbol := c.symbol.1
  vars := c.vars

/-- Lift a formula over the nonempty sublanguage back to the original language. -/
def liftNonemptyFormula {Γ : BoolLanguage}
    (φ : Formula (nonemptySubLanguage Γ)) : Formula Γ :=
  φ.map liftNonemptyConstraint

@[simp]
theorem liftNonemptyConstraint_satisfies_iff {Γ : BoolLanguage}
    (c : Constraint (nonemptySubLanguage Γ)) (a : SAT.Assignment) :
    Constraint.Satisfies (liftNonemptyConstraint c) a ↔ Constraint.Satisfies c a :=
  Iff.rfl

@[simp]
theorem liftNonemptyFormula_satisfies_iff {Γ : BoolLanguage}
    (φ : Formula (nonemptySubLanguage Γ)) (a : SAT.Assignment) :
    Formula.Satisfies (liftNonemptyFormula φ) a ↔ Formula.Satisfies φ a := by
  induction φ with
  | nil =>
      simp [liftNonemptyFormula]
  | cons c φ ih =>
      simp only [liftNonemptyFormula, List.map_cons, Formula.satisfies_cons,
        liftNonemptyConstraint_satisfies_iff]
      exact and_congr Iff.rfl ih

/-- Lifting from the nonempty sublanguage preserves satisfiability exactly. -/
theorem liftNonemptyFormula_satisfiable_iff {Γ : BoolLanguage}
    (φ : Formula (nonemptySubLanguage Γ)) :
    Formula.Satisfiable (liftNonemptyFormula φ) ↔ Formula.Satisfiable φ := by
  constructor
  · rintro ⟨a, hSat⟩
    exact ⟨a, (liftNonemptyFormula_satisfies_iff φ a).1 hSat⟩
  · rintro ⟨a, hSat⟩
    exact ⟨a, (liftNonemptyFormula_satisfies_iff φ a).2 hSat⟩

/-- Restrict one known-nonempty constraint to the nonempty sublanguage. -/
def restrictNonemptyConstraint {Γ : BoolLanguage} (c : Constraint Γ)
    (hNonempty : (Constraint.relation c).Nonempty) :
    Constraint (nonemptySubLanguage Γ) where
  symbol := ⟨c.symbol, hNonempty⟩
  vars := c.vars

/-- Restrict a formula with no empty-relation constraints to the nonempty sublanguage. -/
def restrictFormulaNoEmpty {Γ : BoolLanguage} :
    (φ : Formula Γ) →
      (∀ c ∈ φ, (Constraint.relation c).Nonempty) →
        Formula (nonemptySubLanguage Γ)
  | [], _ => []
  | c :: φ, hNonempty =>
      restrictNonemptyConstraint c (hNonempty c (by simp)) ::
        restrictFormulaNoEmpty φ (by
          intro d hd
          exact hNonempty d (by simp [hd]))

@[simp]
theorem restrictNonemptyConstraint_satisfies_iff {Γ : BoolLanguage}
    (c : Constraint Γ) (hNonempty : (Constraint.relation c).Nonempty)
    (a : SAT.Assignment) :
    Constraint.Satisfies (restrictNonemptyConstraint c hNonempty) a ↔
      Constraint.Satisfies c a :=
  Iff.rfl

/-- Restricting a formula that avoids empty relations preserves assignment satisfaction. -/
theorem restrictFormulaNoEmpty_satisfies_iff {Γ : BoolLanguage}
    (φ : Formula Γ)
    (hNonempty : ∀ c ∈ φ, (Constraint.relation c).Nonempty)
    (a : SAT.Assignment) :
    Formula.Satisfies (restrictFormulaNoEmpty φ hNonempty) a ↔
      Formula.Satisfies φ a := by
  induction φ with
  | nil =>
      simp [restrictFormulaNoEmpty]
  | cons c φ ih =>
      simp only [restrictFormulaNoEmpty, Formula.satisfies_cons,
        restrictNonemptyConstraint_satisfies_iff]
      exact and_congr Iff.rfl
        (ih (by
          intro d hd
          exact hNonempty d (by simp [hd])))

/-- Restricting a formula that avoids empty relations preserves satisfiability exactly. -/
theorem restrictFormulaNoEmpty_satisfiable_iff {Γ : BoolLanguage}
    (φ : Formula Γ)
    (hNonempty : ∀ c ∈ φ, (Constraint.relation c).Nonempty) :
    Formula.Satisfiable (restrictFormulaNoEmpty φ hNonempty) ↔ Formula.Satisfiable φ := by
  constructor
  · rintro ⟨a, hSat⟩
    exact ⟨a, (restrictFormulaNoEmpty_satisfies_iff φ hNonempty a).1 hSat⟩
  · rintro ⟨a, hSat⟩
    exact ⟨a, (restrictFormulaNoEmpty_satisfies_iff φ hNonempty a).2 hSat⟩

/-- Every formula either is immediately unsatisfiable or restricts to the nonempty sublanguage. -/
theorem containsEmptyRelation_or_restricts {Γ : BoolLanguage} (φ : Formula Γ) :
    FormulaContainsEmptyRelation φ ∨
      ∃ hNonempty : ∀ c ∈ φ, (Constraint.relation c).Nonempty,
        Formula.Satisfiable (restrictFormulaNoEmpty φ hNonempty) ↔ Formula.Satisfiable φ := by
  classical
  by_cases hEmpty : FormulaContainsEmptyRelation φ
  · exact Or.inl hEmpty
  · exact Or.inr
      ⟨ all_constraints_nonempty_of_not_containsEmptyRelation hEmpty
      , restrictFormulaNoEmpty_satisfiable_iff φ
          (all_constraints_nonempty_of_not_containsEmptyRelation hEmpty) ⟩

/-- Cost certificate for the inclusion map from the nonempty sublanguage to the original one. -/
theorem liftNonemptyFormula_polynomialSizeBound (Γ : BoolLanguage) :
    PolynomialSizeBound
      (fun φ : Formula (nonemptySubLanguage Γ) =>
        (boolCSPDecisionProblem (nonemptySubLanguage Γ)).Instance.inputSize φ)
      (fun φ : Formula Γ => (boolCSPDecisionProblem Γ).Instance.inputSize φ)
      liftNonemptyFormula := by
  refine PolynomialSizeBound.intro_with 1 1 0 ?_
  intro φ
  induction φ with
  | nil =>
      simp [liftNonemptyFormula, boolCSPDecisionProblem, boolCSPSatLike,
        SatLikeProblem.toDecisionProblem, EncodedType.inputSize, formulaEncodedType,
        Encoding.encodeFormula]
  | cons c φ ih =>
      have hHead :
          (List.ofFn
            ((fun n : Nat => (EncodedType.nat.encode n).length + 1) ∘
              (liftNonemptyConstraint c).vars)).sum =
            (List.ofFn
              ((fun n : Nat => (EncodedType.nat.encode n).length + 1) ∘ c.vars)).sum := rfl
      simp [liftNonemptyFormula, boolCSPDecisionProblem, boolCSPSatLike,
        SatLikeProblem.toDecisionProblem, EncodedType.inputSize, formulaEncodedType,
        Encoding.encodeFormula, Encoding.encodeConstraint, Encoding.encodeVar,
        Encoding.encodeNat] at ih ⊢
      exact Nat.add_le_add (le_of_eq hHead) ih

/-- Karp reduction from the nonempty sublanguage SAT problem to the original SAT problem. -/
noncomputable def nonemptySubLanguageToOriginalKarpReduction (Γ : BoolLanguage) :
    KarpReductionM CostedPolyTimeModel
      (boolCSPDecisionProblem (nonemptySubLanguage Γ))
      (boolCSPDecisionProblem Γ) where
  f :=
    { toFun := liftNonemptyFormula
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            (liftNonemptyFormula_polynomialSizeBound Γ)) }
  correct := by
    intro φ
    exact (liftNonemptyFormula_satisfiable_iff φ).symm

/-- If the nonempty sublanguage is in P, then the original language is in P by empty scanning. -/
theorem boolCSP_inP_of_nonemptySubLanguage_inP {Γ : BoolLanguage}
    (hP : InP CostedPolyTimeModel (boolCSPDecisionProblem (nonemptySubLanguage Γ))) :
    InP CostedPolyTimeModel (boolCSPDecisionProblem Γ) := by
  classical
  rcases hP with ⟨d⟩
  let decide : Formula Γ → Bool :=
    fun φ =>
      if hEmpty : FormulaContainsEmptyRelation φ then
        false
      else
        d.decide.toFun
          (restrictFormulaNoEmpty φ
            (all_constraints_nonempty_of_not_containsEmptyRelation hEmpty))
  have hPoly :
      CostedPolyTimeMap
        (X := (boolCSPDecisionProblem Γ).Instance) (Y := EncodedType.bool) decide := by
    refine CostedPolyTimeMap.of_costed (CostedMap.of_encodedPolynomialSizeBound ?_)
    refine PolynomialSizeBound.intro_with 0 0 1 ?_
    intro φ
    simp [EncodedType.inputSize, EncodedType.bool]
  refine InP.intro { toFun := decide, polytime := hPoly } ?_
  intro φ
  by_cases hEmpty : FormulaContainsEmptyRelation φ
  · constructor
    · intro h
      simp [decide, hEmpty] at h
    · intro hSat
      exact False.elim (formula_unsat_of_containsEmptyRelation hEmpty hSat)
  · have hNonempty := all_constraints_nonempty_of_not_containsEmptyRelation hEmpty
    have hDecide := d.correct (restrictFormulaNoEmpty φ hNonempty)
    have hRestrict := restrictFormulaNoEmpty_satisfiable_iff φ hNonempty
    simpa [decide, hEmpty, boolCSPDecisionProblem_isYes_iff] using hDecide.trans hRestrict

/--
If the nonempty sublanguage is NP-complete, then the original language is
NP-complete, provided the original Boolean CSP problem has already been placed
in NP by the caller's chosen boundary.
-/
theorem boolCSP_npComplete_of_nonemptySubLanguage_npComplete
    {Γ : BoolLanguage}
    (hNPC : NPCompleteEnc CostedPolyTimeModel
      (boolCSPDecisionProblem (nonemptySubLanguage Γ)))
    (hΓInNP : InNPEnc CostedPolyTimeModel (boolCSPDecisionProblem Γ)) :
    NPCompleteEnc CostedPolyTimeModel (boolCSPDecisionProblem Γ) :=
  NPCompleteEnc.transfer hNPC
    ⟨nonemptySubLanguageToOriginalKarpReduction Γ⟩
    hΓInNP

/-- Transfer a dichotomy result for the nonempty sublanguage back to the original language. -/
theorem boolCSP_dichotomy_of_nonemptySubLanguage_dichotomy
    {Γ : BoolLanguage}
    (hDichotomy :
      InP CostedPolyTimeModel (boolCSPDecisionProblem (nonemptySubLanguage Γ)) ∨
        NPCompleteEnc CostedPolyTimeModel (boolCSPDecisionProblem (nonemptySubLanguage Γ)))
    (hΓInNP : InNPEnc CostedPolyTimeModel (boolCSPDecisionProblem Γ)) :
    InP CostedPolyTimeModel (boolCSPDecisionProblem Γ) ∨
      NPCompleteEnc CostedPolyTimeModel (boolCSPDecisionProblem Γ) := by
  rcases hDichotomy with hP | hNPC
  · exact Or.inl (boolCSP_inP_of_nonemptySubLanguage_inP hP)
  · exact Or.inr (boolCSP_npComplete_of_nonemptySubLanguage_npComplete hNPC hΓInNP)

end Preprocessing
end CSP
end ComplexityReduction
