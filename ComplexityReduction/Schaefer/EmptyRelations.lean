/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Preprocessing.EmptyRelations
import ComplexityReduction.CSP.InNP
import ComplexityReduction.Schaefer.Hardness.Constants

/-!
Compatibility wrapper for empty-relation handling in the local Schaefer
`SAT(S)` route.

The generic preprocessing theorem now lives in
`ComplexityReduction.CSP.Preprocessing.EmptyRelations`.  This module keeps the
Schaefer-facing theorem names used by the P9 dichotomy wrapper.
-/

namespace ComplexityReduction
namespace Schaefer

abbrev HasEmptyRelation (Γ : CSP.BoolLanguage) : Prop :=
  CSP.Preprocessing.HasEmptyRelation Γ

abbrev ConstraintUsesEmptyRelation {Γ : CSP.BoolLanguage} (c : CSP.Constraint Γ) : Prop :=
  CSP.Preprocessing.ConstraintUsesEmptyRelation c

abbrev FormulaContainsEmptyRelation {Γ : CSP.BoolLanguage} (φ : SATFormula Γ) : Prop :=
  CSP.Preprocessing.FormulaContainsEmptyRelation φ

noncomputable instance hasEmptyRelationDecidable (Γ : CSP.BoolLanguage) :
    Decidable (HasEmptyRelation Γ) :=
  CSP.Preprocessing.hasEmptyRelationDecidable Γ

noncomputable instance formulaContainsEmptyRelationDecidable {Γ : CSP.BoolLanguage}
    (φ : SATFormula Γ) : Decidable (FormulaContainsEmptyRelation φ) :=
  CSP.Preprocessing.formulaContainsEmptyRelationDecidable φ

theorem hasEmptyRelation_or_allRelationsNonempty (Γ : CSP.BoolLanguage) :
    HasEmptyRelation Γ ∨ Hardness.AllRelationsNonempty Γ :=
  CSP.Preprocessing.hasEmptyRelation_or_allRelationsNonempty Γ

theorem constraint_unsat_of_empty_relation {Γ : CSP.BoolLanguage}
    {c : CSP.Constraint Γ} (hEmpty : ConstraintUsesEmptyRelation c)
    (a : SAT.Assignment) :
    ¬ CSP.Constraint.Satisfies c a :=
  CSP.Preprocessing.constraint_unsat_of_empty_relation hEmpty a

theorem formula_unsat_of_containsEmptyRelation {Γ : CSP.BoolLanguage}
    {φ : SATFormula Γ} (hEmpty : FormulaContainsEmptyRelation φ) :
    ¬ SATSatisfiable φ :=
  CSP.Preprocessing.formula_unsat_of_containsEmptyRelation hEmpty

theorem all_constraints_nonempty_of_not_containsEmptyRelation {Γ : CSP.BoolLanguage}
    {φ : SATFormula Γ} (hNoEmpty : ¬ FormulaContainsEmptyRelation φ) :
    ∀ c ∈ φ, (CSP.Constraint.relation c).Nonempty :=
  CSP.Preprocessing.all_constraints_nonempty_of_not_containsEmptyRelation hNoEmpty

abbrev NonemptySymbol (Γ : CSP.BoolLanguage) : Type :=
  CSP.Preprocessing.NonemptySymbol Γ

noncomputable abbrev nonemptySubLanguage (Γ : CSP.BoolLanguage) : CSP.BoolLanguage :=
  CSP.Preprocessing.nonemptySubLanguage Γ

theorem nonemptySubLanguage_allRelationsNonempty (Γ : CSP.BoolLanguage) :
    Hardness.AllRelationsNonempty (nonemptySubLanguage Γ) :=
  CSP.Preprocessing.nonemptySubLanguage_allRelationsNonempty Γ

abbrev liftNonemptyConstraint {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint (nonemptySubLanguage Γ)) : CSP.Constraint Γ :=
  CSP.Preprocessing.liftNonemptyConstraint c

abbrev liftNonemptyFormula {Γ : CSP.BoolLanguage}
    (φ : SATFormula (nonemptySubLanguage Γ)) : SATFormula Γ :=
  CSP.Preprocessing.liftNonemptyFormula φ

@[simp]
theorem liftNonemptyConstraint_satisfies_iff {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint (nonemptySubLanguage Γ)) (a : SAT.Assignment) :
    CSP.Constraint.Satisfies (liftNonemptyConstraint c) a ↔
      CSP.Constraint.Satisfies c a :=
  CSP.Preprocessing.liftNonemptyConstraint_satisfies_iff c a

@[simp]
theorem liftNonemptyFormula_satisfies_iff {Γ : CSP.BoolLanguage}
    (φ : SATFormula (nonemptySubLanguage Γ)) (a : SAT.Assignment) :
    CSP.Formula.Satisfies (liftNonemptyFormula φ) a ↔ CSP.Formula.Satisfies φ a :=
  CSP.Preprocessing.liftNonemptyFormula_satisfies_iff φ a

theorem liftNonemptyFormula_satisfiable_iff {Γ : CSP.BoolLanguage}
    (φ : SATFormula (nonemptySubLanguage Γ)) :
    SATSatisfiable (liftNonemptyFormula φ) ↔ SATSatisfiable φ :=
  CSP.Preprocessing.liftNonemptyFormula_satisfiable_iff φ

abbrev restrictNonemptyConstraint {Γ : CSP.BoolLanguage} (c : CSP.Constraint Γ)
    (hNonempty : (CSP.Constraint.relation c).Nonempty) :
    CSP.Constraint (nonemptySubLanguage Γ) :=
  CSP.Preprocessing.restrictNonemptyConstraint c hNonempty

abbrev restrictFormulaNoEmpty {Γ : CSP.BoolLanguage}
    (φ : SATFormula Γ)
    (hNonempty : ∀ c ∈ φ, (CSP.Constraint.relation c).Nonempty) :
    SATFormula (nonemptySubLanguage Γ) :=
  CSP.Preprocessing.restrictFormulaNoEmpty φ hNonempty

@[simp]
theorem restrictNonemptyConstraint_satisfies_iff {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint Γ) (hNonempty : (CSP.Constraint.relation c).Nonempty)
    (a : SAT.Assignment) :
    CSP.Constraint.Satisfies (restrictNonemptyConstraint c hNonempty) a ↔
      CSP.Constraint.Satisfies c a :=
  CSP.Preprocessing.restrictNonemptyConstraint_satisfies_iff c hNonempty a

theorem restrictFormulaNoEmpty_satisfies_iff {Γ : CSP.BoolLanguage}
    (φ : SATFormula Γ)
    (hNonempty : ∀ c ∈ φ, (CSP.Constraint.relation c).Nonempty)
    (a : SAT.Assignment) :
    CSP.Formula.Satisfies (restrictFormulaNoEmpty φ hNonempty) a ↔
      CSP.Formula.Satisfies φ a :=
  CSP.Preprocessing.restrictFormulaNoEmpty_satisfies_iff φ hNonempty a

theorem restrictFormulaNoEmpty_satisfiable_iff {Γ : CSP.BoolLanguage}
    (φ : SATFormula Γ)
    (hNonempty : ∀ c ∈ φ, (CSP.Constraint.relation c).Nonempty) :
    SATSatisfiable (restrictFormulaNoEmpty φ hNonempty) ↔ SATSatisfiable φ :=
  CSP.Preprocessing.restrictFormulaNoEmpty_satisfiable_iff φ hNonempty

theorem containsEmptyRelation_or_restricts {Γ : CSP.BoolLanguage} (φ : SATFormula Γ) :
    FormulaContainsEmptyRelation φ ∨
      ∃ hNonempty : ∀ c ∈ φ, (CSP.Constraint.relation c).Nonempty,
        SATSatisfiable (restrictFormulaNoEmpty φ hNonempty) ↔ SATSatisfiable φ :=
  CSP.Preprocessing.containsEmptyRelation_or_restricts φ

theorem liftNonemptyFormula_polynomialSizeBound (Γ : CSP.BoolLanguage) :
    PolynomialSizeBound
      (fun φ : SATFormula (nonemptySubLanguage Γ) =>
        (satSDecisionProblem (nonemptySubLanguage Γ)).Instance.inputSize φ)
      (fun φ : SATFormula Γ => (satSDecisionProblem Γ).Instance.inputSize φ)
      liftNonemptyFormula :=
  CSP.Preprocessing.liftNonemptyFormula_polynomialSizeBound Γ

noncomputable def nonemptySubLanguageToOriginalKarpReduction (Γ : CSP.BoolLanguage) :
    KarpReductionM CostedPolyTimeModel
      (satSDecisionProblem (nonemptySubLanguage Γ))
      (satSDecisionProblem Γ) :=
  CSP.Preprocessing.nonemptySubLanguageToOriginalKarpReduction Γ

theorem satS_inP_of_nonemptySubLanguage_inP {Γ : CSP.BoolLanguage}
    (hP : InP CostedPolyTimeModel (satSDecisionProblem (nonemptySubLanguage Γ))) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) :=
  CSP.Preprocessing.boolCSP_inP_of_nonemptySubLanguage_inP hP

theorem satS_npComplete_of_nonemptySubLanguage_npComplete
    {Γ : CSP.BoolLanguage}
    (hNPC : NPCompleteEnc CostedPolyTimeModel
      (satSDecisionProblem (nonemptySubLanguage Γ)))
    (B : Targets.ThreeSATCompleteBoundary) :
    NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem Γ) := by
  exact CSP.Preprocessing.boolCSP_npComplete_of_nonemptySubLanguage_npComplete hNPC
    (CSP.boolCSPInNP_of_threeSATInNP Γ B.complete.1)

theorem satS_dichotomy_of_nonemptySubLanguage_dichotomy
    {Γ : CSP.BoolLanguage}
    (hDichotomy :
      InP CostedPolyTimeModel (satSDecisionProblem (nonemptySubLanguage Γ)) ∨
        NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem (nonemptySubLanguage Γ)))
    (B : Targets.ThreeSATCompleteBoundary) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) ∨
      NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem Γ) := by
  exact CSP.Preprocessing.boolCSP_dichotomy_of_nonemptySubLanguage_dichotomy hDichotomy
    (CSP.boolCSPInNP_of_threeSATInNP Γ B.complete.1)

/-- Descriptor for the empty-relation preprocessing wrapper. -/
def emptyRelationWrapperDescriptor : StatementDescriptor :=
  { pdfReference := "Section 4, proof of Theorem 2.1; Lemma 4.3 nonempty note"
    informalClaim :=
      "Before applying the nonempty-relation hard-side theorem, scan for empty-relation \
       constraints; formulas using one are unsatisfiable, and all other formulas restrict \
       to the sublanguage of nonempty relations."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.satS_dichotomy_of_nonemptySubLanguage_dichotomy"
    dependencies :=
      [ "ComplexityReduction.CSP.Preprocessing.formula_unsat_of_containsEmptyRelation"
      , "ComplexityReduction.CSP.Preprocessing.restrictFormulaNoEmpty_satisfiable_iff"
      , "ComplexityReduction.CSP.Preprocessing.nonemptySubLanguageToOriginalKarpReduction"
      , "ComplexityReduction.CSP.Preprocessing.nonemptySubLanguage_allRelationsNonempty"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "This is the local empty-relation elimination wrapper over the generic CSP \
       preprocessing layer; Cook-Levin remains represented only by \
       Targets.ThreeSATCompleteBoundary." }

end Schaefer
end ComplexityReduction
