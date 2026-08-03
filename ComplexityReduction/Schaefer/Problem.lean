/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Core.ProblemEquiv
import ComplexityReduction.Certificates.CostedMap
import ComplexityReduction.CSP.SatLike
import ComplexityReduction.Schaefer.Relations

/-!
Local `SAT(S)` view for finite Boolean relation families.

The paper's `S`-formula layer is represented here by the repository's existing
`CSP.Formula Γ`; the adapter is intentionally explicit so future transport work
has one named target instead of relying on similar theorem names.
-/

namespace ComplexityReduction
namespace Schaefer

/-- Local `S`-formula syntax, represented by the existing Boolean CSP formula type. -/
abbrev SATFormula (Γ : CSP.BoolLanguage) : Type :=
  CSP.Formula Γ

/-- Local satisfiability predicate for `SAT(S)`. -/
abbrev SATSatisfiable {Γ : CSP.BoolLanguage} (φ : SATFormula Γ) : Prop :=
  CSP.Formula.Satisfiable φ

/-- Local encoded decision problem for Schaefer's `SAT(S)`. -/
def satSDecisionProblem (Γ : CSP.BoolLanguage) : EncodedDecisionProblem :=
  CSP.boolCSPDecisionProblem Γ

@[simp]
theorem satSDecisionProblem_isYes_iff (Γ : CSP.BoolLanguage) (φ : SATFormula Γ) :
    (satSDecisionProblem Γ).isYes φ ↔ SATSatisfiable φ :=
  Iff.rfl

/--
Adapter from the local `SAT(S)` view to the existing Boolean CSP decision
problem.  It is currently definitional, but keeping this as a named object gives
future external-transport work a stable hook.
-/
def satS_problem_equiv_boolCSP (Γ : CSP.BoolLanguage) :
    ProblemEquivM CostedPolyTimeModel (satSDecisionProblem Γ) (CSP.boolCSPDecisionProblem Γ) :=
  ProblemEquivM.refl CostedPolyTimeModel (CSP.boolCSPDecisionProblem Γ)

/-- Checklist for proving a non-definitional `SAT(S)` adapter in a future transport layer. -/
structure SATSAdapterObligations (Γ : CSP.BoolLanguage) where
  sourceSyntax : String
  targetSyntax : String
  mapSymbol : String
  inverseMapSymbol : String
  assignmentSemanticsTheorem : String
  encodingPreservationTheorem : String
  notes : String
  deriving Repr

/-- Current local adapter obligations are discharged by definitional equality. -/
def localSATSAdapterObligations (Γ : CSP.BoolLanguage) : SATSAdapterObligations Γ :=
  { sourceSyntax := "ComplexityReduction.Schaefer.SATFormula Γ"
    targetSyntax := "ComplexityReduction.CSP.Formula Γ"
    mapSymbol := "id"
    inverseMapSymbol := "id"
    assignmentSemanticsTheorem :=
      "ComplexityReduction.Schaefer.satSDecisionProblem_isYes_iff"
    encodingPreservationTheorem :=
      "ComplexityReduction.Schaefer.satS_problem_equiv_boolCSP"
    notes :=
      "The first local SAT(S) view reuses CSP.Formula and boolCSPDecisionProblem exactly." }

end Schaefer
end ComplexityReduction
