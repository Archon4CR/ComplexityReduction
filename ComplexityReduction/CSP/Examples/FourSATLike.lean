/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.To3SAT
import ComplexityReduction.CSP.To3SATCosted
import ComplexityReduction.SAT.CNFTo3SATCosted
import ComplexityReduction.CSP.StandardRelations

/-!
A fixed arity-4 Boolean CSP language.

This example exercises the unrestricted-arity semantic bridge.  The costed
route is inherited from the generic fixed-finite-language theorem.
-/

namespace ComplexityReduction
namespace CSP
namespace Examples

open SAT

/-- Singleton relation symbol for positive 4-clause SAT. -/
inductive FourClauseSymbol where
  | rel
  deriving DecidableEq, Repr

instance : Fintype FourClauseSymbol where
  elems := { val := [FourClauseSymbol.rel], nodup := by simp }
  complete := by
    intro s
    cases s
    simp

/-- The positive 4-literal clause relation. -/
noncomputable def positiveFourClauseRel : BoolRel :=
  StandardRelations.clauseRel 4 fun _ => false

@[simp]
theorem positiveFourClauseRel_arity :
    positiveFourClauseRel.arity = 4 :=
  rfl

/-- A fixed finite Boolean CSP language whose only relation has arity four. -/
noncomputable def fourClauseLanguage : BoolLanguage where
  Symbol := FourClauseSymbol
  finiteSymbol := inferInstance
  relationOf := fun _ => positiveFourClauseRel

@[simp]
theorem fourClauseLanguage_relation_arity (s : fourClauseLanguage.Symbol) :
    (fourClauseLanguage.relationOf s).arity = 4 := by
  cases s
  rfl

theorem fourClauseLanguage_notThreeBounded :
    ¬ fourClauseLanguage.IsThreeBounded := by
  intro h
  have hrel := h FourClauseSymbol.rel
  simp [fourClauseLanguage] at hrel

/-- The encoded decision problem for the fixed positive 4-clause CSP language. -/
noncomputable def fourClauseDecisionProblem : EncodedDecisionProblem :=
  boolCSPDecisionProblem fourClauseLanguage

/-- The unrestricted-arity semantic reduction specialized to positive 4-clause SAT. -/
noncomputable def fourClauseToThreeSATGeneralReduction :
    SemanticReduction fourClauseDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATGeneralReduction fourClauseLanguage

theorem fourClauseFormula_toThreeCNFGeneral_encodedLength_le
    (φ : Formula fourClauseLanguage) :
    (ThreeSATEncoding.encodeThreeCNF (Formula.toThreeCNFGeneral φ)).length ≤
      (20 * (1 + fourClauseLanguage.maxFalsifyingTuples * fourClauseLanguage.maxArity +
          fourClauseLanguage.maxFalsifyingTuples) ^ 2 * 4) *
        (Encoding.encodeFormula φ).length ^ 2 +
      (20 * (1 + fourClauseLanguage.maxFalsifyingTuples * fourClauseLanguage.maxArity +
          fourClauseLanguage.maxFalsifyingTuples) ^ 2) :=
  Formula.toThreeCNFGeneral_encodedLength_le φ

theorem fourClauseToThreeSATGeneral_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : Formula fourClauseLanguage => fourClauseDecisionProblem.Instance.inputSize φ)
      (fun ψ : ThreeCNF => threeSATDecisionProblem.Instance.inputSize ψ)
      (fun φ => Formula.toThreeCNFGeneral φ) :=
  Formula.toThreeCNFGeneral_polynomialSizeBound fourClauseLanguage

/-- The arity-four example with a project-local costed certificate. -/
noncomputable def fourClauseToThreeSATGeneralCostedReduction :
    CostedReduction fourClauseDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATGeneralCostedReduction fourClauseLanguage

/-- Karp reduction for the arity-four example in the project-local costed model. -/
noncomputable def fourClauseToThreeSATGeneralKarpReduction :
    KarpReductionM CostedPolyTimeModel fourClauseDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATGeneralKarpReduction fourClauseLanguage

/-- A sample positive 4-clause constraint. -/
noncomputable def fourClauseSampleConstraint : Constraint fourClauseLanguage where
  symbol := FourClauseSymbol.rel
  vars := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 2
    | ⟨3, _⟩ => 3

/-- A sample formula with one arity-4 relation application. -/
noncomputable def fourClauseSampleFormula : Formula fourClauseLanguage :=
  [fourClauseSampleConstraint]

/-- The real CSP encoding assigns a nonzero length to the arity-4 sample formula. -/
theorem fourClauseSampleFormula_inputSize_pos :
    0 < (boolCSPDecisionProblem fourClauseLanguage).Instance.inputSize fourClauseSampleFormula := by
  change 0 < (Encoding.encodeFormula (Γ := fourClauseLanguage) fourClauseSampleFormula).length
  simp [Encoding.encodeFormula, Encoding.encodeConstraint, fourClauseSampleFormula,
    fourClauseSampleConstraint]

end Examples
end CSP
end ComplexityReduction
