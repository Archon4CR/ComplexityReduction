/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.To3SATCosted
import ComplexityReduction.CSP.StandardRelations

/-!
A fixed finite Boolean CSP language for ordinary binary 2SAT clauses.

The four symbols represent the four possible polarity patterns of a binary
clause.  The example checks that the generic CSP library handles arity below
three and multi-symbol fixed languages.
-/

namespace ComplexityReduction
namespace CSP
namespace Examples

open SAT

/-- Relation symbols for binary clauses. -/
inductive TwoSATSymbol where
  | posPos
  | negPos
  | posNeg
  | negNeg
  deriving DecidableEq, Repr

instance : Fintype TwoSATSymbol where
  elems :=
    { val := [TwoSATSymbol.posPos, TwoSATSymbol.negPos,
        TwoSATSymbol.posNeg, TwoSATSymbol.negNeg]
      nodup := by simp }
  complete := by
    intro s
    cases s <;> simp

/-- The Boolean relation attached to a 2SAT polarity symbol. -/
noncomputable def twoSATRelationOf : TwoSATSymbol → BoolRel
  | TwoSATSymbol.posPos => StandardRelations.binaryClauseRel false false
  | TwoSATSymbol.negPos => StandardRelations.binaryClauseRel true false
  | TwoSATSymbol.posNeg => StandardRelations.binaryClauseRel false true
  | TwoSATSymbol.negNeg => StandardRelations.binaryClauseRel true true

@[simp]
theorem twoSATRelationOf_arity (s : TwoSATSymbol) :
    (twoSATRelationOf s).arity = 2 := by
  cases s <;> simp [twoSATRelationOf]

/-- The fixed binary-clause CSP language. -/
noncomputable def twoSATLanguage : BoolLanguage where
  Symbol := TwoSATSymbol
  finiteSymbol := inferInstance
  relationOf := twoSATRelationOf

@[simp]
theorem twoSATLanguage_relation_arity (s : twoSATLanguage.Symbol) :
    (twoSATLanguage.relationOf s).arity = 2 := by
  cases s <;> simp [twoSATLanguage, twoSATRelationOf]

/-- The 2SAT-like CSP language is 3-bounded. -/
theorem twoSATLanguage_isThreeBounded :
    twoSATLanguage.IsThreeBounded := by
  intro s
  rw [twoSATLanguage_relation_arity s]
  decide

/-- The encoded decision problem for the fixed binary-clause CSP language. -/
noncomputable def twoSATDecisionProblem : EncodedDecisionProblem :=
  boolCSPDecisionProblem twoSATLanguage

/-- The generic Boolean-CSP-to-3SAT semantic reduction specialized to binary clauses. -/
noncomputable def twoSATToThreeSATReduction :
    SemanticReduction twoSATDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATReduction twoSATLanguage_isThreeBounded

/-- The same specialization with the project-local costed certificate. -/
noncomputable def twoSATToThreeSATCostedReduction :
    CostedReduction twoSATDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATCostedReduction twoSATLanguage_isThreeBounded

/-- The corresponding Karp reduction in the costed polynomial-time model. -/
noncomputable def twoSATToThreeSATKarpReduction :
    KarpReductionM CostedPolyTimeModel twoSATDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATKarpReduction twoSATLanguage_isThreeBounded

/-- A positive binary clause over variables `0` and `1`. -/
noncomputable def positiveBinaryClauseConstraint : Constraint twoSATLanguage where
  symbol := TwoSATSymbol.posPos
  vars := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1

/-- A mixed-polarity binary clause sharing variable `1`. -/
noncomputable def mixedPolarityBinaryClauseConstraint : Constraint twoSATLanguage where
  symbol := TwoSATSymbol.negPos
  vars := fun
    | ⟨0, _⟩ => 1
    | ⟨1, _⟩ => 2

/-- A small two-clause formula over the fixed binary-clause language. -/
noncomputable def twoSATSampleFormula : Formula twoSATLanguage :=
  [positiveBinaryClauseConstraint, mixedPolarityBinaryClauseConstraint]

/-- The real CSP encoding assigns a nonzero length to the sample formula. -/
theorem twoSATSampleFormula_inputSize_pos :
    0 < (boolCSPDecisionProblem twoSATLanguage).Instance.inputSize twoSATSampleFormula := by
  change 0 < (Encoding.encodeFormula (Γ := twoSATLanguage) twoSATSampleFormula).length
  simp [Encoding.encodeFormula, Encoding.encodeConstraint, twoSATSampleFormula,
    positiveBinaryClauseConstraint, mixedPolarityBinaryClauseConstraint]

end Examples
end CSP
end ComplexityReduction
