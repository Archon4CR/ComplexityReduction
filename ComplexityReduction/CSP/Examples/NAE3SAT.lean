/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.To3SATCosted
import ComplexityReduction.CSP.StandardRelations

/-!
The fixed Boolean CSP language for NAE-3SAT.

This is a second non-toy arity-3 regression target for the generic
`SAT(Gamma) <=p 3SAT` bridge.
-/

namespace ComplexityReduction
namespace CSP
namespace Examples

open SAT

/-- The ternary relation accepting exactly the not-all-equal tuples. -/
noncomputable def notAllEqual3Rel : BoolRel :=
  StandardRelations.notAllEqual3Rel

@[simp]
theorem notAllEqual3Rel_arity :
    notAllEqual3Rel.arity = 3 :=
  StandardRelations.notAllEqual3Rel_arity

/-- The singleton relation-symbol type for NAE-3SAT. -/
inductive NAE3Symbol where
  | rel
  deriving DecidableEq, Repr

instance : Fintype NAE3Symbol where
  elems := { val := [NAE3Symbol.rel], nodup := by simp }
  complete := by
    intro s
    cases s
    simp

/-- The fixed NAE-3SAT CSP language. -/
noncomputable def notAllEqual3Language : BoolLanguage where
  Symbol := NAE3Symbol
  finiteSymbol := inferInstance
  relationOf := fun _ => notAllEqual3Rel

@[simp]
theorem notAllEqual3Language_relation_arity (s : notAllEqual3Language.Symbol) :
    (notAllEqual3Language.relationOf s).arity = 3 := by
  cases s
  exact notAllEqual3Rel_arity

/-- NAE-3SAT is a 3-bounded Boolean CSP language. -/
theorem notAllEqual3Language_isThreeBounded :
    notAllEqual3Language.IsThreeBounded := by
  intro s
  cases s
  rw [notAllEqual3Language_relation_arity NAE3Symbol.rel]

/-- The encoded decision problem for NAE-3SAT. -/
noncomputable def notAllEqual3DecisionProblem : EncodedDecisionProblem :=
  boolCSPDecisionProblem notAllEqual3Language

/-- The generic arity-3 CSP-to-3SAT semantic reduction specialized to NAE-3SAT. -/
noncomputable def notAllEqual3ToThreeSATReduction :
    SemanticReduction notAllEqual3DecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATReduction notAllEqual3Language_isThreeBounded

/-- The same specialization with the project-local costed certificate. -/
noncomputable def notAllEqual3ToThreeSATCostedReduction :
    CostedReduction notAllEqual3DecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATCostedReduction notAllEqual3Language_isThreeBounded

/-- The corresponding Karp reduction in the costed polynomial-time model. -/
noncomputable def notAllEqual3ToThreeSATKarpReduction :
    KarpReductionM CostedPolyTimeModel notAllEqual3DecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATKarpReduction notAllEqual3Language_isThreeBounded

/-- A sample NAE constraint with a repeated variable. -/
noncomputable def duplicateVariableNAEConstraint : Constraint notAllEqual3Language where
  symbol := NAE3Symbol.rel
  vars := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => 1

/-- A one-constraint NAE formula exercising the duplicate-variable path. -/
noncomputable def duplicateVariableNAEFormula : Formula notAllEqual3Language :=
  [duplicateVariableNAEConstraint]

/-- The real CSP encoding assigns a nonzero length to the sample formula. -/
theorem duplicateVariableNAEFormula_inputSize_pos :
    0 < (boolCSPDecisionProblem notAllEqual3Language).Instance.inputSize
      duplicateVariableNAEFormula := by
  change 0 < (Encoding.encodeFormula (Γ := notAllEqual3Language)
    duplicateVariableNAEFormula).length
  simp [Encoding.encodeFormula, Encoding.encodeConstraint, duplicateVariableNAEFormula,
    duplicateVariableNAEConstraint]

end Examples
end CSP
end ComplexityReduction
