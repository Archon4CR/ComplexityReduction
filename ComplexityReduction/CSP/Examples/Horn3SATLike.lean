/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.To3SATCosted
import ComplexityReduction.CSP.StandardRelations

/-!
A fixed finite Boolean CSP language for ternary Horn clauses.

This is a tractable Schaefer-side regression case.  The library only proves the
uniform upper-bound reduction `SAT(Gamma) <=p 3SAT`; it does not claim
NP-hardness for this language.
-/

namespace ComplexityReduction
namespace CSP
namespace Examples

open SAT

/-- Relation symbols for ternary Horn clauses, with at most one positive literal. -/
inductive Horn3Symbol where
  | negNegNeg
  | posNegNeg
  | negPosNeg
  | negNegPos
  deriving DecidableEq, Repr

instance : Fintype Horn3Symbol where
  elems :=
    { val :=
        [ Horn3Symbol.negNegNeg
        , Horn3Symbol.posNegNeg
        , Horn3Symbol.negPosNeg
        , Horn3Symbol.negNegPos
        ]
      nodup := by simp }
  complete := by
    intro s
    cases s <;> simp

/-- The Boolean relation attached to a Horn-clause symbol. -/
noncomputable def horn3RelationOf : Horn3Symbol → BoolRel
  | Horn3Symbol.negNegNeg => StandardRelations.ternaryClauseRel true true true
  | Horn3Symbol.posNegNeg => StandardRelations.ternaryClauseRel false true true
  | Horn3Symbol.negPosNeg => StandardRelations.ternaryClauseRel true false true
  | Horn3Symbol.negNegPos => StandardRelations.ternaryClauseRel true true false

@[simp]
theorem horn3RelationOf_arity (s : Horn3Symbol) :
    (horn3RelationOf s).arity = 3 := by
  cases s <;> simp [horn3RelationOf]

/-- The fixed ternary Horn-clause CSP language. -/
noncomputable def horn3Language : BoolLanguage where
  Symbol := Horn3Symbol
  finiteSymbol := inferInstance
  relationOf := horn3RelationOf

@[simp]
theorem horn3Language_relation_arity (s : horn3Language.Symbol) :
    (horn3Language.relationOf s).arity = 3 := by
  cases s <;> simp [horn3Language, horn3RelationOf]

/-- The ternary Horn CSP language is 3-bounded. -/
theorem horn3Language_isThreeBounded :
    horn3Language.IsThreeBounded := by
  intro s
  rw [horn3Language_relation_arity s]

/-- The encoded decision problem for the fixed ternary Horn-clause CSP language. -/
noncomputable def horn3DecisionProblem : EncodedDecisionProblem :=
  boolCSPDecisionProblem horn3Language

/-- The generic Boolean-CSP-to-3SAT semantic reduction specialized to Horn clauses. -/
noncomputable def horn3ToThreeSATReduction :
    SemanticReduction horn3DecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATReduction horn3Language_isThreeBounded

/-- The same specialization with the project-local costed certificate. -/
noncomputable def horn3ToThreeSATCostedReduction :
    CostedReduction horn3DecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATCostedReduction horn3Language_isThreeBounded

/-- The corresponding Karp reduction in the costed polynomial-time model. -/
noncomputable def horn3ToThreeSATKarpReduction :
    KarpReductionM CostedPolyTimeModel horn3DecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATKarpReduction horn3Language_isThreeBounded

/-- A negative Horn clause over variables `0`, `1`, and `2`. -/
noncomputable def negativeHorn3Constraint : Constraint horn3Language where
  symbol := Horn3Symbol.negNegNeg
  vars := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 2

/-- A Horn clause with one positive literal and a repeated variable. -/
noncomputable def mixedHorn3Constraint : Constraint horn3Language where
  symbol := Horn3Symbol.posNegNeg
  vars := fun
    | ⟨0, _⟩ => 2
    | ⟨1, _⟩ => 3
    | ⟨2, _⟩ => 2

/-- A small Horn-CSP formula over the fixed ternary Horn language. -/
noncomputable def horn3SampleFormula : Formula horn3Language :=
  [negativeHorn3Constraint, mixedHorn3Constraint]

/-- The real CSP encoding assigns a nonzero length to the Horn sample formula. -/
theorem horn3SampleFormula_inputSize_pos :
    0 < (boolCSPDecisionProblem horn3Language).Instance.inputSize horn3SampleFormula := by
  change 0 < (Encoding.encodeFormula (Γ := horn3Language) horn3SampleFormula).length
  simp [Encoding.encodeFormula, Encoding.encodeConstraint, horn3SampleFormula,
    negativeHorn3Constraint, mixedHorn3Constraint]

end Examples
end CSP
end ComplexityReduction
