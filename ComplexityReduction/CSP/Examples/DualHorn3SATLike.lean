/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.To3SATCosted
import ComplexityReduction.CSP.StandardRelations

/-!
A fixed finite Boolean CSP language for ternary dual-Horn clauses.

The four symbols are ternary clauses with at most one negative literal.  This
complements `Horn3SATLike` in the Schaefer-facing regression library.
-/

namespace ComplexityReduction
namespace CSP
namespace Examples

open SAT

/-- Relation symbols for ternary dual-Horn clauses, with at most one negative literal. -/
inductive DualHorn3Symbol where
  | posPosPos
  | negPosPos
  | posNegPos
  | posPosNeg
  deriving DecidableEq, Repr

instance : Fintype DualHorn3Symbol where
  elems :=
    { val :=
        [ DualHorn3Symbol.posPosPos
        , DualHorn3Symbol.negPosPos
        , DualHorn3Symbol.posNegPos
        , DualHorn3Symbol.posPosNeg
        ]
      nodup := by simp }
  complete := by
    intro s
    cases s <;> simp

/-- The Boolean relation attached to a dual-Horn-clause symbol. -/
noncomputable def dualHorn3RelationOf : DualHorn3Symbol → BoolRel
  | DualHorn3Symbol.posPosPos => StandardRelations.ternaryClauseRel false false false
  | DualHorn3Symbol.negPosPos => StandardRelations.ternaryClauseRel true false false
  | DualHorn3Symbol.posNegPos => StandardRelations.ternaryClauseRel false true false
  | DualHorn3Symbol.posPosNeg => StandardRelations.ternaryClauseRel false false true

@[simp]
theorem dualHorn3RelationOf_arity (s : DualHorn3Symbol) :
    (dualHorn3RelationOf s).arity = 3 := by
  cases s <;> simp [dualHorn3RelationOf]

/-- The fixed ternary dual-Horn-clause CSP language. -/
noncomputable def dualHorn3Language : BoolLanguage where
  Symbol := DualHorn3Symbol
  finiteSymbol := inferInstance
  relationOf := dualHorn3RelationOf

@[simp]
theorem dualHorn3Language_relation_arity (s : dualHorn3Language.Symbol) :
    (dualHorn3Language.relationOf s).arity = 3 := by
  cases s <;> simp [dualHorn3Language, dualHorn3RelationOf]

/-- The ternary dual-Horn CSP language is 3-bounded. -/
theorem dualHorn3Language_isThreeBounded :
    dualHorn3Language.IsThreeBounded := by
  intro s
  rw [dualHorn3Language_relation_arity s]

/-- The encoded decision problem for the fixed ternary dual-Horn-clause CSP language. -/
noncomputable def dualHorn3DecisionProblem : EncodedDecisionProblem :=
  boolCSPDecisionProblem dualHorn3Language

/-- The generic Boolean-CSP-to-3SAT semantic reduction specialized to dual-Horn clauses. -/
noncomputable def dualHorn3ToThreeSATReduction :
    SemanticReduction dualHorn3DecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATReduction dualHorn3Language_isThreeBounded

/-- The same specialization with the project-local costed certificate. -/
noncomputable def dualHorn3ToThreeSATCostedReduction :
    CostedReduction dualHorn3DecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATCostedReduction dualHorn3Language_isThreeBounded

/-- The corresponding Karp reduction in the costed polynomial-time model. -/
noncomputable def dualHorn3ToThreeSATKarpReduction :
    KarpReductionM CostedPolyTimeModel dualHorn3DecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATKarpReduction dualHorn3Language_isThreeBounded

/-- A positive dual-Horn clause over variables `0`, `1`, and `2`. -/
noncomputable def positiveDualHorn3Constraint : Constraint dualHorn3Language where
  symbol := DualHorn3Symbol.posPosPos
  vars := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 2

/-- A dual-Horn clause with one negative literal and a repeated variable. -/
noncomputable def mixedDualHorn3Constraint : Constraint dualHorn3Language where
  symbol := DualHorn3Symbol.negPosPos
  vars := fun
    | ⟨0, _⟩ => 2
    | ⟨1, _⟩ => 3
    | ⟨2, _⟩ => 2

/-- A small dual-Horn CSP formula over the fixed ternary dual-Horn language. -/
noncomputable def dualHorn3SampleFormula : Formula dualHorn3Language :=
  [positiveDualHorn3Constraint, mixedDualHorn3Constraint]

/-- The real CSP encoding assigns a nonzero length to the dual-Horn sample formula. -/
theorem dualHorn3SampleFormula_inputSize_pos :
    0 < (boolCSPDecisionProblem dualHorn3Language).Instance.inputSize
      dualHorn3SampleFormula := by
  change 0 < (Encoding.encodeFormula (Γ := dualHorn3Language)
    dualHorn3SampleFormula).length
  simp [Encoding.encodeFormula, Encoding.encodeConstraint, dualHorn3SampleFormula,
    positiveDualHorn3Constraint, mixedDualHorn3Constraint]

end Examples
end CSP
end ComplexityReduction
