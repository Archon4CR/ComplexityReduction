/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.To3SATCosted

/-!
Concrete Boolean CSP examples.

This file gives a first non-toy fixed Boolean CSP language: one-in-three SAT.
It is intentionally small, but it exercises the real CSP syntax, language
adapter, duplicate-variable constraints, and the arity-3 CSP-to-3SAT bridge.
-/

namespace ComplexityReduction
namespace CSP
namespace Examples

open SAT

/-- Number of true coordinates in a 3-tuple. -/
def trueCount3 (t : BoolTuple 3) : Nat :=
  (if t ⟨0, by decide⟩ then 1 else 0) +
    (if t ⟨1, by decide⟩ then 1 else 0) +
      (if t ⟨2, by decide⟩ then 1 else 0)

/-- The ternary relation accepting exactly the tuples with one true coordinate. -/
noncomputable def oneInThreeRel : BoolRel where
  arity := 3
  accepts := Finset.univ.filter fun t : BoolTuple 3 => trueCount3 t = 1

@[simp]
theorem oneInThreeRel_arity : oneInThreeRel.arity = 3 :=
  rfl

/-- The singleton relation-symbol type for one-in-three SAT. -/
inductive OneInThreeSymbol where
  | rel
  deriving DecidableEq, Repr

instance : Fintype OneInThreeSymbol where
  elems := { val := [OneInThreeSymbol.rel], nodup := by simp }
  complete := by
    intro s
    cases s
    simp

/-- The fixed one-in-three CSP language. -/
noncomputable def oneInThreeLanguage : BoolLanguage where
  Symbol := OneInThreeSymbol
  finiteSymbol := inferInstance
  relationOf := fun _ => oneInThreeRel

@[simp]
theorem oneInThreeLanguage_relation_arity (s : oneInThreeLanguage.Symbol) :
    (oneInThreeLanguage.relationOf s).arity = 3 := by
  cases s
  rfl

/-- One-in-three SAT is a 3-bounded Boolean CSP language. -/
theorem oneInThreeLanguage_isThreeBounded :
    oneInThreeLanguage.IsThreeBounded := by
  intro s
  cases s
  exact Nat.le_refl 3

/-- The encoded decision problem for one-in-three SAT. -/
noncomputable def oneInThreeDecisionProblem : EncodedDecisionProblem :=
  boolCSPDecisionProblem oneInThreeLanguage

/-- The generic arity-3 CSP-to-3SAT semantic reduction specialized to one-in-three SAT. -/
noncomputable def oneInThreeToThreeSATReduction :
    SemanticReduction oneInThreeDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATReduction oneInThreeLanguage_isThreeBounded

/-- The same specialization with the project-local costed certificate. -/
noncomputable def oneInThreeToThreeSATCostedReduction :
    CostedReduction oneInThreeDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATCostedReduction oneInThreeLanguage_isThreeBounded

/-- The corresponding Karp reduction in the costed polynomial-time model. -/
noncomputable def oneInThreeToThreeSATKarpReduction :
    KarpReductionM CostedPolyTimeModel oneInThreeDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATKarpReduction oneInThreeLanguage_isThreeBounded

/-- A sample one-in-three constraint using the same variable in two positions. -/
noncomputable def duplicateVariableConstraint : Constraint oneInThreeLanguage where
  symbol := OneInThreeSymbol.rel
  vars := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => 1

/-- A one-constraint formula containing a duplicate-variable relation application. -/
noncomputable def duplicateVariableFormula : Formula oneInThreeLanguage :=
  [duplicateVariableConstraint]

/-- The real CSP encoding assigns a nonzero length to the sample formula. -/
theorem duplicateVariableFormula_inputSize_pos :
    0 < (boolCSPDecisionProblem oneInThreeLanguage).Instance.inputSize duplicateVariableFormula := by
  change 0 < (Encoding.encodeFormula (Γ := oneInThreeLanguage) duplicateVariableFormula).length
  simp [Encoding.encodeFormula, Encoding.encodeConstraint, duplicateVariableFormula,
    duplicateVariableConstraint]

end Examples
end CSP
end ComplexityReduction
