/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Examples.OneInThree
import ComplexityReduction.CSP.Examples.NAE3SAT
import ComplexityReduction.CSP.To3SATCosted
import ComplexityReduction.CSP.StandardRelations

/-!
A mixed fixed finite Boolean CSP language.

This file packages several relations with different arities into one language.
It is intended as a tool-facing regression case: a generated reduction must
handle multiple symbols, mixed arities, and repeated variables without adding
any injectivity assumption on constraint variable tuples.
-/

namespace ComplexityReduction
namespace CSP
namespace Examples

open SAT

/-- Relation symbols for a small mixed Boolean CSP language. -/
inductive MixedFiniteSymbol where
  | oneInThree
  | notAllEqual3
  | implication
  | pinTrue
  deriving DecidableEq, Repr

instance : Fintype MixedFiniteSymbol where
  elems :=
    { val := [MixedFiniteSymbol.oneInThree, MixedFiniteSymbol.notAllEqual3,
        MixedFiniteSymbol.implication, MixedFiniteSymbol.pinTrue]
      nodup := by simp }
  complete := by
    intro s
    cases s <;> simp

/-- Relation interpretation for the mixed finite language. -/
noncomputable def mixedFiniteRelationOf : MixedFiniteSymbol → BoolRel
  | MixedFiniteSymbol.oneInThree => oneInThreeRel
  | MixedFiniteSymbol.notAllEqual3 => notAllEqual3Rel
  | MixedFiniteSymbol.implication => StandardRelations.implicationRel
  | MixedFiniteSymbol.pinTrue => StandardRelations.pinTrueRel

@[simp]
theorem mixedFiniteRelationOf_oneInThree_arity :
    (mixedFiniteRelationOf MixedFiniteSymbol.oneInThree).arity = 3 :=
  rfl

@[simp]
theorem mixedFiniteRelationOf_notAllEqual3_arity :
    (mixedFiniteRelationOf MixedFiniteSymbol.notAllEqual3).arity = 3 :=
  notAllEqual3Rel_arity

@[simp]
theorem mixedFiniteRelationOf_implication_arity :
    (mixedFiniteRelationOf MixedFiniteSymbol.implication).arity = 2 :=
  StandardRelations.implicationRel_arity

@[simp]
theorem mixedFiniteRelationOf_pinTrue_arity :
    (mixedFiniteRelationOf MixedFiniteSymbol.pinTrue).arity = 1 :=
  StandardRelations.pinTrueRel_arity

/-- The mixed fixed finite Boolean CSP language. -/
noncomputable def mixedFiniteLanguage : BoolLanguage where
  Symbol := MixedFiniteSymbol
  finiteSymbol := inferInstance
  relationOf := mixedFiniteRelationOf

@[simp]
theorem mixedFiniteLanguage_relation_arity_le_three (s : mixedFiniteLanguage.Symbol) :
    (mixedFiniteLanguage.relationOf s).arity ≤ 3 := by
  cases s <;> simp [mixedFiniteLanguage, mixedFiniteRelationOf]

/-- The mixed finite language is 3-bounded. -/
theorem mixedFiniteLanguage_isThreeBounded :
    mixedFiniteLanguage.IsThreeBounded :=
  mixedFiniteLanguage_relation_arity_le_three

/-- The encoded decision problem for the mixed finite Boolean CSP language. -/
noncomputable def mixedFiniteDecisionProblem : EncodedDecisionProblem :=
  boolCSPDecisionProblem mixedFiniteLanguage

/-- The generic Boolean-CSP-to-3SAT semantic reduction specialized to the mixed language. -/
noncomputable def mixedFiniteToThreeSATReduction :
    SemanticReduction mixedFiniteDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATReduction mixedFiniteLanguage_isThreeBounded

/-- The same specialization with the project-local costed certificate. -/
noncomputable def mixedFiniteToThreeSATCostedReduction :
    CostedReduction mixedFiniteDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATCostedReduction mixedFiniteLanguage_isThreeBounded

/-- The corresponding Karp reduction in the costed polynomial-time model. -/
noncomputable def mixedFiniteToThreeSATKarpReduction :
    KarpReductionM CostedPolyTimeModel mixedFiniteDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATKarpReduction mixedFiniteLanguage_isThreeBounded

/-- A one-in-three constraint inside the mixed language. -/
noncomputable def mixedOneInThreeConstraint : Constraint mixedFiniteLanguage where
  symbol := MixedFiniteSymbol.oneInThree
  vars := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 2

/-- A not-all-equal constraint with a repeated variable inside the mixed language. -/
noncomputable def mixedNAEConstraint : Constraint mixedFiniteLanguage where
  symbol := MixedFiniteSymbol.notAllEqual3
  vars := fun
    | ⟨0, _⟩ => 2
    | ⟨1, _⟩ => 2
    | ⟨2, _⟩ => 3

/-- A binary implication constraint inside the mixed language. -/
noncomputable def mixedImplicationConstraint : Constraint mixedFiniteLanguage where
  symbol := MixedFiniteSymbol.implication
  vars := fun
    | ⟨0, _⟩ => 3
    | ⟨1, _⟩ => 4

/-- A unary pinning constraint inside the mixed language. -/
noncomputable def mixedPinTrueConstraint : Constraint mixedFiniteLanguage where
  symbol := MixedFiniteSymbol.pinTrue
  vars := fun
    | ⟨0, _⟩ => 4

/-- A sample formula touching every relation symbol in the mixed language. -/
noncomputable def mixedFiniteSampleFormula : Formula mixedFiniteLanguage :=
  [ mixedOneInThreeConstraint
  , mixedNAEConstraint
  , mixedImplicationConstraint
  , mixedPinTrueConstraint
  ]

/-- The real CSP encoding assigns a nonzero length to the mixed sample formula. -/
theorem mixedFiniteSampleFormula_inputSize_pos :
    0 < (boolCSPDecisionProblem mixedFiniteLanguage).Instance.inputSize
      mixedFiniteSampleFormula := by
  change 0 < (Encoding.encodeFormula (Γ := mixedFiniteLanguage) mixedFiniteSampleFormula).length
  simp [Encoding.encodeFormula, Encoding.encodeConstraint, mixedFiniteSampleFormula,
    mixedOneInThreeConstraint, mixedNAEConstraint, mixedImplicationConstraint,
    mixedPinTrueConstraint]

end Examples
end CSP
end ComplexityReduction
