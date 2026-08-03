/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.To3SATCosted
import ComplexityReduction.CSP.StandardRelations

/-!
A fixed finite Boolean CSP language for ternary XOR equations.

This gives the concrete problem library an affine Schaefer-side regression
case.  As with the Horn example, the formalized theorem here is the generic
upper-bound reduction to 3SAT, not an NP-hardness claim.
-/

namespace ComplexityReduction
namespace CSP
namespace Examples

open SAT

/-- Singleton relation symbol for odd ternary parity. -/
inductive XOR3Symbol where
  | odd
  deriving DecidableEq, Repr

instance : Fintype XOR3Symbol where
  elems := { val := [XOR3Symbol.odd], nodup := by simp }
  complete := by
    intro s
    cases s
    simp

/-- The odd ternary parity relation. -/
noncomputable def xor3Rel : BoolRel :=
  StandardRelations.oddParity3Rel

@[simp]
theorem xor3Rel_arity :
    xor3Rel.arity = 3 :=
  StandardRelations.oddParity3Rel_arity

/-- The fixed odd-parity CSP language. -/
noncomputable def xor3Language : BoolLanguage where
  Symbol := XOR3Symbol
  finiteSymbol := inferInstance
  relationOf := fun _ => xor3Rel

@[simp]
theorem xor3Language_relation_arity (s : xor3Language.Symbol) :
    (xor3Language.relationOf s).arity = 3 := by
  cases s
  exact xor3Rel_arity

/-- The odd ternary parity CSP language is 3-bounded. -/
theorem xor3Language_isThreeBounded :
    xor3Language.IsThreeBounded := by
  intro s
  rw [xor3Language_relation_arity s]

/-- The encoded decision problem for the fixed odd-parity CSP language. -/
noncomputable def xor3DecisionProblem : EncodedDecisionProblem :=
  boolCSPDecisionProblem xor3Language

/-- The generic Boolean-CSP-to-3SAT semantic reduction specialized to odd parity. -/
noncomputable def xor3ToThreeSATReduction :
    SemanticReduction xor3DecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATReduction xor3Language_isThreeBounded

/-- The same specialization with the project-local costed certificate. -/
noncomputable def xor3ToThreeSATCostedReduction :
    CostedReduction xor3DecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATCostedReduction xor3Language_isThreeBounded

/-- The corresponding Karp reduction in the costed polynomial-time model. -/
noncomputable def xor3ToThreeSATKarpReduction :
    KarpReductionM CostedPolyTimeModel xor3DecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATKarpReduction xor3Language_isThreeBounded

/-- A ternary XOR constraint over variables `0`, `1`, and `2`. -/
noncomputable def xor3SampleConstraint : Constraint xor3Language where
  symbol := XOR3Symbol.odd
  vars := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 2

/-- A duplicate-variable ternary XOR constraint. -/
noncomputable def xor3DuplicateVariableConstraint : Constraint xor3Language where
  symbol := XOR3Symbol.odd
  vars := fun
    | ⟨0, _⟩ => 2
    | ⟨1, _⟩ => 2
    | ⟨2, _⟩ => 3

/-- A small odd-parity CSP formula. -/
noncomputable def xor3SampleFormula : Formula xor3Language :=
  [xor3SampleConstraint, xor3DuplicateVariableConstraint]

/-- The real CSP encoding assigns a nonzero length to the parity sample formula. -/
theorem xor3SampleFormula_inputSize_pos :
    0 < (boolCSPDecisionProblem xor3Language).Instance.inputSize xor3SampleFormula := by
  change 0 < (Encoding.encodeFormula (Γ := xor3Language) xor3SampleFormula).length
  simp [Encoding.encodeFormula, Encoding.encodeConstraint, xor3SampleFormula,
    xor3SampleConstraint, xor3DuplicateVariableConstraint]

end Examples
end CSP
end ComplexityReduction
