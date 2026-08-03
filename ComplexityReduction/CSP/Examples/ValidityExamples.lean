/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.To3SATCosted
import ComplexityReduction.CSP.StandardRelations

/-!
Simple 0-valid and 1-valid Boolean CSP languages.

These are intentionally small tractable-side examples for the catalog.  The
project still exposes the uniform upper-bound reduction to 3SAT, but the
formulas in these languages are also witnessed satisfiable by a constant
assignment.
-/

namespace ComplexityReduction
namespace CSP
namespace Examples

open SAT

/-! ## 1-valid positive ternary clauses -/

/-- Singleton relation symbol for positive ternary clauses. -/
inductive Positive3ClauseSymbol where
  | rel
  deriving DecidableEq, Repr

instance : Fintype Positive3ClauseSymbol where
  elems := { val := [Positive3ClauseSymbol.rel], nodup := by simp }
  complete := by
    intro s
    cases s
    simp

/-- The positive ternary clause relation. -/
noncomputable def positive3ClauseRel : BoolRel :=
  StandardRelations.ternaryClauseRel false false false

@[simp]
theorem positive3ClauseRel_arity :
    positive3ClauseRel.arity = 3 :=
  rfl

/-- The fixed positive ternary-clause CSP language. -/
noncomputable def positive3ClauseLanguage : BoolLanguage where
  Symbol := Positive3ClauseSymbol
  finiteSymbol := inferInstance
  relationOf := fun _ => positive3ClauseRel

@[simp]
theorem positive3ClauseLanguage_relation_arity (s : positive3ClauseLanguage.Symbol) :
    (positive3ClauseLanguage.relationOf s).arity = 3 := by
  cases s
  rfl

/-- Positive ternary clauses form a 3-bounded language. -/
theorem positive3ClauseLanguage_isThreeBounded :
    positive3ClauseLanguage.IsThreeBounded := by
  intro s
  rw [positive3ClauseLanguage_relation_arity s]

/-- The encoded decision problem for the positive ternary-clause CSP language. -/
noncomputable def positive3ClauseDecisionProblem : EncodedDecisionProblem :=
  boolCSPDecisionProblem positive3ClauseLanguage

/-- The generic Boolean-CSP-to-3SAT semantic reduction specialized to positive clauses. -/
noncomputable def positive3ClauseToThreeSATReduction :
    SemanticReduction positive3ClauseDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATReduction positive3ClauseLanguage_isThreeBounded

/-- The same specialization with the project-local costed certificate. -/
noncomputable def positive3ClauseToThreeSATCostedReduction :
    CostedReduction positive3ClauseDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATCostedReduction positive3ClauseLanguage_isThreeBounded

/-- The corresponding Karp reduction in the costed polynomial-time model. -/
noncomputable def positive3ClauseToThreeSATKarpReduction :
    KarpReductionM CostedPolyTimeModel positive3ClauseDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATKarpReduction positive3ClauseLanguage_isThreeBounded

/-- Every positive-clause formula is satisfied by the all-true assignment. -/
theorem positive3ClauseFormula_satisfiable (φ : Formula positive3ClauseLanguage) :
    Formula.Satisfiable φ := by
  refine ⟨fun _ => true, ?_⟩
  intro c hc
  cases c.symbol
  change positive3ClauseRel.Holds (fun i => true)
  rw [positive3ClauseRel, StandardRelations.ternaryClauseRel, StandardRelations.clauseRel,
    BoolRel.holds_ofPredicate_iff]
  exact ⟨⟨0, by decide⟩, rfl⟩

/-! ## 0-valid negative ternary clauses -/

/-- Singleton relation symbol for negative ternary clauses. -/
inductive Negative3ClauseSymbol where
  | rel
  deriving DecidableEq, Repr

instance : Fintype Negative3ClauseSymbol where
  elems := { val := [Negative3ClauseSymbol.rel], nodup := by simp }
  complete := by
    intro s
    cases s
    simp

/-- The negative ternary clause relation. -/
noncomputable def negative3ClauseRel : BoolRel :=
  StandardRelations.ternaryClauseRel true true true

@[simp]
theorem negative3ClauseRel_arity :
    negative3ClauseRel.arity = 3 :=
  rfl

/-- The fixed negative ternary-clause CSP language. -/
noncomputable def negative3ClauseLanguage : BoolLanguage where
  Symbol := Negative3ClauseSymbol
  finiteSymbol := inferInstance
  relationOf := fun _ => negative3ClauseRel

@[simp]
theorem negative3ClauseLanguage_relation_arity (s : negative3ClauseLanguage.Symbol) :
    (negative3ClauseLanguage.relationOf s).arity = 3 := by
  cases s
  rfl

/-- Negative ternary clauses form a 3-bounded language. -/
theorem negative3ClauseLanguage_isThreeBounded :
    negative3ClauseLanguage.IsThreeBounded := by
  intro s
  rw [negative3ClauseLanguage_relation_arity s]

/-- The encoded decision problem for the negative ternary-clause CSP language. -/
noncomputable def negative3ClauseDecisionProblem : EncodedDecisionProblem :=
  boolCSPDecisionProblem negative3ClauseLanguage

/-- The generic Boolean-CSP-to-3SAT semantic reduction specialized to negative clauses. -/
noncomputable def negative3ClauseToThreeSATReduction :
    SemanticReduction negative3ClauseDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATReduction negative3ClauseLanguage_isThreeBounded

/-- The same specialization with the project-local costed certificate. -/
noncomputable def negative3ClauseToThreeSATCostedReduction :
    CostedReduction negative3ClauseDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATCostedReduction negative3ClauseLanguage_isThreeBounded

/-- The corresponding Karp reduction in the costed polynomial-time model. -/
noncomputable def negative3ClauseToThreeSATKarpReduction :
    KarpReductionM CostedPolyTimeModel negative3ClauseDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATKarpReduction negative3ClauseLanguage_isThreeBounded

/-- Every negative-clause formula is satisfied by the all-false assignment. -/
theorem negative3ClauseFormula_satisfiable (φ : Formula negative3ClauseLanguage) :
    Formula.Satisfiable φ := by
  refine ⟨fun _ => false, ?_⟩
  intro c hc
  cases c.symbol
  change negative3ClauseRel.Holds (fun i => false)
  rw [negative3ClauseRel, StandardRelations.ternaryClauseRel, StandardRelations.clauseRel,
    BoolRel.holds_ofPredicate_iff]
  exact ⟨⟨0, by decide⟩, rfl⟩

end Examples
end CSP
end ComplexityReduction
