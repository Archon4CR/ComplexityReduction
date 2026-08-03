/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Templates

namespace ComplexityReduction

namespace Domains

namespace SAT

/-- Literals for the toy SAT benchmark. -/
structure Literal where
  var : Nat
  neg : Bool
  deriving DecidableEq, Repr

/-- Toy clauses are lists of literals. -/
abbrev Clause : Type :=
  List Literal

/-- Toy CNF formulas are lists of clauses. -/
abbrev CNF : Type :=
  List Clause

/-- Encode literals by variable unary code plus a sign marker. -/
def LiteralEnc : EncodedType where
  Carrier := Literal
  Symbol := Bool
  finite_symbol := inferInstance
  encode := fun l => [l.neg] ++ List.replicate l.var true ++ [false]

/-- Encoded toy CNF formulas. -/
def CNFEnc : EncodedType :=
  EncodedType.list (EncodedType.list LiteralEnc)

/-- A deliberately small syntactic property used as a toy target. -/
def hasEmptyClause (φ : CNF) : Prop :=
  [] ∈ φ

/-- Same property through a named predicate, for subset-lifting tests. -/
def hasEmptyClauseAlias (φ : CNF) : Prop :=
  hasEmptyClause φ

/-- Toy SAT-style source problem. -/
def EmptyClauseProblem : EncodedDecisionProblem where
  Instance := CNFEnc
  isYes := hasEmptyClause

/-- Toy SAT-style target problem with definitionally equal predicate. -/
def EmptyClauseAliasProblem : EncodedDecisionProblem where
  Instance := CNFEnc
  isYes := hasEmptyClauseAlias

theorem hasEmptyClause_iff_alias (φ : CNF) :
    hasEmptyClause φ ↔ hasEmptyClauseAlias φ :=
  Iff.rfl

/-- Benchmark: subset lifting over a SAT-shaped problem. -/
def emptyClauseSubsetLift :
    LogReductionCert EmptyClauseProblem EmptyClauseAliasProblem := by
  change LogReductionCert
    ({ Instance := CNFEnc, isYes := hasEmptyClause } : EncodedDecisionProblem)
    ({ Instance := CNFEnc, isYes := hasEmptyClauseAlias } : EncodedDecisionProblem)
  exact Templates.logSubsetLift (X := CNFEnc)
    hasEmptyClause hasEmptyClauseAlias hasEmptyClause_iff_alias

/-- A toy block template mapping each literal to a fixed empty block. -/
def literalEmptyBlock : Templates.BlockTemplate LiteralEnc LiteralEnc where
  blockOf := fun _ => []
  block_costed :=
    CostedPolyTimeMap.const_map (X := LiteralEnc) (Y := EncodedType.list LiteralEnc)
      ([] : List Literal)

end SAT

end Domains

end ComplexityReduction
