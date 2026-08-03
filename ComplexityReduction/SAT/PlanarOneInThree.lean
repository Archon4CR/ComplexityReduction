/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.CSP.FiniteDomain.BoolBridge
import ComplexityReduction.CSP.StandardRelations
import ComplexityReduction.Combinatorics.Graph.BoundedDegree

/-!
Monotone planar one-in-three SAT descriptors and finite-domain CSP bridge.

This module gives the reduction agent a conservative intermediate target for
Moore-Robson/Lichtenstein style routes.  Clauses are positive ternary
one-in-three clauses over natural-number variables.  The word "planar" is kept
as finite incidence-graph metadata; no Lichtenstein planar-SAT theorem or
global hardness theorem is asserted here.
-/

namespace ComplexityReduction
namespace SAT
namespace PlanarOneInThree

/-- Variables are natural-number indices. -/
abbrev Variable : Type :=
  Nat

/-- A positive ternary one-in-three clause. -/
structure Clause where
  first : Variable
  second : Variable
  third : Variable
  deriving DecidableEq, Repr

namespace Clause

/-- Variable at one of the three clause positions. -/
def var (C : Clause) : Fin 3 → Variable
  | ⟨0, _⟩ => C.first
  | ⟨1, _⟩ => C.second
  | ⟨_, _⟩ => C.third

@[simp]
theorem var_zero (C : Clause) :
    C.var (0 : Fin 3) = C.first :=
  rfl

@[simp]
theorem var_one (C : Clause) :
    C.var (1 : Fin 3) = C.second :=
  rfl

@[simp]
theorem var_two (C : Clause) :
    C.var (2 : Fin 3) = C.third :=
  rfl

/-- Clause variables as a finite list. -/
def varsList (C : Clause) : List Variable :=
  [C.first, C.second, C.third]

@[simp]
theorem varsList_length (C : Clause) :
    C.varsList.length = 3 :=
  rfl

@[simp]
theorem mem_varsList_iff (C : Clause) (v : Variable) :
    v ∈ C.varsList ↔ v = C.first ∨ v = C.second ∨ v = C.third := by
  simp [varsList]

/-- Tuple read by this clause under an assignment. -/
def tuple (C : Clause) (a : Variable → Bool) : CSP.BoolTuple 3 :=
  fun i => a (C.var i)

/-- Clause-level exactly-one satisfaction. -/
def Satisfied (C : Clause) (a : Variable → Bool) : Prop :=
  CSP.StandardRelations.exactlyOne3Rel.Holds (C.tuple a)

end Clause

/-- One relation symbol for positive exactly-one ternary clauses. -/
inductive OneInThreeSymbol where
  | rel
  deriving DecidableEq, Fintype, Repr

/-- Boolean CSP language for monotone exactly-one 3SAT clauses. -/
noncomputable def boolLanguage : CSP.BoolLanguage where
  Symbol := OneInThreeSymbol
  finiteSymbol := inferInstance
  relationOf := fun _ => CSP.StandardRelations.exactlyOne3Rel

@[simp]
theorem boolLanguage_relation_arity (s : boolLanguage.Symbol) :
    (boolLanguage.relationOf s).arity = 3 := by
  cases s
  rfl

/-- Finite-domain `Bool` language for monotone exactly-one 3SAT clauses. -/
noncomputable def finiteDomainLanguage : CSP.FiniteDomain.Language Bool :=
  CSP.FiniteDomain.BoolBridge.languageOfBoolLanguage boolLanguage

/-- Convert one positive one-in-three clause to the Boolean CSP surface. -/
noncomputable def Clause.toBoolConstraint (C : Clause) :
    CSP.Constraint boolLanguage where
  symbol := OneInThreeSymbol.rel
  vars := C.var

/-- Convert one positive one-in-three clause to the finite-domain CSP surface. -/
noncomputable def Clause.toFiniteDomainConstraint (C : Clause) :
    CSP.FiniteDomain.Constraint finiteDomainLanguage :=
  CSP.FiniteDomain.BoolBridge.constraintOfBoolConstraint C.toBoolConstraint

@[simp]
theorem Clause.toBoolConstraint_satisfies_iff (C : Clause) (a : Variable → Bool) :
    CSP.Constraint.Satisfies C.toBoolConstraint a ↔ C.Satisfied a :=
  Iff.rfl

@[simp]
theorem Clause.toFiniteDomainConstraint_satisfies_iff
    (C : Clause) (a : CSP.FiniteDomain.Assignment Bool) :
    CSP.FiniteDomain.Constraint.Satisfies C.toFiniteDomainConstraint a ↔ C.Satisfied a :=
  Iff.rfl

private theorem sum_map_const_three {α : Type} (xs : List α) :
    (xs.map fun _ => 3).sum = xs.length * 3 := by
  induction xs with
  | nil =>
      simp
  | cons _ xs ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]
      omega

/-- Finite monotone one-in-three formula with an explicit variable bound. -/
structure Formula where
  variableCount : Nat
  clauses : List Clause
  deriving Repr

namespace Formula

/-- Assignment-level satisfaction of all clauses. -/
def Satisfied (F : Formula) (a : Variable → Bool) : Prop :=
  ∀ C ∈ F.clauses, C.Satisfied a

/-- Existential satisfiability of the finite formula. -/
def Satisfiable (F : Formula) : Prop :=
  ∃ a : Variable → Bool, F.Satisfied a

/-- The formula is syntactically monotone because clauses contain no negated literals. -/
def IsMonotone (_F : Formula) : Prop :=
  True

@[simp]
theorem isMonotone (F : Formula) :
    F.IsMonotone :=
  trivial

/-- Every listed variable is below the declared variable bound. -/
def VarsWithinBounds (F : Formula) : Prop :=
  ∀ C ∈ F.clauses, ∀ v ∈ C.varsList, v < F.variableCount

/-- Number of occurrences of a variable in the ternary clause list. -/
def variableOccurrences (F : Formula) (v : Variable) : Nat :=
  (F.clauses.map fun C => (C.varsList.filter fun u => u = v).length).sum

/-- Cubic incidence metadata: every declared variable has exactly three occurrences. -/
def IsCubicIncidence (F : Formula) : Prop :=
  ∀ v, v < F.variableCount → F.variableOccurrences v = 3

/-- Boolean CSP formula for the monotone one-in-three formula. -/
noncomputable def toBoolFormula (F : Formula) :
    CSP.Formula boolLanguage :=
  F.clauses.map Clause.toBoolConstraint

/-- Finite-domain CSP formula for the monotone one-in-three formula. -/
noncomputable def toFiniteDomainFormula (F : Formula) :
    CSP.FiniteDomain.Formula finiteDomainLanguage :=
  CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula F.toBoolFormula

/-- One generated Boolean CSP constraint per source clause. -/
@[simp]
theorem toBoolFormula_length (F : Formula) :
    F.toBoolFormula.length = F.clauses.length := by
  simp [toBoolFormula]

/-- One generated finite-domain CSP constraint per source clause. -/
@[simp]
theorem toFiniteDomainFormula_length (F : Formula) :
    F.toFiniteDomainFormula.length = F.clauses.length := by
  calc
    F.toFiniteDomainFormula.length = F.toBoolFormula.length := by
      rw [toFiniteDomainFormula, CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula]
      exact F.toBoolFormula.length_map CSP.FiniteDomain.BoolBridge.constraintOfBoolConstraint
    _ = F.clauses.length := toBoolFormula_length F

/-- Boolean CSP formula satisfaction is exactly clause-level one-in-three satisfaction. -/
theorem toBoolFormula_satisfies_iff (F : Formula) (a : Variable → Bool) :
    CSP.Formula.Satisfies F.toBoolFormula a ↔ F.Satisfied a := by
  constructor
  · intro h C hC
    have hMem : C.toBoolConstraint ∈ F.toBoolFormula :=
      List.mem_map.mpr ⟨C, hC, rfl⟩
    exact (Clause.toBoolConstraint_satisfies_iff C a).1 (h C.toBoolConstraint hMem)
  · intro h c hc
    rcases List.mem_map.mp (by simpa [toBoolFormula] using hc) with ⟨C, hC, rfl⟩
    exact (Clause.toBoolConstraint_satisfies_iff C a).2 (h C hC)

/-- Finite-domain CSP formula satisfaction is exactly source formula satisfaction. -/
theorem toFiniteDomainFormula_satisfies_iff (F : Formula)
    (a : CSP.FiniteDomain.Assignment Bool) :
    CSP.FiniteDomain.Formula.Satisfies F.toFiniteDomainFormula a ↔ F.Satisfied a := by
  change
    CSP.FiniteDomain.Formula.Satisfies
        (CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula F.toBoolFormula) a ↔
      F.Satisfied a
  exact
    (CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula_satisfies_iff F.toBoolFormula a).trans
      (toBoolFormula_satisfies_iff F a)

/-- Finite-domain CSP satisfiability is exactly source formula satisfiability. -/
theorem toFiniteDomainFormula_satisfiable_iff (F : Formula) :
    CSP.FiniteDomain.Formula.Satisfiable F.toFiniteDomainFormula ↔ F.Satisfiable := by
  constructor
  · rintro ⟨a, hSat⟩
    exact ⟨a, (toFiniteDomainFormula_satisfies_iff F a).1 hSat⟩
  · rintro ⟨a, hSat⟩
    exact ⟨a, (toFiniteDomainFormula_satisfies_iff F a).2 hSat⟩

/-- Graph vertex assigned to one clause index in the incidence graph. -/
def clauseVertex (F : Formula) (i : Fin F.clauses.length) : Nat :=
  F.variableCount + i.val

/-- Clause-index list used to generate incidence edges. -/
def clauseIndices (F : Formula) : List (Fin F.clauses.length) :=
  List.ofFn fun i => i

@[simp]
theorem clauseIndices_length (F : Formula) :
    F.clauseIndices.length = F.clauses.length := by
  simp [clauseIndices]

/-- Incidence edges from variable vertices to clause vertices, with multiplicity. -/
def incidenceEdges (F : Formula) : List (Nat × Nat) :=
  F.clauseIndices.flatMap fun i =>
    (F.clauses.get i).varsList.map fun v => (v, F.clauseVertex i)

/-- Raw incidence graph for the formula. -/
def incidenceGraph (F : Formula) : Combinatorics.Graph.GraphInput where
  vertices := F.variableCount + F.clauses.length
  edges := F.incidenceEdges
  directed := false

@[simp]
theorem incidenceGraph_vertices (F : Formula) :
    F.incidenceGraph.vertices = F.variableCount + F.clauses.length :=
  rfl

@[simp]
theorem incidenceGraph_edges (F : Formula) :
    F.incidenceGraph.edges = F.incidenceEdges :=
  rfl

/-- Incidence graph has three listed edges per source clause. -/
theorem incidenceEdges_length (F : Formula) :
    F.incidenceEdges.length = F.clauses.length * 3 := by
  calc
    F.incidenceEdges.length = (F.clauseIndices.map fun _ => 3).sum := by
      simp [incidenceEdges, Clause.varsList]
    _ = F.clauseIndices.length * 3 := sum_map_const_three F.clauseIndices
    _ = F.clauses.length * 3 := by simp [clauseIndices]

/-- Clause vertices lie inside the incidence graph's vertex range. -/
theorem clauseVertex_lt_incidenceGraph_vertices (F : Formula)
    (i : Fin F.clauses.length) :
    F.clauseVertex i < F.incidenceGraph.vertices := by
  exact Nat.add_lt_add_left i.isLt F.variableCount

/-- Variable vertices that respect the declared bound lie inside the incidence graph. -/
theorem variable_lt_incidenceGraph_vertices (F : Formula) {v : Variable}
    (hv : v < F.variableCount) :
    v < F.incidenceGraph.vertices := by
  exact lt_of_lt_of_le hv (Nat.le_add_right F.variableCount F.clauses.length)

/--
If all clause variables respect the declared variable bound, the generated
incidence graph has all listed endpoints inside its vertex range.
-/
theorem incidenceGraph_wellFormed_of_varsWithinBounds {F : Formula}
    (hF : F.VarsWithinBounds) :
    Combinatorics.Graph.WellFormed F.incidenceGraph := by
  intro e he
  change e ∈ F.incidenceEdges at he
  rw [incidenceEdges] at he
  rcases List.mem_flatMap.mp he with ⟨i, hi, heInClause⟩
  rcases List.mem_map.mp heInClause with ⟨v, hv, rfl⟩
  have hi' : i ∈ List.ofFn (fun j : Fin F.clauses.length => j) := hi
  rcases List.mem_ofFn.mp hi' with ⟨j, rfl⟩
  exact
    ⟨variable_lt_incidenceGraph_vertices F
        (hF (F.clauses.get j) (List.get_mem F.clauses j) v hv),
      clauseVertex_lt_incidenceGraph_vertices F j⟩

end Formula

end PlanarOneInThree
end SAT
end ComplexityReduction
