/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.CSP.FiniteDomain.Basic

/-!
Standard finite-domain relation gadgets.

This module provides small fixed-template relations that occur frequently in
finite-domain CSP reductions: equality between two variables and unary pinning
to a supplied domain value.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace StandardGadgets

/-- Scope helper for binary constraints. -/
def binaryScope (x y : Nat) : Fin 2 → Nat :=
  fun i => if i.val = 0 then x else y

@[simp]
theorem binaryScope_zero (x y : Nat) :
    binaryScope x y (0 : Fin 2) = x := by
  simp [binaryScope]

@[simp]
theorem binaryScope_one (x y : Nat) :
    binaryScope x y (1 : Fin 2) = y := by
  simp [binaryScope]

/-- Scope helper for unary constraints. -/
def unaryScope (x : Nat) : Fin 1 → Nat :=
  fun _ => x

@[simp]
theorem unaryScope_zero (x : Nat) :
    unaryScope x (0 : Fin 1) = x :=
  rfl

/-- Binary equality relation over an arbitrary finite domain. -/
def equalityRel (D : Type) : Rel D where
  arity := 2
  holds := fun t => t (0 : Fin 2) = t (1 : Fin 2)

@[simp]
theorem equalityRel_holds_iff {D : Type} (t : Tuple D 2) :
    (equalityRel D).Holds t ↔ t (0 : Fin 2) = t (1 : Fin 2) :=
  Iff.rfl

/-- One-symbol language containing only the binary equality relation. -/
def equalityLanguage (D : Type) [Fintype D] : Language D where
  finiteDomain := inferInstance
  Symbol := Unit
  finiteSymbol := inferInstance
  relationOf := fun _ => equalityRel D

/-- Equality constraint between source variables `x` and `y`. -/
def equalityConstraint {D : Type} [Fintype D] (x y : Nat) :
    Constraint (equalityLanguage D) where
  symbol := ()
  vars := binaryScope x y

/-- Singleton formula enforcing equality between variables `x` and `y`. -/
def equalityFormula {D : Type} [Fintype D] (x y : Nat) :
    Formula (equalityLanguage D) :=
  [equalityConstraint x y]

@[simp]
theorem equalityConstraint_satisfies_iff {D : Type} [Fintype D] (x y : Nat)
    (a : Assignment D) :
    Constraint.Satisfies (equalityConstraint (D := D) x y) a ↔ a x = a y := by
  simp [Constraint.Satisfies, Constraint.assignmentTuple, equalityConstraint,
    equalityLanguage, equalityRel, Rel.Holds]

@[simp]
theorem equalityFormula_satisfies_iff {D : Type} [Fintype D] (x y : Nat)
    (a : Assignment D) :
    Formula.Satisfies (equalityFormula (D := D) x y) a ↔ a x = a y := by
  simp [equalityFormula]

/-- If the domain is inhabited, one equality constraint is satisfiable. -/
theorem equalityFormula_satisfiable {D : Type} [Fintype D] [Inhabited D] (x y : Nat) :
    Formula.Satisfiable (equalityFormula (D := D) x y) := by
  refine ⟨fun _ => default, ?_⟩
  simp

/-- Unary relation pinning a variable to the supplied value. -/
def pinRel {D : Type} (d : D) : Rel D where
  arity := 1
  holds := fun t => t (0 : Fin 1) = d

@[simp]
theorem pinRel_holds_iff {D : Type} (d : D) (t : Tuple D 1) :
    (pinRel d).Holds t ↔ t (0 : Fin 1) = d :=
  Iff.rfl

/-- One-symbol language containing only a unary pinning relation. -/
def pinLanguage {D : Type} [Fintype D] (d : D) : Language D where
  finiteDomain := inferInstance
  Symbol := Unit
  finiteSymbol := inferInstance
  relationOf := fun _ => pinRel d

/-- Unary constraint forcing variable `x` to be the supplied domain value. -/
def pinConstraint {D : Type} [Fintype D] (d : D) (x : Nat) :
    Constraint (pinLanguage d) where
  symbol := ()
  vars := unaryScope x

/-- Singleton formula forcing variable `x` to be the supplied domain value. -/
def pinFormula {D : Type} [Fintype D] (d : D) (x : Nat) :
    Formula (pinLanguage d) :=
  [pinConstraint d x]

@[simp]
theorem pinConstraint_satisfies_iff {D : Type} [Fintype D] (d : D) (x : Nat)
    (a : Assignment D) :
    Constraint.Satisfies (pinConstraint d x) a ↔ a x = d := by
  simp [Constraint.Satisfies, Constraint.assignmentTuple, pinConstraint, pinLanguage,
    pinRel, Rel.Holds]

@[simp]
theorem pinFormula_satisfies_iff {D : Type} [Fintype D] (d : D) (x : Nat)
    (a : Assignment D) :
    Formula.Satisfies (pinFormula d x) a ↔ a x = d := by
  simp [pinFormula]

/-- A unary pinning formula is satisfiable, witnessed by the pinned value. -/
theorem pinFormula_satisfiable {D : Type} [Fintype D] (d : D) (x : Nat) :
    Formula.Satisfiable (pinFormula d x) := by
  refine ⟨fun _ => d, ?_⟩
  simp

/-- A two-symbol standard language with equality and one supplied pin value. -/
inductive EqPinSymbol where
  | eq
  | pin
  deriving DecidableEq, Fintype, Repr

/-- Relation interpretation for `EqPinSymbol`. -/
def eqPinRelationOf {D : Type} (d : D) : EqPinSymbol → Rel D
  | EqPinSymbol.eq => equalityRel D
  | EqPinSymbol.pin => pinRel d

/-- Standard language containing equality and a unary pinning relation. -/
def eqPinLanguage {D : Type} [Fintype D] (d : D) : Language D where
  finiteDomain := inferInstance
  Symbol := EqPinSymbol
  finiteSymbol := inferInstance
  relationOf := eqPinRelationOf d

/-- Equality constraint in the combined equality/pinning language. -/
def eqPinEqualityConstraint {D : Type} [Fintype D] (d : D) (x y : Nat) :
    Constraint (eqPinLanguage d) where
  symbol := EqPinSymbol.eq
  vars := binaryScope x y

/-- Pinning constraint in the combined equality/pinning language. -/
def eqPinPinConstraint {D : Type} [Fintype D] (d : D) (x : Nat) :
    Constraint (eqPinLanguage d) where
  symbol := EqPinSymbol.pin
  vars := unaryScope x

@[simp]
theorem eqPinEqualityConstraint_satisfies_iff {D : Type} [Fintype D] (d : D)
    (x y : Nat) (a : Assignment D) :
    Constraint.Satisfies (eqPinEqualityConstraint d x y) a ↔ a x = a y := by
  simp [Constraint.Satisfies, Constraint.assignmentTuple, eqPinEqualityConstraint,
    eqPinLanguage, eqPinRelationOf, equalityRel, Rel.Holds]

@[simp]
theorem eqPinPinConstraint_satisfies_iff {D : Type} [Fintype D] (d : D)
    (x : Nat) (a : Assignment D) :
    Constraint.Satisfies (eqPinPinConstraint d x) a ↔ a x = d := by
  simp [Constraint.Satisfies, Constraint.assignmentTuple, eqPinPinConstraint,
    eqPinLanguage, eqPinRelationOf, pinRel, Rel.Holds]

/-- The relation accepting exactly one supplied tuple. -/
def singletonTupleRel {D : Type} {arity : Nat} (target : Tuple D arity) : Rel D where
  arity := arity
  holds := fun t => t = target

@[simp]
theorem singletonTupleRel_holds_iff {D : Type} {arity : Nat} (target : Tuple D arity)
    (t : Tuple D arity) :
    (singletonTupleRel target).Holds t ↔ t = target :=
  Iff.rfl

end StandardGadgets
end FiniteDomain
end CSP
end ComplexityReduction
