/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Finset.Card
import ComplexityReduction.SAT.Literal

/-!
Lightweight GF(2) linear-system syntax for affine SAT/CSP routes.
-/

namespace ComplexityReduction
namespace Algebra
namespace GF2

/-- A GF(2) linear equation over natural-number variables. -/
structure Equation where
  support : Finset Nat
  rhs : Bool
  deriving DecidableEq

namespace Equation

/-- The parity of variables in the equation support under an assignment. -/
def parity (e : Equation) (a : SAT.Assignment) : Nat :=
  (e.support.filter fun x => a x = true).card % 2

/-- Equation satisfaction over GF(2). -/
def Satisfies (e : Equation) (a : SAT.Assignment) : Prop :=
  e.parity a = if e.rhs then 1 else 0

end Equation

/-- A GF(2) linear system is a conjunction of equations. -/
abbrev System : Type :=
  List Equation

namespace System

/-- Variables mentioned by a GF(2) linear system. -/
def vars : System → Finset Nat
  | [] => ∅
  | e :: es => e.support ∪ vars es

/-- Satisfaction of a GF(2) linear system. -/
def Satisfies (sys : System) (a : SAT.Assignment) : Prop :=
  ∀ e ∈ sys, e.Satisfies a

/-- Existential satisfiability of a GF(2) linear system. -/
def Satisfiable (sys : System) : Prop :=
  ∃ a : SAT.Assignment, Satisfies sys a

end System
end GF2
end Algebra
end ComplexityReduction
