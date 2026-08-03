/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import ComplexityReduction.SAT.Literal

/-!
Direct Horn-CNF syntax and a generic satisfiability decider surface.

The executable unit-closure proof used by Schaefer remains available through the
Schaefer compatibility module; this generic module provides the stable
Schaefer-free syntax and theorem names for future reductions.
-/

namespace ComplexityReduction
namespace SAT
namespace Horn

/-- A Horn clause `p₁ ∧ ... ∧ pₙ -> head`; `none` is a goal/contradiction clause. -/
structure Clause where
  premises : Finset Nat
  head : Option Nat
  deriving DecidableEq

/-- A direct Horn-CNF formula is a conjunction of Horn implication clauses. -/
abbrev CNF : Type :=
  List Clause

namespace Clause

/-- Variables mentioned by a Horn clause. -/
def vars (c : Clause) : Finset Nat :=
  c.premises ∪ c.head.elim ∅ (fun x => {x})

/-- Instantiate a Horn clause by a variable map. -/
def mapVars (f : Nat → Nat) (c : Clause) : Clause where
  premises := c.premises.image f
  head := c.head.map f

/-- Satisfaction of one Horn implication clause by a Boolean assignment. -/
def Satisfies (c : Clause) (a : Assignment) : Prop :=
  (∀ x ∈ c.premises, a x = true) →
    match c.head with
    | some y => a y = true
    | none => False

/-- A conflict clause is a goal clause whose premises are already known. -/
def IsConflict (c : Clause) (known : Finset Nat) : Prop :=
  c.head = none ∧ c.premises ⊆ known

/-- Boolean conflict check for one goal clause. -/
def conflictBool (c : Clause) (known : Finset Nat) : Bool :=
  match c.head with
  | none => decide (c.premises ⊆ known)
  | some _ => false

theorem conflictBool_eq_true_iff (c : Clause) (known : Finset Nat) :
    c.conflictBool known = true ↔ c.IsConflict known := by
  unfold conflictBool IsConflict
  cases hHead : c.head with
  | none =>
      by_cases hPrem : c.premises ⊆ known
      · simp [hPrem]
      · simp [hPrem]
  | some y =>
      simp

end Clause

namespace CNF

/-- Variables mentioned by a Horn-CNF formula. -/
def vars : CNF → Finset Nat
  | [] => ∅
  | c :: cs => c.vars ∪ vars cs

/-- Satisfaction of a Horn-CNF formula. -/
def Satisfies (φ : CNF) (a : Assignment) : Prop :=
  ∀ c ∈ φ, c.Satisfies a

/-- Existential satisfiability of a Horn-CNF formula. -/
def Satisfiable (φ : CNF) : Prop :=
  ∃ a : Assignment, Satisfies φ a

/-- A set of known true variables is closed under all definite Horn clauses. -/
def Closed (φ : CNF) (known : Finset Nat) : Prop :=
  ∀ c ∈ φ, c.premises ⊆ known → ∀ y : Nat, c.head = some y → y ∈ known

/-- A known set triggers a goal/contradiction clause. -/
def HasConflict (φ : CNF) (known : Finset Nat) : Prop :=
  ∃ c ∈ φ, c.IsConflict known

/-- Boolean conflict check for a Horn-CNF formula. -/
def hasConflictBool : CNF → Finset Nat → Bool
  | [], _ => false
  | c :: cs, known => c.conflictBool known || hasConflictBool cs known

theorem hasConflictBool_eq_true_iff (φ : CNF) (known : Finset Nat) :
    hasConflictBool φ known = true ↔ HasConflict φ known := by
  induction φ with
  | nil =>
      simp [hasConflictBool, HasConflict]
  | cons c cs ih =>
      simp [hasConflictBool, HasConflict, ih, Clause.conflictBool_eq_true_iff]

/-- Noncomputable Boolean decision surface for direct Horn-CNF satisfiability. -/
noncomputable def decide (φ : CNF) : Bool := by
  classical
  exact if Satisfiable φ then true else false

theorem decide_eq_true_iff (φ : CNF) :
    decide φ = true ↔ Satisfiable φ := by
  classical
  unfold decide
  by_cases h : Satisfiable φ
  · simp [h]
  · simp [h]

theorem decide_eq_false_iff (φ : CNF) :
    decide φ = false ↔ ¬ Satisfiable φ := by
  rw [← Bool.not_eq_true, decide_eq_true_iff]

end CNF
end Horn
end SAT
end ComplexityReduction
