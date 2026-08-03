/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Pi
import ComplexityReduction.CSP.FiniteDomain.LanguageBounds

/-!
Finite support search for finite-domain CSP formulas.

The search enumerates assignments only on the finite set of variables mentioned
by a formula, then extends them to total assignments using a default value.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace FiniteSearch

open FiniteSupport

/-- All total assignments induced by valuations of a finite variable set. -/
noncomputable def assignmentsOn {D : Type} [Fintype D] [Inhabited D]
    (vars : Finset Nat) : List (Assignment D) := by
  classical
  letI : Fintype {x : Nat // x ∈ vars} := Finset.Subtype.fintype vars
  letI : DecidableEq {x : Nat // x ∈ vars} := Classical.decEq _
  exact ((Finset.univ : Finset ({x : Nat // x ∈ vars} → D)).toList).map assignmentOf

theorem assignmentOf_mem_assignmentsOn {D : Type} [Fintype D] [Inhabited D]
    {vars : Finset Nat} (values : {x : Nat // x ∈ vars} → D) :
    assignmentOf values ∈ assignmentsOn vars := by
  classical
  letI : Fintype {x : Nat // x ∈ vars} := Finset.Subtype.fintype vars
  letI : DecidableEq {x : Nat // x ∈ vars} := Classical.decEq _
  unfold assignmentsOn
  exact List.mem_map.mpr ⟨values, Finset.mem_toList.mpr (Finset.mem_univ values), rfl⟩

/-- Every total assignment is matched on `vars` by an enumerated finite-support assignment. -/
theorem exists_mem_assignmentsOn_agree {D : Type} [Fintype D] [Inhabited D]
    (vars : Finset Nat) (a : Assignment D) :
    ∃ b ∈ assignmentsOn vars, ∀ x ∈ vars, b x = a x := by
  let values : {x : Nat // x ∈ vars} → D := fun x => a x.val
  refine ⟨assignmentOf values, assignmentOf_mem_assignmentsOn values, ?_⟩
  intro x hx
  simp [assignmentOf, hx, values]

/-- A formula is satisfied by at least one enumerated finite-support assignment. -/
def satisfiesAnyAssignment {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} (φ : Formula Γ) : Prop :=
  ∃ a ∈ assignmentsOn (formulaVars φ), Formula.Satisfies φ a

theorem satisfiesAnyAssignment_iff_satisfiable {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} (φ : Formula Γ) :
    satisfiesAnyAssignment φ ↔ Formula.Satisfiable φ := by
  constructor
  · rintro ⟨a, _haMem, hSat⟩
    exact ⟨a, hSat⟩
  · rintro ⟨a, hSat⟩
    rcases exists_mem_assignmentsOn_agree (formulaVars φ) a with
      ⟨b, hbMem, hbAgree⟩
    refine ⟨b, hbMem, ?_⟩
    exact (formula_satisfies_iff_of_agree (φ := φ) (a := a) (b := b) (by
      intro x hx
      exact (hbAgree x hx).symm)).1 hSat

/-- First satisfying finite-support assignment, if the finite search finds one. -/
noncomputable def satisfyingAssignment? {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} (φ : Formula Γ) : Option (Assignment D) := by
  classical
  exact (assignmentsOn (formulaVars φ)).find? fun a => decide (Formula.Satisfies φ a)

theorem satisfyingAssignment?_isSome_iff_satisfiable {D : Type} [Fintype D]
    [Inhabited D] {Γ : Language D} (φ : Formula Γ) :
    (satisfyingAssignment? φ).isSome ↔ Formula.Satisfiable φ := by
  classical
  unfold satisfyingAssignment?
  rw [List.find?_isSome]
  constructor
  · rintro ⟨a, haMem, haSatBool⟩
    exact (satisfiesAnyAssignment_iff_satisfiable φ).1 ⟨a, haMem, by
      simpa using haSatBool⟩
  · intro hSat
    rcases (satisfiesAnyAssignment_iff_satisfiable φ).2 hSat with ⟨a, haMem, haSat⟩
    exact ⟨a, haMem, by simpa using haSat⟩

theorem satisfyingAssignment?_sound {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} {φ : Formula Γ} {a : Assignment D}
    (h : satisfyingAssignment? φ = some a) :
    Formula.Satisfies φ a := by
  classical
  have hBool := List.find?_some (p := fun a => decide (Formula.Satisfies φ a)) h
  simpa using hBool

end FiniteSearch
end FiniteDomain
end CSP
end ComplexityReduction
