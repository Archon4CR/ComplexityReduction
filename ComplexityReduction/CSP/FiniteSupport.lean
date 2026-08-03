/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.SatLike

/-!
Finite-variable satisfiability search for Boolean CSP formulas.

A finite CSP formula only reads finitely many natural-number variables, so an
assignment on that finite support determines formula satisfaction.  This module
is the generic CSP version of the finite search wrapper originally introduced
for the Schaefer tractable branches.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteSupport

/-- Natural-number variables mentioned by one CSP constraint. -/
def constraintVars {Γ : BoolLanguage} (c : Constraint Γ) : Finset Nat :=
  (Finset.univ : Finset (Fin (Γ.relationOf c.symbol).arity)).image c.vars

/-- Natural-number variables mentioned by a Boolean CSP formula. -/
def formulaVars {Γ : BoolLanguage} : Formula Γ → Finset Nat
  | [] => ∅
  | c :: φ => constraintVars c ∪ formulaVars φ

@[simp]
theorem formulaVars_nil {Γ : BoolLanguage} :
    formulaVars ([] : Formula Γ) = ∅ :=
  rfl

@[simp]
theorem formulaVars_cons {Γ : BoolLanguage} (c : Constraint Γ) (φ : Formula Γ) :
    formulaVars (c :: φ) = constraintVars c ∪ formulaVars φ :=
  rfl

theorem mem_constraintVars {Γ : BoolLanguage} (c : Constraint Γ)
    (i : Fin (Γ.relationOf c.symbol).arity) :
    c.vars i ∈ constraintVars c := by
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem constraintVars_subset_formulaVars_of_mem {Γ : BoolLanguage}
    {φ : Formula Γ} {c : Constraint Γ} (hc : c ∈ φ) :
    constraintVars c ⊆ formulaVars φ := by
  induction φ with
  | nil =>
      simp at hc
  | cons d ds ih =>
      simp [formulaVars] at hc ⊢
      rcases hc with hEq | hc
      · subst hEq
        intro x hx
        exact Finset.mem_union.mpr (Or.inl hx)
      · intro x hx
        exact Finset.mem_union.mpr (Or.inr (ih hc hx))

theorem var_mem_formulaVars_of_constraint_mem {Γ : BoolLanguage}
    {φ : Formula Γ} {c : Constraint Γ} (hc : c ∈ φ)
    (i : Fin (Γ.relationOf c.symbol).arity) :
    c.vars i ∈ formulaVars φ :=
  constraintVars_subset_formulaVars_of_mem hc (mem_constraintVars c i)

/-- Turn a finite-support valuation into a total SAT assignment. -/
def assignmentOf {vars : Finset Nat} (values : {x : Nat // x ∈ vars} → Bool) :
    SAT.Assignment :=
  fun x => if h : x ∈ vars then values ⟨x, h⟩ else false

@[simp]
theorem assignmentOf_eq_of_mem {vars : Finset Nat}
    (values : {x : Nat // x ∈ vars} → Bool) {x : Nat} (hx : x ∈ vars) :
    assignmentOf values x = values ⟨x, hx⟩ := by
  simp [assignmentOf, hx]

theorem formula_satisfies_iff_of_agree {Γ : BoolLanguage}
    {φ : Formula Γ} {a b : SAT.Assignment}
    (hAgree : ∀ x ∈ formulaVars φ, a x = b x) :
    Formula.Satisfies φ a ↔ Formula.Satisfies φ b := by
  constructor
  · intro h c hc
    have hTuple : c.assignmentTuple a = c.assignmentTuple b := by
      funext i
      exact hAgree (c.vars i) (var_mem_formulaVars_of_constraint_mem hc i)
    change (Γ.relationOf c.symbol).Holds (c.assignmentTuple b)
    rw [← hTuple]
    exact h c hc
  · intro h c hc
    have hTuple : c.assignmentTuple a = c.assignmentTuple b := by
      funext i
      exact hAgree (c.vars i) (var_mem_formulaVars_of_constraint_mem hc i)
    change (Γ.relationOf c.symbol).Holds (c.assignmentTuple a)
    rw [hTuple]
    exact h c hc

/-- A finite-support witness for satisfiability. -/
def SearchWitness {Γ : BoolLanguage} (φ : Formula Γ) : Prop :=
  ∃ values : {x : Nat // x ∈ formulaVars φ} → Bool,
    Formula.Satisfies φ (assignmentOf values)

/-- Boolean finite-support satisfiability search. -/
noncomputable def decide {Γ : BoolLanguage} (φ : Formula Γ) : Bool := by
  classical
  exact if SearchWitness φ then true else false

theorem searchWitness_iff_satisfiable {Γ : BoolLanguage} (φ : Formula Γ) :
    SearchWitness φ ↔ Formula.Satisfiable φ := by
  constructor
  · rintro ⟨values, hSat⟩
    exact ⟨assignmentOf values, hSat⟩
  · rintro ⟨a, hSat⟩
    refine ⟨fun x => a x.val, ?_⟩
    exact (formula_satisfies_iff_of_agree (φ := φ) (a := assignmentOf (fun x => a x.val))
      (b := a) (by
        intro x hx
        simp [assignmentOf, hx])).2 hSat

theorem decide_eq_true_iff {Γ : BoolLanguage} (φ : Formula Γ) :
    decide φ = true ↔ Formula.Satisfiable φ := by
  classical
  unfold decide
  by_cases h : SearchWitness φ
  · simp [h, (searchWitness_iff_satisfiable φ).1 h]
  · have hUnsat : ¬ Formula.Satisfiable φ := by
      intro hSat
      exact h ((searchWitness_iff_satisfiable φ).2 hSat)
    simp [h, hUnsat]

end FiniteSupport
end CSP
end ComplexityReduction
