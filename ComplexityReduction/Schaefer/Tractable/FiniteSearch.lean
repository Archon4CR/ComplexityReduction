/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteSupport
import ComplexityReduction.Schaefer.DichotomyStatement

/-!
Compatibility wrapper for finite-variable satisfiability search in local
Schaefer `SAT(S)` formulas.

The implementation now lives in `ComplexityReduction.CSP.FiniteSupport`.  This
module preserves the previous Schaefer-facing namespace and theorem names.
-/

namespace ComplexityReduction
namespace Schaefer
namespace FiniteSearch

abbrev constraintVars {Γ : CSP.BoolLanguage} (c : CSP.Constraint Γ) : Finset Nat :=
  CSP.FiniteSupport.constraintVars c

abbrev formulaVars {Γ : CSP.BoolLanguage} (φ : SATFormula Γ) : Finset Nat :=
  CSP.FiniteSupport.formulaVars φ

@[simp]
theorem formulaVars_nil {Γ : CSP.BoolLanguage} :
    formulaVars ([] : SATFormula Γ) = ∅ :=
  rfl

@[simp]
theorem formulaVars_cons {Γ : CSP.BoolLanguage} (c : CSP.Constraint Γ) (φ : SATFormula Γ) :
    formulaVars (c :: φ) = constraintVars c ∪ formulaVars φ :=
  rfl

theorem mem_constraintVars {Γ : CSP.BoolLanguage} (c : CSP.Constraint Γ)
    (i : Fin (Γ.relationOf c.symbol).arity) :
    c.vars i ∈ constraintVars c :=
  CSP.FiniteSupport.mem_constraintVars c i

theorem constraintVars_subset_formulaVars_of_mem {Γ : CSP.BoolLanguage}
    {φ : SATFormula Γ} {c : CSP.Constraint Γ} (hc : c ∈ φ) :
    constraintVars c ⊆ formulaVars φ :=
  CSP.FiniteSupport.constraintVars_subset_formulaVars_of_mem hc

theorem var_mem_formulaVars_of_constraint_mem {Γ : CSP.BoolLanguage}
    {φ : SATFormula Γ} {c : CSP.Constraint Γ} (hc : c ∈ φ)
    (i : Fin (Γ.relationOf c.symbol).arity) :
    c.vars i ∈ formulaVars φ :=
  CSP.FiniteSupport.var_mem_formulaVars_of_constraint_mem hc i

abbrev assignmentOf {vars : Finset Nat}
    (values : {x : Nat // x ∈ vars} → Bool) : SAT.Assignment :=
  CSP.FiniteSupport.assignmentOf values

@[simp]
theorem assignmentOf_eq_of_mem {vars : Finset Nat}
    (values : {x : Nat // x ∈ vars} → Bool) {x : Nat} (hx : x ∈ vars) :
    assignmentOf values x = values ⟨x, hx⟩ :=
  CSP.FiniteSupport.assignmentOf_eq_of_mem values hx

theorem formula_satisfies_iff_of_agree {Γ : CSP.BoolLanguage}
    {φ : SATFormula Γ} {a b : SAT.Assignment}
    (hAgree : ∀ x ∈ formulaVars φ, a x = b x) :
    CSP.Formula.Satisfies φ a ↔ CSP.Formula.Satisfies φ b :=
  CSP.FiniteSupport.formula_satisfies_iff_of_agree hAgree

abbrev SearchWitness {Γ : CSP.BoolLanguage} (φ : SATFormula Γ) : Prop :=
  CSP.FiniteSupport.SearchWitness φ

noncomputable abbrev decide {Γ : CSP.BoolLanguage} (φ : SATFormula Γ) : Bool :=
  CSP.FiniteSupport.decide φ

theorem searchWitness_iff_satisfiable {Γ : CSP.BoolLanguage} (φ : SATFormula Γ) :
    SearchWitness φ ↔ SATSatisfiable φ :=
  CSP.FiniteSupport.searchWitness_iff_satisfiable φ

theorem decide_eq_true_iff {Γ : CSP.BoolLanguage} (φ : SATFormula Γ) :
    decide φ = true ↔ SATSatisfiable φ :=
  CSP.FiniteSupport.decide_eq_true_iff φ

end FiniteSearch
end Schaefer
end ComplexityReduction
