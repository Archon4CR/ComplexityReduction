/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.PPDef.Basic

/-!
Variable-renaming primitives for generic CSP pp-definition blocks.
-/

namespace ComplexityReduction
namespace CSP
namespace PPDef

/-- Rename all variables in one target-language constraint. -/
def constraintMapVars {Γ : BoolLanguage} (f : Nat → Nat)
    (c : Constraint Γ) : Constraint Γ where
  symbol := c.symbol
  vars := fun i => f (c.vars i)

@[simp]
theorem constraintMapVars_satisfies_iff {Γ : BoolLanguage} (f : Nat → Nat)
    (c : Constraint Γ) (a : SAT.Assignment) :
    Constraint.Satisfies (constraintMapVars f c) a ↔
      Constraint.Satisfies c (fun x => a (f x)) :=
  Iff.rfl

/-- Rename all variables in a target-language formula. -/
def formulaMapVars {Γ : BoolLanguage} (f : Nat → Nat)
    (φ : Formula Γ) : Formula Γ :=
  φ.map (constraintMapVars f)

@[simp]
theorem formulaMapVars_nil {Γ : BoolLanguage} (f : Nat → Nat) :
    formulaMapVars f ([] : Formula Γ) = [] :=
  rfl

@[simp]
theorem formulaMapVars_cons {Γ : BoolLanguage} (f : Nat → Nat)
    (c : Constraint Γ) (φ : Formula Γ) :
    formulaMapVars f (c :: φ) = constraintMapVars f c :: formulaMapVars f φ :=
  rfl

@[simp]
theorem formulaMapVars_satisfies_iff {Γ : BoolLanguage} (f : Nat → Nat)
    (φ : Formula Γ) (a : SAT.Assignment) :
    Formula.Satisfies (formulaMapVars f φ) a ↔
      Formula.Satisfies φ (fun x => a (f x)) := by
  induction φ with
  | nil =>
      simp
  | cons c φ ih =>
      simp [ih]

@[simp]
theorem finiteSupport_formulaVars_append {Γ : BoolLanguage}
    (φ ψ : Formula Γ) :
    FiniteSupport.formulaVars (φ ++ ψ) =
      FiniteSupport.formulaVars φ ∪ FiniteSupport.formulaVars ψ := by
  induction φ with
  | nil =>
      simp [FiniteSupport.formulaVars]
  | cons c φ ih =>
      simp [FiniteSupport.formulaVars, ih, Finset.union_assoc]

end PPDef
end CSP
end ComplexityReduction
