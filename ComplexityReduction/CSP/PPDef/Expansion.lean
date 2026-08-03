/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.PPDef.Renaming

/-!
Syntax expansion induced by proof-bearing language representations.
-/

namespace ComplexityReduction
namespace CSP
namespace PPDef

/-- A strict upper bound for variables mentioned by a source formula. -/
noncomputable def formulaVarBound {Γ : BoolLanguage} (φ : Formula Γ) : Nat :=
  (FiniteSupport.formulaVars φ).sup id + 1

theorem var_lt_formulaVarBound {Γ : BoolLanguage} {φ : Formula Γ} {x : Nat}
    (hx : x ∈ FiniteSupport.formulaVars φ) :
    x < formulaVarBound φ :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)

theorem constraint_var_lt_formulaVarBound_of_mem {Γ : BoolLanguage}
    {φ : Formula Γ} {c : Constraint Γ} (hc : c ∈ φ)
    (i : Fin (Γ.relationOf c.symbol).arity) :
    c.vars i < formulaVarBound φ :=
  var_lt_formulaVarBound (FiniteSupport.var_mem_formulaVars_of_constraint_mem hc i)

/--
Variable map for instantiating a representation block against one source
constraint.  Free variables `0, ..., arity - 1` are substituted by the source
constraint variables; all other variables are placed in the auxiliary block
starting at `auxBase`.
-/
def representationBlockVarMap {Δ : BoolLanguage} (c : Constraint Δ)
    (auxBase x : Nat) : Nat :=
  if h : x < (Δ.relationOf c.symbol).arity then c.vars ⟨x, h⟩ else auxBase + x

/-- Expand one source constraint through a representation block using a chosen auxiliary base. -/
def constraintViaRepresentationAt {Δ Γ : BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (c : Constraint Δ) (auxBase : Nat) :
    Formula Γ :=
  formulaMapVars
    (representationBlockVarMap c auxBase)
    (rep.block c.symbol).constraints

/--
Syntax map for expanding one source constraint through a language
representation, using a block just above the variables of that constraint.
-/
noncomputable def constraintViaRepresentation {Δ Γ : BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (c : Constraint Δ) : Formula Γ :=
  constraintViaRepresentationAt rep c (Constraint.maxVar c + 1)

/-- Recursive formula expansion with one fresh auxiliary block per source constraint. -/
noncomputable def formulaViaRepresentationFrom {Δ Γ : BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (auxBase blockWidth : Nat) :
    Formula Δ → Formula Γ
  | [] => []
  | c :: φ =>
      constraintViaRepresentationAt rep c auxBase ++
        formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ

/-- Formula-level expansion induced by a language representation. -/
noncomputable def formulaViaRepresentation {Δ Γ : BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (φ : Formula Δ) : Formula Γ :=
  formulaViaRepresentationFrom rep
    (formulaVarBound φ)
    rep.auxBlockWidth
    φ

@[simp]
theorem formulaMapVars_length {Γ : BoolLanguage} (f : Nat → Nat)
    (φ : Formula Γ) :
    (formulaMapVars f φ).length = φ.length := by
  simp [formulaMapVars]

@[simp]
theorem constraintViaRepresentationAt_length {Δ Γ : BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (c : Constraint Δ) (auxBase : Nat) :
    (constraintViaRepresentationAt rep c auxBase).length =
      (rep.block c.symbol).constraints.length := by
  simp [constraintViaRepresentationAt]

theorem formulaViaRepresentationFrom_length_le_maxBlockConstraints
    {Δ Γ : BoolLanguage} (rep : LanguageRepresentation Δ Γ)
    (auxBase blockWidth : Nat) (φ : Formula Δ) :
    (formulaViaRepresentationFrom rep auxBase blockWidth φ).length ≤
      φ.length * rep.maxBlockConstraints := by
  induction φ generalizing auxBase with
  | nil =>
      simp [formulaViaRepresentationFrom]
  | cons c φ ih =>
      rw [formulaViaRepresentationFrom, List.length_append, constraintViaRepresentationAt_length]
      let M := rep.maxBlockConstraints
      have hHead := rep.block_constraints_length_le_maxBlockConstraints c.symbol
      have hTail :
          (formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ).length ≤
            φ.length * M := by
        simpa [M] using ih (auxBase := auxBase + blockWidth)
      calc
        (rep.block c.symbol).constraints.length +
            (formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ).length
            ≤ M + φ.length * M := Nat.add_le_add hHead hTail
        _ = (φ.length + 1) * M := by
          rw [Nat.succ_mul]
          omega

end PPDef
end CSP
end ComplexityReduction
