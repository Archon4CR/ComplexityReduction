/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteSupport

/-!
Generic primitive-positive definition blocks for Boolean CSP languages.

This module contains the Schaefer-independent syntax and semantics for relation
representations.  Application-specific hard certificates live outside this
module family.
-/

namespace ComplexityReduction
namespace CSP
namespace PPDef

/-- Extend a free Boolean tuple with a total auxiliary assignment. -/
def extendTupleAssignment {k : Nat} (t : BoolTuple k) (aux : SAT.Assignment) :
    SAT.Assignment :=
  fun x => if h : x < k then t ⟨x, h⟩ else aux x

@[simp]
theorem extendTupleAssignment_of_lt {k : Nat} (t : BoolTuple k)
    (aux : SAT.Assignment) {x : Nat} (hx : x < k) :
    extendTupleAssignment t aux x = t ⟨x, hx⟩ := by
  simp [extendTupleAssignment, hx]

/--
A primitive-positive style representation block over a target language `Γ`.

The free variables are expected at indices `0, ..., arity - 1`; all other
variables are auxiliary variables supplied by the existential witness in
`RepresentsRelation`.
-/
structure RelationFormula (Γ : BoolLanguage) (arity : Nat) where
  constraints : Formula Γ
  notes : String := ""

/-- Semantics of a local relation representation block. -/
def RepresentsRelation (Γ : BoolLanguage) (R : BoolRel)
    (rep : RelationFormula Γ R.arity) : Prop :=
  ∀ t : BoolTuple R.arity,
    R.Holds t ↔ ∃ aux : SAT.Assignment,
      Formula.Satisfies rep.constraints (extendTupleAssignment t aux)

namespace RelationFormula

/-- Largest variable mentioned in a representation block. -/
def maxVar {Γ : BoolLanguage} {arity : Nat} (rep : RelationFormula Γ arity) : Nat :=
  Formula.maxVar rep.constraints

end RelationFormula

/-- A representation for every relation symbol of a source language. -/
structure LanguageRepresentation (Δ Γ : BoolLanguage) where
  block : ∀ s : Δ.Symbol, RelationFormula Γ (Δ.relationOf s).arity
  represents : ∀ s : Δ.Symbol, RepresentsRelation Γ (Δ.relationOf s) (block s)
  notes : String := ""

namespace LanguageRepresentation

/-- A strict upper bound for the variables mentioned in one representation block. -/
noncomputable def blockVarBound {Δ Γ : BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (s : Δ.Symbol) : Nat :=
  (FiniteSupport.formulaVars (rep.block s).constraints).sup id + 1

/-- Largest variable used by any representation block in a fixed finite source language. -/
noncomputable def maxBlockVar {Δ Γ : BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) : Nat :=
  (Finset.univ : Finset Δ.Symbol).sup fun s =>
    (FiniteSupport.formulaVars (rep.block s).constraints).sup id

/-- A conservative per-source-constraint auxiliary width for block allocation. -/
noncomputable def auxBlockWidth {Δ Γ : BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) : Nat :=
  (Finset.univ : Finset Δ.Symbol).sup fun s => rep.blockVarBound s

/-- Maximum number of target constraints used by any representation block. -/
noncomputable def maxBlockConstraints {Δ Γ : BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) : Nat :=
  (Finset.univ : Finset Δ.Symbol).sup fun s => (rep.block s).constraints.length

theorem var_lt_blockVarBound {Δ Γ : BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (s : Δ.Symbol) {x : Nat}
    (hx : x ∈ FiniteSupport.formulaVars (rep.block s).constraints) :
    x < rep.blockVarBound s := by
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)

theorem blockVarBound_le_auxBlockWidth {Δ Γ : BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (s : Δ.Symbol) :
    rep.blockVarBound s ≤ rep.auxBlockWidth := by
  classical
  exact Finset.le_sup
    (s := (Finset.univ : Finset Δ.Symbol))
    (f := fun s => rep.blockVarBound s)
    (b := s)
    (Finset.mem_univ s)

theorem var_lt_auxBlockWidth {Δ Γ : BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (s : Δ.Symbol) {x : Nat}
    (hx : x ∈ FiniteSupport.formulaVars (rep.block s).constraints) :
    x < rep.auxBlockWidth :=
  lt_of_lt_of_le (rep.var_lt_blockVarBound s hx) (rep.blockVarBound_le_auxBlockWidth s)

theorem block_constraints_length_le_maxBlockConstraints {Δ Γ : BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (s : Δ.Symbol) :
    (rep.block s).constraints.length ≤ rep.maxBlockConstraints := by
  classical
  exact Finset.le_sup
    (s := (Finset.univ : Finset Δ.Symbol))
    (f := fun s => (rep.block s).constraints.length)
    (b := s)
    (Finset.mem_univ s)

end LanguageRepresentation

end PPDef
end CSP
end ComplexityReduction
