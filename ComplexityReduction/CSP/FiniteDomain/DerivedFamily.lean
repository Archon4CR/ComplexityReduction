/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.CSP.FiniteDomain.DerivedLanguage

/-!
Finite families of pp-derived relation symbols.

This module generalizes `singleDerivedLanguage`: a finite type of new symbols is
added to a target language, each new symbol is interpreted by the relation
defined by its pp block, and the whole extended language is represented back in
the target language.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace PPDef

/-- Extend `Γ` by a finite family of pp-derived relation symbols. -/
def derivedFamilyLanguage {D : Type} (Γ : Language D) {NewSym : Type}
    [Fintype NewSym] (arityOf : NewSym → Nat)
    (block : ∀ s : NewSym, RelationFormula Γ (arityOf s)) : Language D where
  finiteDomain := Γ.finiteDomain
  Symbol := Γ.Symbol ⊕ NewSym
  finiteSymbol := inferInstance
  relationOf
    | Sum.inl s => Γ.relationOf s
    | Sum.inr s => (block s).definedRel

/-- The derived-family language adds exactly the declared finite family of symbols. -/
theorem derivedFamilyLanguage_size {D : Type} (Γ : Language D) {NewSym : Type}
    [Fintype NewSym] (arityOf : NewSym → Nat)
    (block : ∀ s : NewSym, RelationFormula Γ (arityOf s)) :
    Fintype.card (derivedFamilyLanguage Γ arityOf block).Symbol =
      Fintype.card Γ.Symbol + Fintype.card NewSym := by
  change Fintype.card (Γ.Symbol ⊕ NewSym) =
    Fintype.card Γ.Symbol + Fintype.card NewSym
  exact Fintype.card_sum

/-- Represent a finite derived-family extension back in the target language. -/
def derivedFamilyRepresentation {D : Type} [Inhabited D]
    (Γ : Language D) {NewSym : Type} [Fintype NewSym]
    (arityOf : NewSym → Nat)
    (block : ∀ s : NewSym, RelationFormula Γ (arityOf s)) :
    LanguageRepresentation (derivedFamilyLanguage Γ arityOf block) Γ where
  block
    | Sum.inl s => atomicRelationFormula Γ s
    | Sum.inr s => block s
  represents
    | Sum.inl s => atomicRelationFormula_represents Γ s
    | Sum.inr s => (block s).represents_definedRel
  notes := "derived relation family"

/-- Block-width side condition for a finite derived-family representation. -/
theorem derivedFamilyRepresentation_blockBound {D : Type} [Inhabited D]
    (Γ : Language D) {NewSym : Type} [Fintype NewSym]
    (arityOf : NewSym → Nat)
    (block : ∀ s : NewSym, RelationFormula Γ (arityOf s))
    {blockWidth : Nat}
    (hBase : Γ.IsArityBounded blockWidth)
    (hDerived :
      ∀ s : NewSym, ∀ c ∈ (block s).constraints,
        ∀ i : Fin (Γ.relationOf c.symbol).arity, c.vars i < blockWidth) :
    ∀ s : (derivedFamilyLanguage Γ arityOf block).Symbol,
      ∀ c ∈ ((derivedFamilyRepresentation Γ arityOf block).block s).constraints,
        ∀ i : Fin (Γ.relationOf c.symbol).arity, c.vars i < blockWidth := by
  intro s
  cases s with
  | inl base =>
      simpa [derivedFamilyRepresentation] using
        atomicRelationFormula_blockBound Γ base (hBase base)
  | inr derived =>
      simpa [derivedFamilyRepresentation] using hDerived derived

/-- Canonical formula expansion for a finite derived-family extension. -/
noncomputable def formulaViaDerivedFamilyRepresentationFrom {D : Type}
    [Inhabited D] (Γ : Language D) {NewSym : Type} [Fintype NewSym]
    (arityOf : NewSym → Nat)
    (block : ∀ s : NewSym, RelationFormula Γ (arityOf s))
    (auxBase blockWidth : Nat) :
    Formula (derivedFamilyLanguage Γ arityOf block) → Formula Γ :=
  formulaViaRepresentationFrom
    (derivedFamilyRepresentation Γ arityOf block) auxBase blockWidth

/--
Satisfiability preservation for canonical expansion from a finite family of
pp-derived relation symbols back to the target language.
-/
theorem formulaViaDerivedFamilyRepresentationFrom_satisfiable_iff {D : Type}
    [Inhabited D] (Γ : Language D) {NewSym : Type} [Fintype NewSym]
    (arityOf : NewSym → Nat)
    (block : ∀ s : NewSym, RelationFormula Γ (arityOf s))
    (auxBase blockWidth : Nat) (φ : Formula (derivedFamilyLanguage Γ arityOf block))
    (hSourceFresh :
      ∀ c ∈ φ,
        ∀ i : Fin ((derivedFamilyLanguage Γ arityOf block).relationOf c.symbol).arity,
          c.vars i < auxBase)
    (hBase : Γ.IsArityBounded blockWidth)
    (hDerived :
      ∀ s : NewSym, ∀ c ∈ (block s).constraints,
        ∀ i : Fin (Γ.relationOf c.symbol).arity, c.vars i < blockWidth) :
    Formula.Satisfiable
        (formulaViaDerivedFamilyRepresentationFrom Γ arityOf block auxBase blockWidth φ) ↔
      Formula.Satisfiable φ := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, formulaViaRepresentationFrom_sound
      (derivedFamilyRepresentation Γ arityOf block) auxBase blockWidth φ a h⟩
  · rintro ⟨a, h⟩
    rcases formulaViaRepresentationFrom_complete
        (derivedFamilyRepresentation Γ arityOf block) auxBase blockWidth φ a
        hSourceFresh
        (derivedFamilyRepresentation_blockBound Γ arityOf block hBase hDerived)
        h with ⟨b, _hbBase, hbSat⟩
    exact ⟨b, hbSat⟩

end PPDef
end FiniteDomain
end CSP
end ComplexityReduction
