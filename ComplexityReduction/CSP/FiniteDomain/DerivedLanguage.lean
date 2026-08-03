/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.CSP.FiniteDomain.Gadgets

/-!
Language-level wrappers for finite-domain pp-derived relations.

This module turns a pp-defined relation into a new relation symbol and supplies
the representation back into the target language.  It is the bridge from
relation-level gadgets to formula expansion through `LanguageRepresentation`.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace PPDef

/-- Extend `Γ` by one new relation symbol represented by `block`. -/
def singleDerivedLanguage {D : Type} (Γ : Language D) {arity : Nat}
    (block : RelationFormula Γ arity) : Language D where
  finiteDomain := Γ.finiteDomain
  Symbol := Γ.Symbol ⊕ Unit
  finiteSymbol := inferInstance
  relationOf
    | Sum.inl s => Γ.relationOf s
    | Sum.inr _ => block.definedRel

/-- The atomic pp block that represents an existing target-language symbol. -/
def atomicRelationFormula {D : Type} (Γ : Language D) (s : Γ.Symbol) :
    RelationFormula Γ (Γ.relationOf s).arity where
  constraints := [{ symbol := s, vars := fun i => i.val }]
  notes := "atomic"

/--
An existing language symbol represents itself by a single atomic constraint.
The auxiliary assignment witness needs a nonempty domain.
-/
theorem atomicRelationFormula_represents {D : Type} [Inhabited D]
    (Γ : Language D) (s : Γ.Symbol) :
    RepresentsRelation Γ (Γ.relationOf s) (atomicRelationFormula Γ s) := by
  intro t
  let c : Constraint Γ := { symbol := s, vars := fun i => i.val }
  constructor
  · intro h
    refine ⟨fun _ => default, ?_⟩
    intro d hd
    have hdEq : d = c := by
      simpa [atomicRelationFormula, c] using hd
    subst d
    have hTuple :
        Constraint.assignmentTuple c (extendTupleAssignment t (fun _ => default)) = t := by
      funext i
      simp [c, Constraint.assignmentTuple]
    simpa [Constraint.Satisfies, c, hTuple] using h
  · rintro ⟨aux, hAux⟩
    have hc : c ∈ (atomicRelationFormula Γ s).constraints := by
      simp [atomicRelationFormula, c]
    have hSat := hAux c hc
    have hTuple : Constraint.assignmentTuple c (extendTupleAssignment t aux) = t := by
      funext i
      simp [c, Constraint.assignmentTuple]
    simpa [Constraint.Satisfies, c, hTuple] using hSat

/-- Represent the one-symbol extension back in the target language. -/
def singleDerivedRepresentation {D : Type} [Inhabited D]
    (Γ : Language D) {arity : Nat} (block : RelationFormula Γ arity) :
    LanguageRepresentation (singleDerivedLanguage Γ block) Γ where
  block
    | Sum.inl s => atomicRelationFormula Γ s
    | Sum.inr _ => block
  represents
    | Sum.inl s => atomicRelationFormula_represents Γ s
    | Sum.inr _ => block.represents_definedRel
  notes := "single derived relation"

/-- Local variables in an atomic block are bounded by the represented relation arity. -/
theorem atomicRelationFormula_blockBound {D : Type} (Γ : Language D)
    (s : Γ.Symbol) {blockWidth : Nat}
    (hArity : (Γ.relationOf s).arity ≤ blockWidth) :
    ∀ c ∈ (atomicRelationFormula Γ s).constraints,
      ∀ i : Fin (Γ.relationOf c.symbol).arity, c.vars i < blockWidth := by
  intro c hc i
  have hcEq : c = { symbol := s, vars := fun i => i.val } := by
    simpa [atomicRelationFormula] using hc
  subst c
  exact lt_of_lt_of_le i.isLt hArity

/-- Block-width side condition for the single-derived representation. -/
theorem singleDerivedRepresentation_blockBound {D : Type} [Inhabited D]
    (Γ : Language D) {arity blockWidth : Nat} (block : RelationFormula Γ arity)
    (hBase : Γ.IsArityBounded blockWidth)
    (hDerived :
      ∀ c ∈ block.constraints, ∀ i : Fin (Γ.relationOf c.symbol).arity,
        c.vars i < blockWidth) :
    ∀ s : (singleDerivedLanguage Γ block).Symbol,
      ∀ c ∈ ((singleDerivedRepresentation Γ block).block s).constraints,
        ∀ i : Fin (Γ.relationOf c.symbol).arity, c.vars i < blockWidth := by
  intro s
  cases s with
  | inl base =>
      simpa [singleDerivedRepresentation] using
        atomicRelationFormula_blockBound Γ base (hBase base)
  | inr derived =>
      cases derived
      simpa [singleDerivedRepresentation] using hDerived

/-- Canonical formula expansion for the one-symbol derived-language extension. -/
noncomputable def formulaViaSingleDerivedRepresentationFrom {D : Type} [Inhabited D]
    (Γ : Language D) {arity : Nat} (block : RelationFormula Γ arity)
    (auxBase blockWidth : Nat) :
    Formula (singleDerivedLanguage Γ block) → Formula Γ :=
  formulaViaRepresentationFrom
    (singleDerivedRepresentation Γ block) auxBase blockWidth

/--
Satisfiability preservation for the canonical expansion from the one-symbol
derived-language extension, under the standard freshness and block-width
conditions used by `formulaViaRepresentationFrom_complete`.
-/
theorem formulaViaSingleDerivedRepresentationFrom_satisfiable_iff {D : Type}
    [Inhabited D] (Γ : Language D) {arity : Nat} (block : RelationFormula Γ arity)
    (auxBase blockWidth : Nat) (φ : Formula (singleDerivedLanguage Γ block))
    (hSourceFresh :
      ∀ c ∈ φ,
        ∀ i : Fin ((singleDerivedLanguage Γ block).relationOf c.symbol).arity,
          c.vars i < auxBase)
    (hBase : Γ.IsArityBounded blockWidth)
    (hDerived :
      ∀ c ∈ block.constraints, ∀ i : Fin (Γ.relationOf c.symbol).arity,
        c.vars i < blockWidth) :
    Formula.Satisfiable
        (formulaViaSingleDerivedRepresentationFrom Γ block auxBase blockWidth φ) ↔
      Formula.Satisfiable φ := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, formulaViaRepresentationFrom_sound
      (singleDerivedRepresentation Γ block) auxBase blockWidth φ a h⟩
  · rintro ⟨a, h⟩
    rcases formulaViaRepresentationFrom_complete
        (singleDerivedRepresentation Γ block) auxBase blockWidth φ a
        hSourceFresh
        (singleDerivedRepresentation_blockBound Γ block hBase hDerived)
        h with ⟨b, _hbBase, hbSat⟩
    exact ⟨b, hbSat⟩

end PPDef
end FiniteDomain
end CSP
end ComplexityReduction
