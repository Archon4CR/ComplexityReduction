/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.PPDef.Costed

/-!
Composition surface for generic pp-definition routes.

The canonical syntactic composition is available as a relation block.  Semantic
composition is exposed as a proof-bearing constructor whose caller supplies the
representation proof; Schaefer's hard-side module contains one such application
with the stronger local proof already established.
-/

namespace ComplexityReduction
namespace CSP
namespace PPDef

/--
Compose a single relation representation block through another language
representation.  The auxiliary block starts above both the free-variable range
and the variables already used by the intermediate block.
-/
noncomputable def relationFormulaViaRepresentationComposition
    {Δ Γ : BoolLanguage} (inner : LanguageRepresentation Δ Γ)
    (R : BoolRel) (rep : RelationFormula Δ R.arity) :
    RelationFormula Γ R.arity where
  constraints :=
    formulaViaRepresentationFrom inner
      (max R.arity (formulaVarBound rep.constraints))
      inner.auxBlockWidth
      rep.constraints
  notes := "Composition of relation representations."

/-- Proof-bearing composition package for two language representations. -/
structure LanguageRepresentationCompositionCertificate
    (Α Δ Γ : BoolLanguage)
    (outer : LanguageRepresentation Α Δ) (inner : LanguageRepresentation Δ Γ) where
  composedRepresents :
    ∀ s : Α.Symbol,
      RepresentsRelation Γ (Α.relationOf s)
        (relationFormulaViaRepresentationComposition inner (Α.relationOf s) (outer.block s))
  notes : String := ""

/-- Compose two language representations once the semantic composition proof is supplied. -/
noncomputable def composeLanguageRepresentation
    (Α Δ Γ : BoolLanguage)
    (outer : LanguageRepresentation Α Δ) (inner : LanguageRepresentation Δ Γ)
    (cert : LanguageRepresentationCompositionCertificate Α Δ Γ outer inner) :
    LanguageRepresentation Α Γ where
  block s :=
    relationFormulaViaRepresentationComposition inner (Α.relationOf s) (outer.block s)
  represents s := cert.composedRepresents s
  notes := cert.notes

end PPDef
end CSP
end ComplexityReduction
