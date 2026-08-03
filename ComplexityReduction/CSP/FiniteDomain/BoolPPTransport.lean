/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.PPBounds
import ComplexityReduction.CSP.FiniteDomain.BoolBridge
import ComplexityReduction.CSP.PPDef.Expansion

/-!
Transport Boolean primitive-positive certificates into the finite-domain CSP
surface.

The Boolean CSP API and the finite-domain CSP API use parallel pp-definition
records.  This module converts proof-bearing Boolean certificates into
finite-domain certificates over either `Bool` or the two-element domain `Fin 2`,
then reuses the finite-domain pp expansion theorem.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace BoolPPTransport

/-- The finite-domain and Boolean pp extensions agree definitionally over `Bool`. -/
theorem extendTupleAssignment_bool_eq {k : Nat} (t : Tuple Bool k)
    (aux : Assignment Bool) :
    PPDef.extendTupleAssignment t aux =
      ComplexityReduction.CSP.PPDef.extendTupleAssignment t aux := by
  funext x
  by_cases hx : x < k
  · simp [PPDef.extendTupleAssignment, ComplexityReduction.CSP.PPDef.extendTupleAssignment, hx]
  · simp [PPDef.extendTupleAssignment, ComplexityReduction.CSP.PPDef.extendTupleAssignment, hx]

/-- Decoding a finite-domain `Fin 2` pp assignment yields the Boolean pp assignment. -/
theorem assignmentFin2ToBool_extendTupleAssignment {k : Nat} (t : Tuple (Fin 2) k)
    (aux : Assignment (Fin 2)) :
    BoolBridge.assignmentFin2ToBool (PPDef.extendTupleAssignment t aux) =
      ComplexityReduction.CSP.PPDef.extendTupleAssignment
        (BoolBridge.tupleFin2ToBool t)
        (BoolBridge.assignmentFin2ToBool aux) := by
  funext x
  by_cases hx : x < k
  · simp [BoolBridge.assignmentFin2ToBool, BoolBridge.tupleFin2ToBool,
      PPDef.extendTupleAssignment, ComplexityReduction.CSP.PPDef.extendTupleAssignment, hx]
  · simp [BoolBridge.assignmentFin2ToBool, PPDef.extendTupleAssignment,
      ComplexityReduction.CSP.PPDef.extendTupleAssignment, hx]

/-- Transport one Boolean pp block to the finite-domain `Bool` surface. -/
def relationFormulaOfBool {Γ : BoolLanguage} {arity : Nat}
    (rep : ComplexityReduction.CSP.PPDef.RelationFormula Γ arity) :
    PPDef.RelationFormula (BoolBridge.languageOfBoolLanguage Γ) arity where
  constraints := BoolBridge.formulaOfBoolFormula rep.constraints
  notes := rep.notes

/-- Transport one Boolean pp block to the finite-domain `Fin 2` surface. -/
def relationFormulaFin2OfBool {Γ : BoolLanguage} {arity : Nat}
    (rep : ComplexityReduction.CSP.PPDef.RelationFormula Γ arity) :
    PPDef.RelationFormula (BoolBridge.languageFin2OfBoolLanguage Γ) arity where
  constraints := BoolBridge.formulaFin2OfBoolFormula rep.constraints
  notes := rep.notes

theorem relationFormulaOfBool_represents {Γ : BoolLanguage} {R : BoolRel}
    (rep : ComplexityReduction.CSP.PPDef.RelationFormula Γ R.arity)
    (hrep : ComplexityReduction.CSP.PPDef.RepresentsRelation Γ R rep) :
    PPDef.RepresentsRelation
      (BoolBridge.languageOfBoolLanguage Γ)
      (BoolBridge.relOfBoolRel R)
      (relationFormulaOfBool rep) := by
  intro t
  have hBool := hrep t
  constructor
  · intro ht
    rcases hBool.1 ht with ⟨aux, haux⟩
    refine ⟨aux, ?_⟩
    exact (BoolBridge.formulaOfBoolFormula_satisfies_iff rep.constraints
      (PPDef.extendTupleAssignment t aux)).2 (by
        simpa [extendTupleAssignment_bool_eq t aux] using haux)
  · rintro ⟨aux, haux⟩
    exact hBool.2 ⟨aux, by
      have hBoolSat :=
        (BoolBridge.formulaOfBoolFormula_satisfies_iff rep.constraints
          (PPDef.extendTupleAssignment t aux)).1 haux
      simpa [extendTupleAssignment_bool_eq t aux] using hBoolSat⟩

theorem relationFormulaFin2OfBool_represents {Γ : BoolLanguage} {R : BoolRel}
    (rep : ComplexityReduction.CSP.PPDef.RelationFormula Γ R.arity)
    (hrep : ComplexityReduction.CSP.PPDef.RepresentsRelation Γ R rep) :
    PPDef.RepresentsRelation
      (BoolBridge.languageFin2OfBoolLanguage Γ)
      (BoolBridge.relFin2OfBoolRel R)
      (relationFormulaFin2OfBool rep) := by
  intro t
  have hBool := hrep (BoolBridge.tupleFin2ToBool t)
  constructor
  · intro ht
    rcases hBool.1 ht with ⟨aux, haux⟩
    refine ⟨BoolBridge.assignmentBoolToFin2 aux, ?_⟩
    refine (BoolBridge.formulaFin2OfBoolFormula_satisfies_iff rep.constraints
      (PPDef.extendTupleAssignment t (BoolBridge.assignmentBoolToFin2 aux))).2 ?_
    simpa [assignmentFin2ToBool_extendTupleAssignment t
      (BoolBridge.assignmentBoolToFin2 aux)] using haux
  · rintro ⟨aux, haux⟩
    have hDecoded :
        ComplexityReduction.CSP.Formula.Satisfies rep.constraints
          (ComplexityReduction.CSP.PPDef.extendTupleAssignment
            (BoolBridge.tupleFin2ToBool t)
            (BoolBridge.assignmentFin2ToBool aux)) := by
      have hBoolSat :=
        (BoolBridge.formulaFin2OfBoolFormula_satisfies_iff rep.constraints
          (PPDef.extendTupleAssignment t aux)).1 haux
      simpa [assignmentFin2ToBool_extendTupleAssignment t aux] using hBoolSat
    exact hBool.2 ⟨BoolBridge.assignmentFin2ToBool aux, hDecoded⟩

/-- Transport a Boolean language representation to the finite-domain `Bool` surface. -/
def languageRepresentationOfBool {Δ Γ : BoolLanguage}
    (rep : ComplexityReduction.CSP.PPDef.LanguageRepresentation Δ Γ) :
    PPDef.LanguageRepresentation
      (BoolBridge.languageOfBoolLanguage Δ)
      (BoolBridge.languageOfBoolLanguage Γ) where
  block := fun s => relationFormulaOfBool (rep.block s)
  represents := fun s => relationFormulaOfBool_represents (rep.block s) (rep.represents s)
  notes := rep.notes

/-- Transport a Boolean language representation to the finite-domain `Fin 2` surface. -/
def languageRepresentationFin2OfBool {Δ Γ : BoolLanguage}
    (rep : ComplexityReduction.CSP.PPDef.LanguageRepresentation Δ Γ) :
    PPDef.LanguageRepresentation
      (BoolBridge.languageFin2OfBoolLanguage Δ)
      (BoolBridge.languageFin2OfBoolLanguage Γ) where
  block := fun s => relationFormulaFin2OfBool (rep.block s)
  represents := fun s => relationFormulaFin2OfBool_represents (rep.block s) (rep.represents s)
  notes := rep.notes

/--
Expand a Boolean source formula through a Boolean pp certificate, returning a
finite-domain formula over `Bool`.
-/
noncomputable def formulaViaBoolPPTransport {Δ Γ : BoolLanguage}
    (rep : ComplexityReduction.CSP.PPDef.LanguageRepresentation Δ Γ)
    (φ : ComplexityReduction.CSP.Formula Δ) :
    Formula (BoolBridge.languageOfBoolLanguage Γ) :=
  PPDef.formulaViaRepresentation
    (languageRepresentationOfBool rep)
    (BoolBridge.formulaOfBoolFormula φ)

/--
Expand a Boolean source formula through a Boolean pp certificate, returning a
finite-domain formula over `Fin 2`.
-/
noncomputable def formulaViaFin2BoolPPTransport {Δ Γ : BoolLanguage}
    (rep : ComplexityReduction.CSP.PPDef.LanguageRepresentation Δ Γ)
    (φ : ComplexityReduction.CSP.Formula Δ) :
    Formula (BoolBridge.languageFin2OfBoolLanguage Γ) :=
  PPDef.formulaViaRepresentation
    (languageRepresentationFin2OfBool rep)
    (BoolBridge.formulaFin2OfBoolFormula φ)

theorem formulaViaBoolPPTransport_satisfiable_iff {Δ Γ : BoolLanguage}
    (rep : ComplexityReduction.CSP.PPDef.LanguageRepresentation Δ Γ)
    (φ : ComplexityReduction.CSP.Formula Δ) :
    Formula.Satisfiable (formulaViaBoolPPTransport rep φ) ↔
      ComplexityReduction.CSP.Formula.Satisfiable φ := by
  rw [formulaViaBoolPPTransport, PPDef.formulaViaRepresentation_satisfiable_iff,
    BoolBridge.formulaOfBoolFormula_satisfiable_iff]

theorem formulaViaFin2BoolPPTransport_satisfiable_iff {Δ Γ : BoolLanguage}
    (rep : ComplexityReduction.CSP.PPDef.LanguageRepresentation Δ Γ)
    (φ : ComplexityReduction.CSP.Formula Δ) :
    Formula.Satisfiable (formulaViaFin2BoolPPTransport rep φ) ↔
      ComplexityReduction.CSP.Formula.Satisfiable φ := by
  rw [formulaViaFin2BoolPPTransport, PPDef.formulaViaRepresentation_satisfiable_iff,
    BoolBridge.formulaFin2OfBoolFormula_satisfiable_iff]

end BoolPPTransport
end FiniteDomain
end CSP
end ComplexityReduction
