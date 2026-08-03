/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.PPSizeBounds
import ComplexityReduction.Certificates.CostedMap

/-!
Costed certificate wrappers for finite-domain pp-definition expansion.

The finite-domain CSP formula encoding is currently the project-local raw
encoding.  That makes the canonical pp-expansion map available as a costed
Karp reduction while the semantic and syntactic bounds remain explicit fields
that future structured encodings can reuse.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace PPDef

/-- The canonical finite-domain pp-expansion map has a costed certificate. -/
noncomputable def formulaViaRepresentationCostedMap {D : Type} {Δ Γ : Language D}
    (rep : LanguageRepresentation Δ Γ) :
    CostedMap (cspDecisionProblem Δ).Instance (cspDecisionProblem Γ).Instance
      (formulaViaRepresentation rep) :=
  CostedMap.of_emptyOutputEncoding (by
    intro φ
    rfl)

/-- The canonical finite-domain pp-expansion map is polynomial-time in the local model. -/
noncomputable def formulaViaRepresentationPolyTime {D : Type} {Δ Γ : Language D}
    (rep : LanguageRepresentation Δ Γ) :
    CostedPolyTimeModel.IsPolyTimeMap
      (X := (cspDecisionProblem Δ).Instance)
      (Y := (cspDecisionProblem Γ).Instance)
      (formulaViaRepresentation rep) :=
  CostedPolyTimeMap.of_costed (formulaViaRepresentationCostedMap rep)

/-- Finite-domain pp expansion as a costed Karp reduction. -/
noncomputable def formulaViaRepresentationKarpReduction {D : Type} {Δ Γ : Language D}
    (rep : LanguageRepresentation Δ Γ) :
    KarpReductionM CostedPolyTimeModel (cspDecisionProblem Δ) (cspDecisionProblem Γ) where
  f :=
    { toFun := formulaViaRepresentation rep
      polytime := formulaViaRepresentationPolyTime rep }
  correct := fun φ => (formulaViaRepresentation_satisfiable_iff rep φ).symm

/--
Proof-bearing certificate for the canonical finite-domain pp-expansion route.

Besides the Karp reduction, the certificate exposes the reusable syntactic
length and size bounds used by planner-side cost reasoning.
-/
structure FiniteDomainRepresentationReductionCertificate {D : Type}
    (Δ Γ : Language D) where
  representation : LanguageRepresentation Δ Γ
  mapFormula : Formula Δ → Formula Γ
  mapFormula_satisfiable_iff :
    ∀ φ : Formula Δ, Formula.Satisfiable (mapFormula φ) ↔ Formula.Satisfiable φ
  mapFormula_length_le :
    ∀ φ : Formula Δ, (mapFormula φ).length ≤
      φ.length * representation.maxBlockConstraints
  mapFormula_size_le :
    ∀ φ : Formula Δ, Formula.size (mapFormula φ) ≤
      (φ.length * representation.maxBlockConstraints) *
        Formula.maxConstraintSize (mapFormula φ)
  reduction :
    KarpReductionM CostedPolyTimeModel (cspDecisionProblem Δ) (cspDecisionProblem Γ)

namespace FiniteDomainRepresentationReductionCertificate

/-- Forget the extra size metadata and recover the older pp-reduction certificate surface. -/
def toRepresentationReductionCertificate {D : Type} {Δ Γ : Language D}
    (cert : FiniteDomainRepresentationReductionCertificate Δ Γ) :
    RepresentationReductionCertificate Δ Γ where
  representation := cert.representation
  mapFormula := cert.mapFormula
  mapFormula_satisfiable_iff := cert.mapFormula_satisfiable_iff
  reduction := cert.reduction

end FiniteDomainRepresentationReductionCertificate

/--
Package a finite-domain language representation into the canonical costed
pp-expansion certificate.
-/
noncomputable def finiteDomainRepresentationReductionCertificateOfLanguageRepresentation
    {D : Type} {Δ Γ : Language D} (rep : LanguageRepresentation Δ Γ) :
    FiniteDomainRepresentationReductionCertificate Δ Γ where
  representation := rep
  mapFormula := formulaViaRepresentation rep
  mapFormula_satisfiable_iff := formulaViaRepresentation_satisfiable_iff rep
  mapFormula_length_le := formulaViaRepresentation_length_le rep
  mapFormula_size_le := formulaViaRepresentation_size_le rep
  reduction := formulaViaRepresentationKarpReduction rep

/-- Costed Karp wrapper for one-symbol pp-derived language expansion. -/
noncomputable def formulaViaSingleDerivedRepresentationKarpReduction {D : Type}
    [Inhabited D] (Γ : Language D) {arity : Nat}
    (block : RelationFormula Γ arity) :
    KarpReductionM CostedPolyTimeModel
      (cspDecisionProblem (singleDerivedLanguage Γ block))
      (cspDecisionProblem Γ) :=
  formulaViaRepresentationKarpReduction (singleDerivedRepresentation Γ block)

/-- Certificate wrapper for one-symbol pp-derived language expansion. -/
noncomputable def finiteDomainSingleDerivedRepresentationReductionCertificate
    {D : Type} [Inhabited D] (Γ : Language D) {arity : Nat}
    (block : RelationFormula Γ arity) :
    FiniteDomainRepresentationReductionCertificate
      (singleDerivedLanguage Γ block) Γ :=
  finiteDomainRepresentationReductionCertificateOfLanguageRepresentation
    (singleDerivedRepresentation Γ block)

/-- Costed Karp wrapper for finite-family pp-derived language expansion. -/
noncomputable def formulaViaDerivedFamilyRepresentationKarpReduction {D : Type}
    [Inhabited D] (Γ : Language D) {NewSym : Type} [Fintype NewSym]
    (arityOf : NewSym → Nat)
    (block : ∀ s : NewSym, RelationFormula Γ (arityOf s)) :
    KarpReductionM CostedPolyTimeModel
      (cspDecisionProblem (derivedFamilyLanguage Γ arityOf block))
      (cspDecisionProblem Γ) :=
  formulaViaRepresentationKarpReduction (derivedFamilyRepresentation Γ arityOf block)

/-- Certificate wrapper for finite-family pp-derived language expansion. -/
noncomputable def finiteDomainDerivedFamilyRepresentationReductionCertificate
    {D : Type} [Inhabited D] (Γ : Language D) {NewSym : Type} [Fintype NewSym]
    (arityOf : NewSym → Nat)
    (block : ∀ s : NewSym, RelationFormula Γ (arityOf s)) :
    FiniteDomainRepresentationReductionCertificate
      (derivedFamilyLanguage Γ arityOf block) Γ :=
  finiteDomainRepresentationReductionCertificateOfLanguageRepresentation
    (derivedFamilyRepresentation Γ arityOf block)

end PPDef
end FiniteDomain
end CSP
end ComplexityReduction
