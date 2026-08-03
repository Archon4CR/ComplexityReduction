/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.PPDef.Expansion
import ComplexityReduction.CSP.SatLike
import ComplexityReduction.Certificates.CostedMap

/-!
Costed certificate surface for pp-definition expansion routes.
-/

namespace ComplexityReduction
namespace CSP
namespace PPDef

/--
Proof-bearing formula expansion certificate.

Concrete applications may use the canonical `formulaViaRepresentation` map or a
hand-optimized expansion map; the certificate records semantic correctness and a
model-level Karp reduction over generic Boolean CSP decision problems.
-/
structure RepresentationReductionCertificate (Δ Γ : BoolLanguage) where
  representation : LanguageRepresentation Δ Γ
  mapFormula : Formula Δ → Formula Γ
  mapFormula_satisfiable_iff :
    ∀ φ : Formula Δ, Formula.Satisfiable (mapFormula φ) ↔ Formula.Satisfiable φ
  reduction :
    KarpReductionM CostedPolyTimeModel (boolCSPDecisionProblem Δ) (boolCSPDecisionProblem Γ)

/--
Package any proved semantic/costed canonical expansion into the generic
certificate surface.
-/
noncomputable def representationReductionCertificateOfLanguageRepresentation
    {Δ Γ : BoolLanguage} (rep : LanguageRepresentation Δ Γ)
    (hSat :
      ∀ φ : Formula Δ,
        Formula.Satisfiable (formulaViaRepresentation rep φ) ↔ Formula.Satisfiable φ)
    (hPoly :
      CostedPolyTimeModel.IsPolyTimeMap
        (X := (boolCSPDecisionProblem Δ).Instance)
        (Y := (boolCSPDecisionProblem Γ).Instance)
        (formulaViaRepresentation rep)) :
    RepresentationReductionCertificate Δ Γ where
  representation := rep
  mapFormula := formulaViaRepresentation rep
  mapFormula_satisfiable_iff := hSat
  reduction :=
    { f := { toFun := formulaViaRepresentation rep, polytime := hPoly }
      correct := fun φ => (hSat φ).symm }

end PPDef
end CSP
end ComplexityReduction
