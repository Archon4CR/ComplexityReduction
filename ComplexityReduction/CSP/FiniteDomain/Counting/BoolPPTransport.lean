/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Encoding
import ComplexityReduction.CSP.FiniteDomain.BoolPPTransport
import ComplexityReduction.CSP.FiniteDomain.Counting.BoolBridge

/-!
Count-preserving wrappers for Boolean pp transport into finite-domain CSPs.

The Boolean pp transport modules prove satisfiability preservation.  Exact
count preservation is exposed here only when the transported finite-domain pp
representation carries an explicit count-preservation certificate.
-/

namespace ComplexityReduction
namespace CSP

/-- Counting problem associated to a fixed Boolean CSP language. -/
noncomputable def boolCountingProblem (Γ : BoolLanguage) : CountingProblem :=
  { Instance := formulaEncodedType Γ
    count := fun φ => Formula.solutionCount φ }

@[simp]
theorem boolCountingProblem_count (Γ : BoolLanguage) (φ : Formula Γ) :
    (boolCountingProblem Γ).count φ = Formula.solutionCount φ :=
  rfl

namespace FiniteDomain
namespace BoolPPTransport

/--
A Boolean pp representation whose transport to the finite-domain `Bool` surface
preserves finite-support solution counts.
-/
structure CountPreservingBoolRepresentationCertificate (Δ Γ : BoolLanguage) where
  representation : ComplexityReduction.CSP.PPDef.LanguageRepresentation Δ Γ
  count_preserving :
    ∀ φ : Formula (BoolBridge.languageOfBoolLanguage Δ),
      Formula.solutionCount
          (PPDef.formulaViaRepresentation
            (languageRepresentationOfBool representation) φ) =
        Formula.solutionCount φ
  notes : String := ""

/--
A Boolean pp representation whose transport to the finite-domain `Fin 2`
surface preserves finite-support solution counts.
-/
structure CountPreservingFin2RepresentationCertificate (Δ Γ : BoolLanguage) where
  representation : ComplexityReduction.CSP.PPDef.LanguageRepresentation Δ Γ
  count_preserving :
    ∀ φ : Formula (BoolBridge.languageFin2OfBoolLanguage Δ),
      Formula.solutionCount
          (PPDef.formulaViaRepresentation
            (languageRepresentationFin2OfBool representation) φ) =
        Formula.solutionCount φ
  notes : String := ""

/-- Build a `Bool`-surface pp transport counting certificate from solution equivalences. -/
noncomputable def countPreservingBoolCertificateOfSolutionEquiv
    {Δ Γ : BoolLanguage}
    (rep : ComplexityReduction.CSP.PPDef.LanguageRepresentation Δ Γ)
    (solutionEquiv :
      ∀ φ : Formula (BoolBridge.languageOfBoolLanguage Δ),
        Formula.SolutionEquivCertificate φ
          (PPDef.formulaViaRepresentation (languageRepresentationOfBool rep) φ))
    (notes : String := "") :
    CountPreservingBoolRepresentationCertificate Δ Γ where
  representation := rep
  count_preserving := fun φ =>
    Formula.solutionCount_eq_of_solutionEquiv (solutionEquiv φ)
  notes := notes

/-- Build a `Fin 2`-surface pp transport counting certificate from solution equivalences. -/
noncomputable def countPreservingFin2CertificateOfSolutionEquiv
    {Δ Γ : BoolLanguage}
    (rep : ComplexityReduction.CSP.PPDef.LanguageRepresentation Δ Γ)
    (solutionEquiv :
      ∀ φ : Formula (BoolBridge.languageFin2OfBoolLanguage Δ),
        Formula.SolutionEquivCertificate φ
          (PPDef.formulaViaRepresentation (languageRepresentationFin2OfBool rep) φ))
    (notes : String := "") :
    CountPreservingFin2RepresentationCertificate Δ Γ where
  representation := rep
  count_preserving := fun φ =>
    Formula.solutionCount_eq_of_solutionEquiv (solutionEquiv φ)
  notes := notes

/-- Boolean pp transport to finite-domain `Bool` preserves counts when certified. -/
theorem solutionCount_formulaViaBoolPPTransport
    {Δ Γ : BoolLanguage}
    (cert : CountPreservingBoolRepresentationCertificate Δ Γ)
    (φ : ComplexityReduction.CSP.Formula Δ) :
    Formula.solutionCount (formulaViaBoolPPTransport cert.representation φ) =
      ComplexityReduction.CSP.Formula.solutionCount φ := by
  calc
    Formula.solutionCount (formulaViaBoolPPTransport cert.representation φ)
        = Formula.solutionCount (BoolBridge.formulaOfBoolFormula φ) := by
          simpa [formulaViaBoolPPTransport] using
            cert.count_preserving (BoolBridge.formulaOfBoolFormula φ)
    _ = ComplexityReduction.CSP.Formula.solutionCount φ :=
          BoolBridge.solutionCount_formulaOfBoolFormula φ

/-- Boolean pp transport to finite-domain `Fin 2` preserves counts when certified. -/
theorem solutionCount_formulaViaFin2BoolPPTransport
    {Δ Γ : BoolLanguage}
    (cert : CountPreservingFin2RepresentationCertificate Δ Γ)
    (φ : ComplexityReduction.CSP.Formula Δ) :
    Formula.solutionCount (formulaViaFin2BoolPPTransport cert.representation φ) =
      ComplexityReduction.CSP.Formula.solutionCount φ := by
  calc
    Formula.solutionCount (formulaViaFin2BoolPPTransport cert.representation φ)
        = Formula.solutionCount (BoolBridge.formulaFin2OfBoolFormula φ) := by
          simpa [formulaViaFin2BoolPPTransport] using
            cert.count_preserving (BoolBridge.formulaFin2OfBoolFormula φ)
    _ = ComplexityReduction.CSP.Formula.solutionCount φ :=
          BoolBridge.solutionCount_formulaFin2OfBoolFormula φ

/-- Count-preserving reduction induced by certified Boolean pp transport to `Bool`. -/
noncomputable def countingReduction_formulaViaBoolPPTransport
    {Δ Γ : BoolLanguage}
    (cert : CountPreservingBoolRepresentationCertificate Δ Γ) :
    CountingReduction
      (boolCountingProblem Δ)
      (countingProblem (BoolBridge.languageOfBoolLanguage Γ)) :=
  CountingReduction.of_count_eq
    (formulaViaBoolPPTransport cert.representation)
    (fun φ => solutionCount_formulaViaBoolPPTransport cert φ)

/-- Parsimonious reduction induced by certified Boolean pp transport to `Bool`. -/
noncomputable def parsimoniousReduction_formulaViaBoolPPTransport
    {Δ Γ : BoolLanguage}
    (cert : CountPreservingBoolRepresentationCertificate Δ Γ) :
    ParsimoniousReduction
      (boolCountingProblem Δ)
      (countingProblem (BoolBridge.languageOfBoolLanguage Γ)) :=
  ParsimoniousReduction.of_count_eq
    (formulaViaBoolPPTransport cert.representation)
    (fun φ => solutionCount_formulaViaBoolPPTransport cert φ)
    cert.notes

/-- Count-preserving reduction induced by certified Boolean pp transport to `Fin 2`. -/
noncomputable def countingReduction_formulaViaFin2BoolPPTransport
    {Δ Γ : BoolLanguage}
    (cert : CountPreservingFin2RepresentationCertificate Δ Γ) :
    CountingReduction
      (boolCountingProblem Δ)
      (countingProblem (BoolBridge.languageFin2OfBoolLanguage Γ)) :=
  CountingReduction.of_count_eq
    (formulaViaFin2BoolPPTransport cert.representation)
    (fun φ => solutionCount_formulaViaFin2BoolPPTransport cert φ)

/-- Parsimonious reduction induced by certified Boolean pp transport to `Fin 2`. -/
noncomputable def parsimoniousReduction_formulaViaFin2BoolPPTransport
    {Δ Γ : BoolLanguage}
    (cert : CountPreservingFin2RepresentationCertificate Δ Γ) :
    ParsimoniousReduction
      (boolCountingProblem Δ)
      (countingProblem (BoolBridge.languageFin2OfBoolLanguage Γ)) :=
  ParsimoniousReduction.of_count_eq
    (formulaViaFin2BoolPPTransport cert.representation)
    (fun φ => solutionCount_formulaViaFin2BoolPPTransport cert φ)
    cert.notes

end BoolPPTransport
end FiniteDomain
end CSP
end ComplexityReduction
