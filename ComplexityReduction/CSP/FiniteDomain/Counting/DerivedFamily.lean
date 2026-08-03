/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.Counting.Bijection
import ComplexityReduction.CSP.FiniteDomain.DerivedFamily

/-!
Count-preserving certificates for finite families of pp-derived relation symbols.

Plain pp expansion preserves satisfiability, not witness counts.  This module
therefore exposes count-preserving derived-family routes only through an
explicit equivalence between finite-support solution valuations.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace PPDef

/--
A finite pp-derived language family together with a per-formula equivalence of
finite-support solution valuations for the canonical representation expansion.
-/
structure DerivedFamilyCountPreservingCertificate {D : Type} [Fintype D] [Inhabited D]
    (Γ : Language D) {NewSym : Type} [Fintype NewSym]
    (arityOf : NewSym → Nat)
    (block : ∀ s : NewSym, RelationFormula Γ (arityOf s)) where
  solution_equiv :
    ∀ φ : Formula (derivedFamilyLanguage Γ arityOf block),
      Formula.SolutionEquivCertificate φ
        (formulaViaRepresentation (derivedFamilyRepresentation Γ arityOf block) φ)
  notes : String := ""

/-- Build a derived-family count-preservation certificate from solution equivalences. -/
noncomputable def countPreservingDerivedFamilyCertificateOfSolutionEquiv
    {D : Type} [Fintype D] [Inhabited D]
    (Γ : Language D) {NewSym : Type} [Fintype NewSym]
    (arityOf : NewSym → Nat)
    (block : ∀ s : NewSym, RelationFormula Γ (arityOf s))
    (solutionEquiv :
      ∀ φ : Formula (derivedFamilyLanguage Γ arityOf block),
        Formula.SolutionEquivCertificate φ
          (formulaViaRepresentation (derivedFamilyRepresentation Γ arityOf block) φ))
    (notes : String := "") :
    DerivedFamilyCountPreservingCertificate Γ arityOf block where
  solution_equiv := solutionEquiv
  notes := notes

/-- A certified derived-family representation preserves finite-support solution counts. -/
theorem solutionCount_viaDerivedFamilyRepresentation
    {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} {NewSym : Type} [Fintype NewSym]
    {arityOf : NewSym → Nat}
    {block : ∀ s : NewSym, RelationFormula Γ (arityOf s)}
    (cert : DerivedFamilyCountPreservingCertificate Γ arityOf block)
    (φ : Formula (derivedFamilyLanguage Γ arityOf block)) :
    Formula.solutionCount
        (formulaViaRepresentation (derivedFamilyRepresentation Γ arityOf block) φ) =
      Formula.solutionCount φ :=
  Formula.solutionCount_eq_of_solutionEquiv (cert.solution_equiv φ)

/--
Forget the derived-family wrapper to the generic count-preserving pp
representation certificate.
-/
noncomputable def DerivedFamilyCountPreservingCertificate.toRepresentationCertificate
    {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} {NewSym : Type} [Fintype NewSym]
    {arityOf : NewSym → Nat}
    {block : ∀ s : NewSym, RelationFormula Γ (arityOf s)}
    (cert : DerivedFamilyCountPreservingCertificate Γ arityOf block) :
    CountPreservingRepresentationCertificate
      (derivedFamilyLanguage Γ arityOf block) Γ where
  representation := derivedFamilyRepresentation Γ arityOf block
  count_preserving := fun φ => solutionCount_viaDerivedFamilyRepresentation cert φ
  notes := cert.notes

/-- Count-preserving reduction induced by a certified finite derived-family expansion. -/
noncomputable def countingReduction_viaDerivedFamilyRepresentation
    {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} {NewSym : Type} [Fintype NewSym]
    {arityOf : NewSym → Nat}
    {block : ∀ s : NewSym, RelationFormula Γ (arityOf s)}
    (cert : DerivedFamilyCountPreservingCertificate Γ arityOf block) :
    CountingReduction
      (countingProblem (derivedFamilyLanguage Γ arityOf block))
      (countingProblem Γ) :=
  CountingReduction.of_count_eq
    (formulaViaRepresentation (derivedFamilyRepresentation Γ arityOf block))
    (fun φ => solutionCount_viaDerivedFamilyRepresentation cert φ)

/-- Parsimonious reduction induced by a certified finite derived-family expansion. -/
noncomputable def parsimoniousReduction_viaDerivedFamilyRepresentation
    {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} {NewSym : Type} [Fintype NewSym]
    {arityOf : NewSym → Nat}
    {block : ∀ s : NewSym, RelationFormula Γ (arityOf s)}
    (cert : DerivedFamilyCountPreservingCertificate Γ arityOf block) :
    ParsimoniousReduction
      (countingProblem (derivedFamilyLanguage Γ arityOf block))
      (countingProblem Γ) :=
  ParsimoniousReduction.of_count_eq
    (formulaViaRepresentation (derivedFamilyRepresentation Γ arityOf block))
    (fun φ => solutionCount_viaDerivedFamilyRepresentation cert φ)
    cert.notes

end PPDef
end FiniteDomain
end CSP
end ComplexityReduction
