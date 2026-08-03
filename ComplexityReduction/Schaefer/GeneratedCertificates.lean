/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Schaefer.Dichotomy

/-!
Lean-side API for generated finite-language Schaefer hard certificates.

The generator may emit proof terms for these fields after it constructs a
finite truth-table language, but Python truth-table checks alone are not a
substitute for the Lean proofs stored here.  If a generated task cannot provide
all fields, it should report `remaining_obligations` and stay on the upper-bound
route until P11 consumes this API.
-/

namespace ComplexityReduction
namespace Schaefer

/-- Individual Lean obligations needed for a generated hard-case certificate. -/
inductive GeneratedHardCaseObligation where
  | allRelationsNonempty
  | notZeroValid
  | notOneValid
  | notHorn
  | notDualHorn
  | notAffine
  | notBijunctive
  deriving DecidableEq, Repr

namespace GeneratedHardCaseObligation

/-- Stable manifest spelling for generated hard-certificate obligations. -/
def asString : GeneratedHardCaseObligation → String
  | allRelationsNonempty => "all-relations-nonempty"
  | notZeroValid => "not-zero-valid"
  | notOneValid => "not-one-valid"
  | notHorn => "not-Horn"
  | notDualHorn => "not-dual-Horn"
  | notAffine => "not-affine"
  | notBijunctive => "not-bijunctive"

end GeneratedHardCaseObligation

/-- Full obligation list for generated hard-case certificates. -/
def generatedHardCaseObligations : List GeneratedHardCaseObligation :=
  [ GeneratedHardCaseObligation.allRelationsNonempty
  , GeneratedHardCaseObligation.notZeroValid
  , GeneratedHardCaseObligation.notOneValid
  , GeneratedHardCaseObligation.notHorn
  , GeneratedHardCaseObligation.notDualHorn
  , GeneratedHardCaseObligation.notAffine
  , GeneratedHardCaseObligation.notBijunctive
  ]

theorem generatedHardCaseObligations_length :
    generatedHardCaseObligations.length = 7 :=
  rfl

/--
Proof object a generated finite Boolean language must provide before it can use
the local hard-side Schaefer route as a hard certificate.
-/
structure GeneratedHardCaseCertificate (Γ : CSP.BoolLanguage) where
  allRelationsNonempty : Hardness.AllRelationsNonempty Γ
  notZeroValid : ¬ IsZeroValidLanguage Γ
  notOneValid : ¬ IsOneValidLanguage Γ
  notHorn : ¬ IsHornLanguage Γ
  notDualHorn : ¬ IsDualHornLanguage Γ
  notAffine : ¬ IsAffineLanguage Γ
  notBijunctive : ¬ IsBijunctiveLanguage Γ
  notes : String := ""

namespace GeneratedHardCaseCertificate

/-- Collapse generated proof fields to the standard hard-case assumption package. -/
def toHardCaseAssumptions {Γ : CSP.BoolLanguage}
    (cert : GeneratedHardCaseCertificate Γ) :
    HardCaseAssumptions Γ where
  notZeroValid := cert.notZeroValid
  notOneValid := cert.notOneValid
  notHorn := cert.notHorn
  notDualHorn := cert.notDualHorn
  notAffine := cert.notAffine
  notBijunctive := cert.notBijunctive

/-- Generated certificate route to the local hard relation certificate. -/
noncomputable def toHardRelationCertificate {Γ : CSP.BoolLanguage}
    (cert : GeneratedHardCaseCertificate Γ) :
    Hardness.HardRelationCertificate Γ :=
  Hardness.hardRelationCertificateOfHardCase
    cert.allRelationsNonempty cert.toHardCaseAssumptions

/-- Generated certificate route to the boundary-explicit hard-side theorem. -/
theorem hardSide_npComplete_fromBoundary {Γ : CSP.BoolLanguage}
    (cert : GeneratedHardCaseCertificate Γ)
    (B : Targets.ThreeSATCompleteBoundary) :
    NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem Γ) :=
  (Hardness.hardSideStatement_ofHardCase cert.allRelationsNonempty)
    cert.toHardCaseAssumptions B

end GeneratedHardCaseCertificate

/-- Generated proof-object accessor for the nonempty-relation precondition. -/
theorem generated_allRelationsNonempty {Γ : CSP.BoolLanguage}
    (cert : GeneratedHardCaseCertificate Γ) :
    Hardness.AllRelationsNonempty Γ :=
  cert.allRelationsNonempty

/-- Generated proof-object accessor for the six hard-case assumptions. -/
theorem generated_hardCaseAssumptions {Γ : CSP.BoolLanguage}
    (cert : GeneratedHardCaseCertificate Γ) :
    HardCaseAssumptions Γ :=
  cert.toHardCaseAssumptions

/--
Generated compatibility wrapper with an explicit 3SAT-completeness parameter.
-/
theorem generated_localSchaeferDichotomy_completeExceptCookLevin
    (Γ : CSP.BoolLanguage) (B : Targets.ThreeSATCompleteBoundary) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) ∨
      NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem Γ) :=
  localSchaeferDichotomy_completeExceptCookLevin Γ B

/-- Generated final local dichotomy wrapper using the P14e Cook-Levin discharge. -/
theorem generated_localSchaeferDichotomy_complete
    (Γ : CSP.BoolLanguage) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) ∨
      NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem Γ) :=
  localSchaeferDichotomy_complete Γ

/-- Generated hard-case route status: either Lean-certified or still obligation-only. -/
inductive GeneratedHardCaseRoute (Γ : CSP.BoolLanguage) where
  | certified : GeneratedHardCaseCertificate Γ → GeneratedHardCaseRoute Γ
  | remaining_obligations :
      List GeneratedHardCaseObligation → GeneratedHardCaseRoute Γ

namespace GeneratedHardCaseRoute

/-- Manifest status for a generated hard-case route. -/
def status {Γ : CSP.BoolLanguage} : GeneratedHardCaseRoute Γ → String
  | certified _ => "certified"
  | remaining_obligations _ => "remaining_obligations"

/-- Extract the remaining Lean obligations, or the empty list for a certified route. -/
def remainingObligations {Γ : CSP.BoolLanguage} :
    GeneratedHardCaseRoute Γ → List GeneratedHardCaseObligation
  | certified _ => []
  | remaining_obligations obligations => obligations

/-- Extract the checked certificate when the generated route is fully certified. -/
def certificate? {Γ : CSP.BoolLanguage} :
    GeneratedHardCaseRoute Γ → Option (GeneratedHardCaseCertificate Γ)
  | certified cert => some cert
  | remaining_obligations _ => none

theorem certified_remainingObligations_empty {Γ : CSP.BoolLanguage}
    (cert : GeneratedHardCaseCertificate Γ) :
    (GeneratedHardCaseRoute.certified cert).remainingObligations = [] :=
  rfl

end GeneratedHardCaseRoute

/-- Descriptor for the generated finite-language hard-certificate API. -/
def generatedHardCertificateDescriptor : StatementDescriptor :=
  { pdfReference := "Generated finite BoolLanguage route; Section 2/4 hard side"
    informalClaim :=
      "A generated finite truth-table language may use the local hard-side route only \
       after Lean proof objects establish nonempty relations and all six hard-case \
       assumptions."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.GeneratedHardCaseCertificate"
    dependencies :=
      [ "ComplexityReduction.CSP.AllRelationsNonempty"
      , "ComplexityReduction.Schaefer.HardCaseAssumptions"
      , "ComplexityReduction.Schaefer.Hardness.hardRelationCertificateOfHardCase"
      , "ComplexityReduction.Schaefer.localSchaeferDichotomy_complete"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "If a generated language cannot provide the Lean proofs, the route reports \
       remaining_obligations and generated artifacts must stay upper-bound-only." }

end Schaefer
end ComplexityReduction
