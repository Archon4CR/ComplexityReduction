/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Schaefer.Tractable
import ComplexityReduction.Schaefer.EmptyRelations

/-!
Certificate-aware local Schaefer dichotomy aggregation.

The tractable side is fully aggregated over the six local condition names.  The
hard side now uses the local Section 3/4 witness theorem under the paper's
nonempty-relation precondition, and arbitrary languages are handled by the
empty-relation preprocessing wrapper.  The compatibility wrappers keep the
explicit `Targets.ThreeSATCompleteBoundary` parameter; the local final wrapper
uses the P14e discharged 3SAT completeness witness.
-/

namespace ComplexityReduction
namespace Schaefer

/-- All six locally implemented tractable-side statement wrappers. -/
theorem allTractableSideStatements (Γ : CSP.BoolLanguage) :
    ∀ condition : TractableConditionKind, tractableSideStatement Γ condition := by
  intro condition
  cases condition with
  | zeroValid => exact zeroValid_tractableSideStatement Γ
  | oneValid => exact oneValid_tractableSideStatement Γ
  | horn => exact horn_tractableSideStatement Γ
  | dualHorn => exact dualHorn_tractableSideStatement Γ
  | affine => exact affine_tractableSideStatement Γ
  | bijunctive => exact bijunctive_tractableSideStatement Γ

/-- Consumer-facing tractable branch: any of the six local tractable conditions puts `SAT(S)` in P. -/
theorem tractableLanguage_satS_inP {Γ : CSP.BoolLanguage}
    (hΓ : IsTractableLanguage Γ) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) := by
  rcases hΓ with ⟨condition, hCondition⟩
  exact (allTractableSideStatements Γ condition) hCondition

/-- Expanding the negation of the local tractable disjunction gives the named hard assumptions. -/
theorem not_tractable_to_hardAssumptions {Γ : CSP.BoolLanguage}
    (hNot : ¬ IsTractableLanguage Γ) :
    HardCaseAssumptions Γ where
  notZeroValid := by
    intro h
    exact hNot ⟨TractableConditionKind.zeroValid, h⟩
  notOneValid := by
    intro h
    exact hNot ⟨TractableConditionKind.oneValid, h⟩
  notHorn := by
    intro h
    exact hNot ⟨TractableConditionKind.horn, h⟩
  notDualHorn := by
    intro h
    exact hNot ⟨TractableConditionKind.dualHorn, h⟩
  notAffine := by
    intro h
    exact hNot ⟨TractableConditionKind.affine, h⟩
  notBijunctive := by
    intro h
    exact hNot ⟨TractableConditionKind.bijunctive, h⟩

/-- Hard certificate branch as a dichotomy result. -/
theorem hardCertificate_dichotomyBranch {Γ : CSP.BoolLanguage}
    (cert : Hardness.HardRelationCertificate Γ)
    (B : Targets.ThreeSATCompleteBoundary) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) ∨
      NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem Γ) :=
  Or.inr (Hardness.hardCertificate_satS_npComplete_fromBoundary cert B)

/--
Hard-language branch once a local classification step supplies a hard
certificate from the named hard assumptions.
-/
theorem hardLanguage_satS_npComplete_fromBoundary {Γ : CSP.BoolLanguage}
    (toCert : HardCaseAssumptions Γ → Hardness.HardRelationCertificate Γ)
    (hHard : HardCaseAssumptions Γ) (B : Targets.ThreeSATCompleteBoundary) :
    NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem Γ) :=
  Hardness.hardCertificate_satS_npComplete_fromBoundary (toCert hHard) B

/--
Final local statement wrapper, parameterized by the still-missing full hard-side
theorem.
-/
theorem localDichotomyStatement_proved {Γ : CSP.BoolLanguage}
    (hardRoute : hardSideStatement Γ) :
    localDichotomyStatement Γ :=
  ⟨allTractableSideStatements Γ, hardRoute⟩

/--
Boundary-explicit dichotomy once the missing hard-classification-to-certificate
route is supplied.
-/
theorem localSchaeferDichotomy_fromBoundary {Γ : CSP.BoolLanguage}
    (toCert : HardCaseAssumptions Γ → Hardness.HardRelationCertificate Γ)
    (B : Targets.ThreeSATCompleteBoundary) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) ∨
      NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem Γ) := by
  classical
  by_cases hTractable : IsTractableLanguage Γ
  · exact Or.inl (tractableLanguage_satS_inP hTractable)
  · exact Or.inr
      (hardLanguage_satS_npComplete_fromBoundary toCert
        (not_tractable_to_hardAssumptions hTractable) B)

/--
Boundary-explicit local Schaefer dichotomy for languages satisfying the
nonempty-relation precondition used in the paper's Section 4 proof.
-/
theorem localSchaeferDichotomy_nonempty_fromBoundary {Γ : CSP.BoolLanguage}
    (hNonempty : Hardness.AllRelationsNonempty Γ)
    (B : Targets.ThreeSATCompleteBoundary) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) ∨
      NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem Γ) :=
  localSchaeferDichotomy_fromBoundary
    (Hardness.hardRelationCertificateOfHardCase hNonempty) B

/--
Final local Schaefer dichotomy wrapper, excluding only the internal
Cook-Levin/3SAT-completeness proof.  Empty relation symbols are eliminated by
restricting to the nonempty sublanguage before applying the nonempty hard-side
theorem.
-/
theorem localSchaeferDichotomy_completeExceptCookLevin
    (Γ : CSP.BoolLanguage) (B : Targets.ThreeSATCompleteBoundary) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) ∨
      NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem Γ) := by
  exact satS_dichotomy_of_nonemptySubLanguage_dichotomy
    (localSchaeferDichotomy_nonempty_fromBoundary
      (nonemptySubLanguage_allRelationsNonempty Γ) B)
    B

/-- Final local Schaefer dichotomy wrapper using the discharged P14e 3SAT theorem. -/
theorem localSchaeferDichotomy_complete
    (Γ : CSP.BoolLanguage) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) ∨
      NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem Γ) :=
  localSchaeferDichotomy_completeExceptCookLevin Γ Targets.localThreeSATCompleteBoundary

/-- Local statement wrapper discharged for nonempty languages by the P8k hard theorem. -/
theorem localDichotomyStatement_nonempty_proved {Γ : CSP.BoolLanguage}
    (hNonempty : Hardness.AllRelationsNonempty Γ) :
    localDichotomyStatement Γ :=
  localDichotomyStatement_proved (Hardness.hardSideStatement_ofHardCase hNonempty)

/-- Descriptor for the complete local tractable aggregation. -/
def allTractableSideDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1 tractable side"
    informalClaim :=
      "The six local Schaefer tractable conditions dispatch to local InP theorem wrappers."
    localTargetSymbol := "ComplexityReduction.Schaefer.allTractableSideStatements"
    dependencies :=
      [ "ComplexityReduction.Schaefer.zeroValid_tractableSideStatement"
      , "ComplexityReduction.Schaefer.oneValid_tractableSideStatement"
      , "ComplexityReduction.Schaefer.horn_tractableSideStatement"
      , "ComplexityReduction.Schaefer.dualHorn_tractableSideStatement"
      , "ComplexityReduction.Schaefer.affine_tractableSideStatement"
      , "ComplexityReduction.Schaefer.bijunctive_tractableSideStatement"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes := "This descriptor covers only the tractable side." }

/-- Descriptor for the certificate-aware final wrapper. -/
def certificateAwareDichotomyDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1"
    informalClaim :=
      "Local dichotomy aggregation with the 3SAT completeness boundary explicit and \
       the hard classification supplied as a certificate builder."
    localTargetSymbol := "ComplexityReduction.Schaefer.localSchaeferDichotomy_fromBoundary"
    dependencies :=
      [ "ComplexityReduction.Schaefer.allTractableSideStatements"
      , "ComplexityReduction.Schaefer.not_tractable_to_hardAssumptions"
      , "ComplexityReduction.Schaefer.Hardness.HardRelationCertificate"
      , "ComplexityReduction.Schaefer.Hardness.hardCertificate_satS_npComplete_fromBoundary"
      , "ComplexityReduction.Targets.ThreeSATCompleteBoundary"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "The theorem is parameterized by HardCaseAssumptions Γ -> HardRelationCertificate Γ. \
       The unparameterized full hard classification remains missing." }

/-- Descriptor for the nonempty-language final wrapper. -/
def nonemptyLocalDichotomyDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1; Section 4 proof"
    informalClaim :=
      "For languages whose relations are all nonempty, the six tractable cases and the \
       locally proved Section 3/4 hard-side theorem give the Schaefer dichotomy.  \
       The compatibility theorem keeps 3SAT completeness as an explicit parameter."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.localSchaeferDichotomy_nonempty_fromBoundary"
    dependencies :=
      [ "ComplexityReduction.Schaefer.allTractableSideStatements"
      , "ComplexityReduction.Schaefer.not_tractable_to_hardAssumptions"
      , "ComplexityReduction.Schaefer.Hardness.hardRelationCertificateOfHardCase"
      , "ComplexityReduction.Schaefer.Hardness.AllRelationsNonempty"
      , "ComplexityReduction.Targets.ThreeSATCompleteBoundary"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "This is the paper's hard-side route under the explicit nonempty-relation \
       precondition; the local final wrapper uses the P14e Cook-Levin discharge." }

/-- Descriptor for the complete local wrapper with the P14e Cook-Levin discharge. -/
def completeExceptCookLevinDichotomyDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1; Section 4 proof"
    informalClaim :=
      "Arbitrary finite Boolean languages are handled by deleting empty relation symbols, \
       scanning empty constraints, and applying the nonempty local Schaefer dichotomy to \
       the resulting sublanguage."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.localSchaeferDichotomy_complete"
    dependencies :=
      [ "ComplexityReduction.Schaefer.emptyRelationWrapperDescriptor"
      , "ComplexityReduction.Schaefer.localSchaeferDichotomy_nonempty_fromBoundary"
      , "ComplexityReduction.Schaefer.nonemptySubLanguage_allRelationsNonempty"
      , "ComplexityReduction.Targets.localThreeSATCompleteBoundary"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "This is the local final dichotomy artifact available in this repository. \
       3SAT completeness is discharged by SAT.localCookLevinTheorem." }

end Schaefer
end ComplexityReduction
