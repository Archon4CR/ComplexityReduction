/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.SAT.ThreeSAT
import ComplexityReduction.Targets.ThreeSATCompleteBoundary
import ComplexityReduction.Schaefer.Problem

/-!
Statement skeleton for the local Schaefer dichotomy route.

This file records the theorem shapes the project intends to prove locally.  It
does not assert the dichotomy, import the external Schaefer project, or introduce
any new trusted boundary.
-/

namespace ComplexityReduction
namespace Schaefer

/-- Gap-map status values shared by Lean descriptors and markdown planning. -/
inductive ProofStatus where
  | done
  | skeleton
  | missingProof
  | externalOnly
  deriving DecidableEq, Repr

namespace ProofStatus

/-- Stable status spelling for manifests and gap maps. -/
def asString : ProofStatus → String
  | done => "done"
  | skeleton => "skeleton"
  | missingProof => "missing-proof"
  | externalOnly => "external-only"

end ProofStatus

/-- A tractable-side certificate shape for one Schaefer condition. -/
structure TractableSideCertificate
    (Γ : CSP.BoolLanguage) (condition : TractableConditionKind) where
  conditionHolds : LanguageSatisfies condition Γ
  inP : InP CostedPolyTimeModel (satSDecisionProblem Γ)

/-- A hard-side local certificate shape before applying the 3SAT completeness boundary. -/
structure HardSideReductionCertificate (Γ : CSP.BoolLanguage) where
  assumptions : HardCaseAssumptions Γ
  reduction :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem (satSDecisionProblem Γ)
  membership : InNPEnc CostedPolyTimeModel (satSDecisionProblem Γ)

/-- Target proposition for one local tractable Schaefer case. -/
def tractableSideStatement (Γ : CSP.BoolLanguage) (condition : TractableConditionKind) :
    Prop :=
  LanguageSatisfies condition Γ → InP CostedPolyTimeModel (satSDecisionProblem Γ)

/-- Target proposition for the local hard side, conditional on local 3SAT completeness. -/
def hardSideStatement (Γ : CSP.BoolLanguage) : Prop :=
  HardCaseAssumptions Γ →
    Targets.ThreeSATCompleteBoundary →
      NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem Γ)

/-- Target proposition for this repository's final Schaefer dichotomy wrapper. -/
def localDichotomyStatement (Γ : CSP.BoolLanguage) : Prop :=
  (∀ condition : TractableConditionKind, tractableSideStatement Γ condition) ∧
    hardSideStatement Γ

/-- One row in the local Schaefer theorem target inventory. -/
structure StatementDescriptor where
  pdfReference : String
  informalClaim : String
  localTargetSymbol : String
  dependencies : List String
  status : ProofStatus
  externalSymbols : List String
  notes : String
  deriving Repr

/-- Descriptor for the local Section 3/4 typed hard-base witness theorem. -/
def localRepAllStatement : StatementDescriptor :=
  { pdfReference := "Section 3, Theorem 3.0"
    informalClaim :=
      "If the Schaefer hard-case assumptions hold, the local typed Section 3/4 route \
       produces a proof-bearing hard-base representation witness under the paper's \
       nonempty-relation precondition."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.Hardness.hardBaseRepresentationWitnessOfHardCase"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Hardness.Section34ClassificationWitness"
      , "ComplexityReduction.Schaefer.Hardness.hardBaseRepresentationWitnessWithConstantsOfHardCase"
      , "ComplexityReduction.Schaefer.Hardness.repNAEWitnessOfComplementiveHardCase"
      ]
    status := ProofStatus.done
    externalSymbols := [ "SchaeferDichotomy.classification_theorem" ]
    notes :=
      "The repository does not expose a literal Rep(S)=all-relations theorem; it proves the \
       typed witness needed by the local hard route." }

/-- Descriptor for the local with-constants hard-side theorem. -/
def localSatWithConstantsHardnessStatement : StatementDescriptor :=
  { pdfReference := "Section 4, Lemma 4.1"
    informalClaim := "Hard-base representation witness for the local SAT-with-constants language."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.Hardness.hardBaseRepresentationWitnessWithConstantsOfHardCase"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Hardness.satCWithConstantsLanguage"
      , "ComplexityReduction.Schaefer.Hardness.repOneInThreeWitnessWithConstantsOfHardCase"
      ]
    status := ProofStatus.done
    externalSymbols := [ "SchaeferDichotomy.schaefer_hardness_with_constants" ]
    notes := "Local proof is expressed as a hard-base witness, then routed through certificates." }

/-- Descriptor for the local constants-to-no-constants equivalence lemma. -/
def localSatCToSatWhenConstantsRepresentable : StatementDescriptor :=
  { pdfReference := "Section 4, Lemma 4.2"
    informalClaim :=
      "If unary constants are representable without constants, SATc(S) and SAT(S) have the same complexity."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.Hardness.satCToSatWhenConstantsRepresentable"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Hardness.ConstantRepresentationWitness"
      , "ComplexityReduction.Schaefer.Hardness.satCWithConstantsLanguageRepresentation"
      , "ComplexityReduction.Schaefer.Hardness.representationReductionCertificateOfLanguageRepresentationAuto"
      ]
    status := ProofStatus.done
    externalSymbols :=
      [ "SchaeferDichotomy.satCToSat_reduction"
      , "SchaeferDichotomy.satCToSat_log_reduction"
      ]
    notes := "Local theorem is costed via the generic proof-bearing representation route." }

/-- Descriptor for the local Lemma 4.3 case split. -/
def localLemma43ConstantElimWitness : StatementDescriptor :=
  { pdfReference := "Section 4, Lemma 4.3"
    informalClaim :=
      "No-constants case split: zero/one failures yield constants or complementive structure."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.Hardness.constantOrComplementiveWitnessOfHardCase"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Hardness.AllRelationsNonempty"
      , "ComplexityReduction.Schaefer.Hardness.constantOrXorWitnessOfHardCase"
      , "ComplexityReduction.Schaefer.Hardness.repNAEWitnessOfComplementiveHardCase"
      ]
    status := ProofStatus.done
    externalSymbols := [ "SchaeferDichotomy.constantElimWitnessOfLemma43" ]
    notes := "The theorem keeps the PDF's nonempty-relation precondition explicit." }

/-- Descriptor grouping the local no-constants constant-elimination route. -/
def localConstantEliminationStatement : StatementDescriptor :=
  { pdfReference := "Section 4, Lemmas 4.2 and 4.3"
    informalClaim := "Eliminate constants for the no-constants SAT(S) theorem."
    localTargetSymbol := "ComplexityReduction.Schaefer.Hardness.section34WitnessOfHardCase"
    dependencies :=
      [ "ComplexityReduction.Schaefer.localSatCToSatWhenConstantsRepresentable"
      , "ComplexityReduction.Schaefer.localLemma43ConstantElimWitness"
      ]
    status := ProofStatus.done
    externalSymbols :=
      [ "SchaeferDichotomy.constantElimWitnessOfLemma43"
      , "SchaeferDichotomy.satCToSat_log_reduction"
      ]
    notes := "Combined route produces the typed Section 3/4 witness used by the hard side." }

/-- Descriptor for removing empty-relation symbols before applying the nonempty hard theorem. -/
def localEmptyRelationWrapperStatement : StatementDescriptor :=
  { pdfReference := "Section 4, proof of Theorem 2.1; Lemma 4.3 nonempty note"
    informalClaim :=
      "A formula containing an empty-relation constraint is unsatisfiable; otherwise it \
       restricts to the sublanguage of nonempty relations."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.satS_dichotomy_of_nonemptySubLanguage_dichotomy"
    dependencies :=
      [ "ComplexityReduction.Schaefer.formula_unsat_of_containsEmptyRelation"
      , "ComplexityReduction.Schaefer.restrictFormulaNoEmpty_satisfiable_iff"
      , "ComplexityReduction.Schaefer.nonemptySubLanguageToOriginalKarpReduction"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes := "This wrapper is local and does not introduce a new trusted boundary." }

/-- Descriptor for the final local wrapper using the P14e Cook-Levin discharge. -/
def localCompleteExceptCookLevinStatement : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1"
    informalClaim :=
      "Local Schaefer dichotomy for arbitrary finite Boolean languages, with local \
       3SAT completeness supplied by `Targets.localThreeSATCompleteBoundary`."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.localSchaeferDichotomy_complete"
    dependencies :=
      [ "ComplexityReduction.Schaefer.localSchaeferDichotomy_nonempty_fromBoundary"
      , "ComplexityReduction.Schaefer.satS_dichotomy_of_nonemptySubLanguage_dichotomy"
      , "ComplexityReduction.Targets.localThreeSATCompleteBoundary"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes := "Cook-Levin is discharged for the local InNPEnc class by SAT.localCookLevinTheorem." }

/-- Local theorem targets extracted for P8a. -/
def localStatementInventory : List StatementDescriptor :=
  [ { pdfReference := "Section 2, Theorem 2.1"
      informalClaim := "Schaefer dichotomy for finite SAT(S)."
      localTargetSymbol :=
        "ComplexityReduction.Schaefer.localSchaeferDichotomy_complete"
      dependencies :=
        [ "ComplexityReduction.Schaefer.tractableSideStatement"
        , "ComplexityReduction.Schaefer.hardSideStatement"
        , "ComplexityReduction.Targets.localThreeSATCompleteBoundary"
        ]
      status := ProofStatus.done
      externalSymbols :=
        [ "SchaeferDichotomy.schaefer_hardness_no_constants_log_nonempty_failure_witnesses_internal"
        ]
      notes := "Local final wrapper uses `Targets.localThreeSATCompleteBoundary`." }
  , { pdfReference := "Section 2, definitions after Theorem 2.1"
      informalClaim := "Six tractable relation-family conditions."
      localTargetSymbol := "ComplexityReduction.Schaefer.TractableConditionKind"
      dependencies :=
        [ "ComplexityReduction.Schaefer.IsZeroValid"
        , "ComplexityReduction.Schaefer.IsOneValid"
        , "ComplexityReduction.Schaefer.IsHorn"
        , "ComplexityReduction.Schaefer.IsDualHorn"
        , "ComplexityReduction.Schaefer.IsAffine"
        , "ComplexityReduction.Schaefer.IsBijunctive"
        ]
      status := ProofStatus.done
      externalSymbols := [ "SchaeferDichotomy.LogRel" ]
      notes := "Predicates are local over CSP.BoolRel and are connected to local tractable wrappers." }
  , localRepAllStatement
  , localSatWithConstantsHardnessStatement
  , localConstantEliminationStatement
  , localEmptyRelationWrapperStatement
  , localCompleteExceptCookLevinStatement
  , { pdfReference := "Section 4, proof of Theorem 2.1"
      informalClaim := "Hard side of no-constants SAT(S), conditional on 3SAT completeness."
      localTargetSymbol := "ComplexityReduction.Schaefer.Hardness.hardSideStatement_ofHardCase"
      dependencies :=
        [ "localRepAllStatement"
        , "localConstantEliminationStatement"
        , "KarpReductionM CostedPolyTimeModel 3SAT SAT(S)"
        , "InNPEnc CostedPolyTimeModel SAT(S)"
        , "Targets.localThreeSATCompleteBoundary"
        ]
      status := ProofStatus.done
      externalSymbols :=
        [ "SchaeferDichotomy.schaefer_hardness_no_constants_log_nonempty_failure_witnesses_internal"
        , "SchaeferDichotomy.threeSAT_logCompleteInNP"
        ]
      notes := "Hard side is local under the nonempty-relation precondition; empty relations are handled by the P9 wrapper. Cook-Levin is discharged by SAT.localCookLevinTheorem." }
  ]

theorem localStatementInventory_nonempty :
    localStatementInventory.length = 8 :=
  rfl

end Schaefer
end ComplexityReduction
