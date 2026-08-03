/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Core.EncodedDecisionProblem

/-!
Audit-only bridge metadata for the external Schaefer dichotomy project.

The sibling project `../schaefer_dichotomy_lean` also defines a Lean library
named `ComplexityReduction`, so this repository cannot safely import it as a
Lake dependency without module-name ambiguity.  This module therefore records
the exact external symbols and boundary policy as typed metadata only; it does
not transport theorems into this project's `EncodedDecisionProblem` foundation.
-/

namespace ComplexityReduction
namespace Targets
namespace Schaefer

/-- How an external theorem is connected to this repository's foundation. -/
inductive ExternalBridgeKind where
  | definitional
  | transported
  | trustedBoundary
  deriving DecidableEq, Repr

namespace ExternalBridgeKind

/-- Stable manifest string for an external bridge kind. -/
def asString : ExternalBridgeKind → String
  | definitional => "definitional"
  | transported => "transported"
  | trustedBoundary => "trusted_boundary"

end ExternalBridgeKind

/-- Metadata for a single audited symbol in the external Schaefer project. -/
structure ExternalSymbolDescriptor where
  sourceProject : String
  sourcePath : String
  sourceModule : String
  sourceSymbol : String
  statement : String
  foundation : String
  bridgeKind : ExternalBridgeKind
  localTransportTheorem : Option String
  axiomBoundary : List String
  naturalLanguageReference : Option String
  notes : String
  deriving Repr

/-- The sibling project audited by P7. -/
def sourceProjectRoot : String :=
  "../schaefer_dichotomy_lean"

/-- Natural-language proof reference under this repository's `reference/` directory. -/
def naturalLanguageReference : String :=
  "reference/800133.804350.pdf"

/-- External encoded 3SAT problem in the Schaefer foundation. -/
def threeSATEncodedSymbol : ExternalSymbolDescriptor :=
  { sourceProject := sourceProjectRoot
    sourcePath := "SchaeferDichotomy/Hardness/StrictComplexity.lean"
    sourceModule := "SchaeferDichotomy.Hardness.StrictComplexity"
    sourceSymbol := "SchaeferDichotomy.threeSAT_encoded"
    statement :=
      "SchaeferDichotomy.threeSAT_encoded : \
       SchaeferDichotomy.EncodedDecisionProblem"
    foundation :=
      "SchaeferDichotomy.Foundation.EncodedDecisionProblem; not definitional-equal \
       to this repository's ComplexityReduction.EncodedDecisionProblem."
    bridgeKind := ExternalBridgeKind.trustedBoundary
    localTransportTheorem := none
    axiomBoundary := []
    naturalLanguageReference := some naturalLanguageReference
    notes :=
      "External definition audited for symbol/type only.  A local artifact must \
       use an explicit transport theorem before treating this as the local 3SAT target." }

/-- External no-constant SAT(S) encoded problem in the Schaefer foundation. -/
def nsatSEncodedSymbol : ExternalSymbolDescriptor :=
  { sourceProject := sourceProjectRoot
    sourcePath := "SchaeferDichotomy/Hardness/StrictComplexity.lean"
    sourceModule := "SchaeferDichotomy.Hardness.StrictComplexity"
    sourceSymbol := "SchaeferDichotomy.NSAT_S_encoded"
    statement :=
      "SchaeferDichotomy.NSAT_S_encoded \
       (S : Finset SchaeferDichotomy.BundledLogRel) : \
       SchaeferDichotomy.EncodedDecisionProblem"
    foundation :=
      "SchaeferDichotomy.Foundation.EncodedDecisionProblem and \
       SchaeferDichotomy.SAT.NSFormula encodings."
    bridgeKind := ExternalBridgeKind.trustedBoundary
    localTransportTheorem := none
    axiomBoundary := []
    naturalLanguageReference := some naturalLanguageReference
    notes :=
      "External target family is parameterized by SchaeferDichotomy.BundledLogRel; \
       no local BoolLanguage transport is available yet." }

/-- External table-backed certificate for SAT3-to-SAT_C(S). -/
def strictClauseEncodingTableSymbol : ExternalSymbolDescriptor :=
  { sourceProject := sourceProjectRoot
    sourcePath := "SchaeferDichotomy/Hardness/StrictComplexity.lean"
    sourceModule := "SchaeferDichotomy.Hardness.StrictComplexity"
    sourceSymbol := "SchaeferDichotomy.StrictClauseEncodingTable"
    statement :=
      "SchaeferDichotomy.StrictClauseEncodingTable \
       (S : Finset SchaeferDichotomy.BundledLogRel) : Type"
    foundation :=
      "SchaeferDichotomy.ClauseEncodingTable, CostedMap, BSFormula, and \
       project-local LogSpaceMap."
    bridgeKind := ExternalBridgeKind.trustedBoundary
    localTransportTheorem := none
    axiomBoundary := []
    naturalLanguageReference := some naturalLanguageReference
    notes :=
      "The external structure packages table and costed-map fields.  It is not \
       a local ComplexityReduction strict-machine certificate." }

/-- External strict log-space reduction from SAT3 to SAT_C(S). -/
def sat3ToSatCAlgLogReductionSymbol : ExternalSymbolDescriptor :=
  { sourceProject := sourceProjectRoot
    sourcePath := "SchaeferDichotomy/Hardness/StrictComplexity.lean"
    sourceModule := "SchaeferDichotomy.Hardness.StrictComplexity"
    sourceSymbol := "SchaeferDichotomy.sat3ToSatCAlg_log_reduction"
    statement :=
      "SchaeferDichotomy.sat3ToSatCAlg_log_reduction \
       {S : Finset SchaeferDichotomy.BundledLogRel} \
       (cert : SchaeferDichotomy.StrictClauseEncodingTable S) : \
       SchaeferDichotomy.LogReducible SchaeferDichotomy.threeSAT_encoded \
       (SchaeferDichotomy.BSAT_S_encoded S)"
    foundation :=
      "SchaeferDichotomy.LogReducible over SchaeferDichotomy.EncodedDecisionProblem."
    bridgeKind := ExternalBridgeKind.trustedBoundary
    localTransportTheorem := none
    axiomBoundary := []
    naturalLanguageReference := some naturalLanguageReference
    notes :=
      "External axiom scan reported only standard Lean axioms for this theorem. \
       It still cannot be used as a local reduction without transport." }

/-- External Cook-Levin/3SAT-completeness boundary in the Schaefer foundation. -/
def threeSATLogCompleteBoundarySymbol : ExternalSymbolDescriptor :=
  { sourceProject := sourceProjectRoot
    sourcePath := "SchaeferDichotomy/Hardness/StrictComplexity.lean"
    sourceModule := "SchaeferDichotomy.Hardness.StrictComplexity"
    sourceSymbol := "SchaeferDichotomy.threeSAT_logCompleteInNP"
    statement :=
      "SchaeferDichotomy.threeSAT_logCompleteInNP : \
       SchaeferDichotomy.LogCompleteInNP SchaeferDichotomy.threeSAT_encoded"
    foundation :=
      "SchaeferDichotomy.LogCompleteInNP over the external encoded-language layer."
    bridgeKind := ExternalBridgeKind.trustedBoundary
    localTransportTheorem := none
    axiomBoundary := ["SchaeferDichotomy.threeSAT_logCompleteInNP"]
    naturalLanguageReference := some naturalLanguageReference
    notes :=
      "This is an explicit external Cook-Levin/3SAT-completeness axiom and must \
       be recorded as a remaining boundary by any artifact that cites it." }

/-- Core external symbols audited for the first Schaefer bridge. -/
def externalCoreSymbols : List ExternalSymbolDescriptor :=
  [ threeSATEncodedSymbol
  , nsatSEncodedSymbol
  , strictClauseEncodingTableSymbol
  , sat3ToSatCAlgLogReductionSymbol
  , threeSATLogCompleteBoundarySymbol
  ]

theorem externalCoreSymbols_length :
    externalCoreSymbols.length = 5 :=
  rfl

/-- No local transport theorem is available in the P7 bridge. -/
def localTransportTheorems : List String :=
  []

theorem localTransportTheorems_empty :
    localTransportTheorems = [] :=
  rfl

/-- Generator policy for the first Schaefer bridge. -/
structure BridgePolicy where
  externalBridgeAllowedField : String
  transportTheoremField : String
  remainingBoundariesField : String
  defaultArtifactEligible : Bool
  generatorMayUseUnconditionally : Bool
  notes : String
  deriving Repr

/-- P7 policy: discoverable metadata, but no unconditional generated artifact. -/
def auditOnlyPolicy : BridgePolicy :=
  { externalBridgeAllowedField := "external_bridge_allowed"
    transportTheoremField := "transport_theorem"
    remainingBoundariesField := "remaining_boundaries"
    defaultArtifactEligible := false
    generatorMayUseUnconditionally := false
    notes :=
      "External Schaefer symbols are catalog metadata until a local transport theorem \
       or an explicit trusted boundary is present in the manifest." }

theorem auditOnlyPolicy_not_unconditional :
    auditOnlyPolicy.generatorMayUseUnconditionally = false :=
  rfl

/--
Typed boundary record for external Schaefer theorem use.

This is metadata, not a transported theorem.  A generated artifact may consume
this record only by recording the listed remaining boundaries in its manifest;
it still cannot treat the external symbols as local `ComplexityReduction`
theorems.
-/
structure TrustedExternalSchaeferBoundary where
  name : String
  externalSymbols : List ExternalSymbolDescriptor
  localFoundation : String
  externalFoundation : String
  transportTheorem : Option String
  remainingBoundaries : List String
  artifactEligible : Bool
  generatorMayUseAsLocalTheorem : Bool
  notes : String
  deriving Repr

/--
P10 audit decision: the sibling Schaefer project remains audit-only in this
repository because the two foundations are not definitionally equal and the Lake
module graph still has a `ComplexityReduction` library-name collision.
-/
def auditOnlyTrustedBoundary : TrustedExternalSchaeferBoundary :=
  { name := "external-schaefer-audit-only"
    externalSymbols := externalCoreSymbols
    localFoundation := "ComplexityReduction.EncodedDecisionProblem and CSP.BoolLanguage"
    externalFoundation :=
      "SchaeferDichotomy.Foundation.EncodedDecisionProblem and \
       SchaeferDichotomy.BundledLogRel"
    transportTheorem := none
    remainingBoundaries :=
      [ "No local transport theorem from the external encoded-problem foundation to \
         ComplexityReduction.EncodedDecisionProblem"
      , "External Cook-Levin/3SAT completeness is represented locally only by \
         Targets.ThreeSATCompleteBoundary"
      ]
    artifactEligible := false
    generatorMayUseAsLocalTheorem := false
    notes :=
      "Use local Schaefer theorems for generated artifacts.  External symbols remain \
       catalog/audit metadata until a transport theorem or an explicitly trusted \
       external-boundary route is added." }

theorem auditOnlyTrustedBoundary_no_transport :
    auditOnlyTrustedBoundary.transportTheorem = none :=
  rfl

theorem auditOnlyTrustedBoundary_not_artifactEligible :
    auditOnlyTrustedBoundary.artifactEligible = false :=
  rfl

theorem auditOnlyTrustedBoundary_not_local_theorem :
    auditOnlyTrustedBoundary.generatorMayUseAsLocalTheorem = false :=
  rfl

end Schaefer
end Targets
end ComplexityReduction
