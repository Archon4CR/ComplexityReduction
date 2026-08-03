/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Targets.ThreeSAT
import ComplexityReduction.Targets.ThreeSATCompleteBoundary
import ComplexityReduction.Targets.Schaefer

/-!
Initial target catalog for NP-complete destinations.

This catalog is small but concrete so that the standalone reduction library can
name a target theorem and a target problem term without depending on project-local
wrapper namespace.
-/

namespace ComplexityReduction
namespace Targets

/-- Tool-visible reference metadata for an NPC target. -/
structure NPCTargetDescriptor where
  name : String
  problemSymbol : String
  completenessSymbol : String
  foundation : String
  bridgeKind : String
  requiresExplicitOptIn : Bool
  artifactEligibleByDefault : Bool
  transportTheorem : Option String
  remainingBoundaries : List String
  trustedBoundary : String
  notes : String
  deriving Repr

/-- Tool-visible reference metadata for Schaefer hard-route artifact generation. -/
structure SchaeferHardRouteDescriptor where
  routeKind : String
  hardRouteSymbol : String
  emptyRelationPolicy : String
  requiresEmptyRelationWrapper : Bool
  requiresHardCaseAssumptions : Bool
  requiresThreeSATBoundary : Bool
  generatedCertificateAPI : Option String
  remainingObligationsAPI : Option String
  externalBoundarySymbol : Option String
  artifactEligibleByDefault : Bool
  notes : String
  deriving Repr

/-- The local 3SAT target entry. -/
def threeSATTarget : NPCTargetDescriptor :=
  { name := "3SAT"
    problemSymbol := "ComplexityReduction.Targets.threeSATDecisionProblem"
    completenessSymbol := "ComplexityReduction.SAT.localCookLevinTheorem"
    foundation := "ComplexityReduction.Core.NPClass + ComplexityReduction.SAT.ThreeSAT"
    bridgeKind := "local_discharged"
    requiresExplicitOptIn := false
    artifactEligibleByDefault := true
    transportTheorem := some "ComplexityReduction.Targets.localThreeSATCompleteBoundary"
    remainingBoundaries := []
    trustedBoundary :=
      "No trusted boundary is needed for the local class: P14e makes direct InNPEnc \
       leaves carry a local Cook-Levin map to 3SAT."
    notes := "This target is ready for local CSP reductions and boundary-free local NPC transfer." }

/-- Local targets available to generated artifacts by default. -/
def localTargets : List NPCTargetDescriptor :=
  [threeSATTarget]

/-- Local final Schaefer wrapper route for arbitrary finite Boolean languages. -/
def schaeferLocalFinalRoute : SchaeferHardRouteDescriptor :=
  { routeKind := "local_final"
    hardRouteSymbol :=
      "ComplexityReduction.Schaefer.localSchaeferDichotomy_complete"
    emptyRelationPolicy := "eliminate"
    requiresEmptyRelationWrapper := true
    requiresHardCaseAssumptions := false
    requiresThreeSATBoundary := false
    generatedCertificateAPI :=
      some "ComplexityReduction.Schaefer.GeneratedHardCaseCertificate"
    remainingObligationsAPI :=
      some "ComplexityReduction.Schaefer.GeneratedHardCaseRoute.remainingObligations"
    externalBoundarySymbol := none
    artifactEligibleByDefault := true
    notes :=
      "Produces the local Schaefer dichotomy branch for a fixed language using the \
       discharged P14e 3SAT completeness theorem." }

/-- Local nonempty hard-side route when hard-case proof objects are supplied. -/
def schaeferLocalNonemptyHardRoute : SchaeferHardRouteDescriptor :=
  { routeKind := "local_nonempty"
    hardRouteSymbol :=
      "ComplexityReduction.Schaefer.Hardness.hardRelationCertificateOfHardCase"
    emptyRelationPolicy := "require_nonempty"
    requiresEmptyRelationWrapper := false
    requiresHardCaseAssumptions := true
    requiresThreeSATBoundary := false
    generatedCertificateAPI :=
      some "ComplexityReduction.Schaefer.GeneratedHardCaseCertificate"
    remainingObligationsAPI :=
      some "ComplexityReduction.Schaefer.GeneratedHardCaseRoute.remainingObligations"
    externalBoundarySymbol := none
    artifactEligibleByDefault := false
    notes :=
      "Produces an NP-completeness theorem only when Lean proof objects provide \
       AllRelationsNonempty and HardCaseAssumptions, or a generated hard certificate; \
       local 3SAT completeness is discharged by P14e." }

/-- External Schaefer route remains an audit-only bridge until transport exists. -/
def schaeferExternalAuditRoute : SchaeferHardRouteDescriptor :=
  { routeKind := "external"
    hardRouteSymbol := "SchaeferDichotomy.*"
    emptyRelationPolicy := "reject"
    requiresEmptyRelationWrapper := false
    requiresHardCaseAssumptions := false
    requiresThreeSATBoundary := false
    generatedCertificateAPI := none
    remainingObligationsAPI := none
    externalBoundarySymbol :=
      some "ComplexityReduction.Targets.Schaefer.auditOnlyTrustedBoundary"
    artifactEligibleByDefault := false
    notes :=
      "External symbols are metadata only without an explicit local transport theorem \
       or manifest-recorded trusted external boundary." }

/-- Schaefer hard routes visible to the generator and audit gate. -/
def schaeferHardRoutes : List SchaeferHardRouteDescriptor :=
  [schaeferLocalFinalRoute, schaeferLocalNonemptyHardRoute, schaeferExternalAuditRoute]

theorem schaeferHardRoutes_length :
    schaeferHardRoutes.length = 3 :=
  rfl

/-- Audit-only external Schaefer encoded-3SAT target descriptor. -/
def schaeferThreeSATEncodedTarget : NPCTargetDescriptor :=
  { name := "external Schaefer encoded 3SAT"
    problemSymbol := "SchaeferDichotomy.threeSAT_encoded"
    completenessSymbol := "SchaeferDichotomy.threeSAT_logCompleteInNP"
    foundation :=
      "SchaeferDichotomy.Foundation.EncodedDecisionProblem and \
       SchaeferDichotomy.Foundation.LogSpace"
    bridgeKind := Schaefer.ExternalBridgeKind.trustedBoundary.asString
    requiresExplicitOptIn := true
    artifactEligibleByDefault := false
    transportTheorem := none
    remainingBoundaries :=
      [ "No local transport theorem from SchaeferDichotomy.EncodedDecisionProblem \
          to ComplexityReduction.EncodedDecisionProblem is registered."
      , "SchaeferDichotomy.threeSAT_logCompleteInNP is an external Cook-Levin/3SAT \
          completeness axiom."
      ]
    trustedBoundary :=
      "The sibling project cannot be mounted as a Lake dependency here because it also \
       exports a ComplexityReduction library.  This entry is metadata until an explicit \
       transport theorem or trusted boundary is supplied."
    notes :=
      "Audited in SCHAEFER_BRIDGE_AUDIT.md; natural-language reference is \
       reference/800133.804350.pdf." }

/-- Audit-only external Schaefer no-constant SAT(S) target descriptor. -/
def schaeferNSATTarget : NPCTargetDescriptor :=
  { name := "external Schaefer NSAT(S)"
    problemSymbol := "SchaeferDichotomy.NSAT_S_encoded S"
    completenessSymbol :=
      "SchaeferDichotomy.schaefer_hardness_no_constants_log_nonempty_relations_internal"
    foundation :=
      "SchaeferDichotomy.Foundation.EncodedDecisionProblem, NSFormula, and \
       external LogCompleteInNP"
    bridgeKind := Schaefer.ExternalBridgeKind.trustedBoundary.asString
    requiresExplicitOptIn := true
    artifactEligibleByDefault := false
    transportTheorem := none
    remainingBoundaries :=
      [ "No local transport theorem from SchaeferDichotomy.BundledLogRel / NSFormula \
          to ComplexityReduction.CSP.BoolLanguage is registered."
      , "External Schaefer hardness theorem depends on the external \
          threeSAT_logCompleteInNP boundary and native_decide proof byproducts."
      ]
    trustedBoundary :=
      "This is a discoverable external bridge target only.  Generated artifacts must not \
       use it as a local NP-complete target without manifest-recorded external boundary \
       and transport data."
    notes :=
      "The first local use should be an explicit transport theorem or a generated artifact \
       whose remaining_boundaries name the external foundation." }

/-- External Schaefer bridge targets that are discoverable but not usable by default. -/
def schaeferBridgeTargets : List NPCTargetDescriptor :=
  [schaeferThreeSATEncodedTarget, schaeferNSATTarget]

/-- Current default catalog used by local generated artifacts. -/
def initialTargets : List NPCTargetDescriptor :=
  localTargets

/-- Extended catalog for tools that explicitly opt into external bridge discovery. -/
def targetsWithExternalBridges : List NPCTargetDescriptor :=
  localTargets ++ schaeferBridgeTargets

theorem localTargets_length :
    localTargets.length = 1 :=
  rfl

theorem schaeferBridgeTargets_length :
    schaeferBridgeTargets.length = 2 :=
  rfl

end Targets
end ComplexityReduction
