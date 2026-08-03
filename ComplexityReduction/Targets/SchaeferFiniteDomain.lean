/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Targets.Schaefer
import ComplexityReduction.CSP.FiniteDomain
import ComplexityReduction.CSP.FiniteDomain.BooleanCloneCatalog

/-!
Planner catalog for Boolean/Schaefer routes that interact with finite-domain CSP.

This file separates routes with local Lean theorems from external metadata and
currently blocked transport paths.  The planner can therefore choose a local
finite-domain bridge when one exists and decline unsupported external transport.
-/

namespace ComplexityReduction
namespace Targets

/-- Trust/use status for a Schaefer-to-finite-domain route. -/
inductive SchaeferFiniteDomainStatus where
  | localTheorem
  | metadataOnly
  | blocked
  deriving DecidableEq, Repr

namespace SchaeferFiniteDomainStatus

def asString : SchaeferFiniteDomainStatus → String
  | localTheorem => "local_theorem"
  | metadataOnly => "metadata_only"
  | blocked => "blocked"

end SchaeferFiniteDomainStatus

/-- Planner metadata for Schaefer/Boolean finite-domain transport. -/
structure SchaeferFiniteDomainRouteDescriptor where
  name : String
  status : SchaeferFiniteDomainStatus
  sourceSymbol : String
  targetSymbol : String
  mapSymbol : Option String
  localTheorem : Option String
  requiredTransport : List String
  generatorMayUseAsTheorem : Bool
  roles : List String
  notes : List String
  deriving Repr

/-- Local Boolean CSP to `Fin 2` finite-domain CSP transport. -/
def boolCSPToFin2Route : SchaeferFiniteDomainRouteDescriptor :=
  { name := "bool_csp_to_fin2_finite_domain"
    status := SchaeferFiniteDomainStatus.localTheorem
    sourceSymbol := "ComplexityReduction.CSP.BoolLanguage"
    targetSymbol := "ComplexityReduction.CSP.FiniteDomain.Language (Fin 2)"
    mapSymbol := some "ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaFin2OfBoolFormula"
    localTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaFin2OfBoolFormula_satisfiable_iff"
    requiredTransport := []
    generatorMayUseAsTheorem := true
    roles := ["schaefer", "bool_csp", "finite_domain_csp", "local_theorem"]
    notes := ["Preferred local bridge from Boolean CSP formulas to finite-domain CSP over `Fin 2`."] }

/-- Local Boolean CSP to finite-domain CSP over `Bool`. -/
def boolCSPToBoolDomainRoute : SchaeferFiniteDomainRouteDescriptor :=
  { name := "bool_csp_to_bool_finite_domain"
    status := SchaeferFiniteDomainStatus.localTheorem
    sourceSymbol := "ComplexityReduction.CSP.BoolLanguage"
    targetSymbol := "ComplexityReduction.CSP.FiniteDomain.Language Bool"
    mapSymbol := some "ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula"
    localTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula_satisfiable_iff"
    requiredTransport := []
    generatorMayUseAsTheorem := true
    roles := ["schaefer", "bool_csp", "finite_domain_csp", "local_theorem"]
    notes := ["Local bridge when the target domain is literally `Bool`."] }

/-- Local Schaefer hard-side route remains Boolean before optional finite-domain transport. -/
def localSchaeferThenFiniteDomainRoute : SchaeferFiniteDomainRouteDescriptor :=
  { name := "local_schaefer_then_finite_domain_bridge"
    status := SchaeferFiniteDomainStatus.localTheorem
    sourceSymbol := "ComplexityReduction.Schaefer.satSDecisionProblem"
    targetSymbol := "ComplexityReduction.CSP.FiniteDomain.cspDecisionProblem"
    mapSymbol := none
    localTheorem := some "ComplexityReduction.Schaefer.localSchaeferDichotomy_complete"
    requiredTransport :=
      [ "Use `BoolBridge.formulaOfBoolFormula_satisfiable_iff` or \
         `BoolBridge.formulaFin2OfBoolFormula_satisfiable_iff` after selecting a Boolean language."
      , "If the route starts from a Boolean pp representation, use \
         `BoolPPTransport.formulaViaFin2BoolPPTransport_satisfiable_iff`." ]
    generatorMayUseAsTheorem := true
    roles := ["schaefer", "local_theorem", "finite_domain_followup"]
    notes :=
      [ "The Schaefer branch itself is local."
      , "Finite-domain conversion is a separate formula transport step through `BoolBridge` or `BoolPPTransport`." ] }

/-- Boolean clone/co-clone catalog route metadata for planner-side class selection. -/
def booleanCloneCatalogRoute : SchaeferFiniteDomainRouteDescriptor :=
  { name := "boolean_clone_catalog_metadata"
    status := SchaeferFiniteDomainStatus.metadataOnly
    sourceSymbol :=
      "ComplexityReduction.CSP.FiniteDomain.BooleanCloneCatalog.BooleanCloneDescriptor"
    targetSymbol := "ComplexityReduction.CSP.FiniteDomain.PreservesLanguage"
    mapSymbol := none
    localTheorem := none
    requiredTransport :=
      [ "Use the descriptor's `languageTransportTheorem` only when it is present."
      , "Metadata-only refinements such as definite Horn and width-2 affine require a separate local theorem before generated proofs may cite them." ]
    generatorMayUseAsTheorem := false
    roles := ["schaefer", "boolean_clone", "co_clone", "metadata_only"]
    notes :=
      [ "Indexes Schnoor-Schnoor/Post-lattice vocabulary without asserting lattice completeness."
      , "The theorem-usable entries point back to local Boolean polymorphism transport lemmas." ] }

/-- External Schaefer symbols are discoverable metadata here, not local theorem inputs. -/
def externalSchaeferMetadataRoute : SchaeferFiniteDomainRouteDescriptor :=
  { name := "external_schaefer_metadata_only"
    status := SchaeferFiniteDomainStatus.metadataOnly
    sourceSymbol := "SchaeferDichotomy.*"
    targetSymbol := "ComplexityReduction.CSP.FiniteDomain.cspDecisionProblem"
    mapSymbol := none
    localTheorem := none
    requiredTransport :=
      [ "A local transport theorem from the external encoded-problem foundation."
      , "A local transport theorem from external relation bundles to `CSP.BoolLanguage`." ]
    generatorMayUseAsTheorem := false
    roles := ["schaefer", "external_metadata", "not_local_theorem"]
    notes := ["Discoverable for planning context only; generated proofs must use local theorems."] }

/-- Explicit blocked path for direct external Schaefer-to-finite-domain transport. -/
def blockedExternalSchaeferFiniteDomainRoute : SchaeferFiniteDomainRouteDescriptor :=
  { name := "blocked_external_schaefer_to_finite_domain"
    status := SchaeferFiniteDomainStatus.blocked
    sourceSymbol := "SchaeferDichotomy.NSAT_S_encoded"
    targetSymbol := "ComplexityReduction.CSP.FiniteDomain.cspDecisionProblem"
    mapSymbol := none
    localTheorem := none
    requiredTransport :=
      [ "External encoded decision problems must be transported to this repository's foundation."
      , "External bundled relations must be transported to local Boolean CSP languages."
      , "Only then can `BoolBridge` move the Boolean formula route to finite-domain CSP." ]
    generatorMayUseAsTheorem := false
    roles := ["schaefer", "blocked", "requires_transport"]
    notes := ["Planner should report this route as unavailable until the listed transports exist."] }

/-- Public Schaefer/Boolean finite-domain transport routes. -/
def schaeferFiniteDomainRoutes : List SchaeferFiniteDomainRouteDescriptor :=
  [ boolCSPToFin2Route
  , boolCSPToBoolDomainRoute
  , localSchaeferThenFiniteDomainRoute
  , booleanCloneCatalogRoute
  , externalSchaeferMetadataRoute
  , blockedExternalSchaeferFiniteDomainRoute
  ]

theorem schaeferFiniteDomainRoutes_length :
    schaeferFiniteDomainRoutes.length = 6 :=
  rfl

theorem booleanCloneCatalogRoute_not_local :
    booleanCloneCatalogRoute.generatorMayUseAsTheorem = false :=
  rfl

theorem externalSchaeferMetadataRoute_not_local :
    externalSchaeferMetadataRoute.generatorMayUseAsTheorem = false :=
  rfl

theorem blockedExternalSchaeferFiniteDomainRoute_not_local :
    blockedExternalSchaeferFiniteDomainRoute.generatorMayUseAsTheorem = false :=
  rfl

end Targets
end ComplexityReduction
