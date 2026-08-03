/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.Counting.BoolPPTransport
import ComplexityReduction.CSP.FiniteDomain.Counting.DerivedFamily

/-!
Planner catalog for finite-domain CSP counting routes.

The catalog exposes local finite-support counting definitions and records
source-gated counting-classification work without asserting #P-hardness or a
counting dichotomy.
-/

namespace ComplexityReduction
namespace Targets

/-- Local finite-domain CSP counting problem constructor. -/
def finiteDomainCountingProblemRoute : CSP.CountingRouteDescriptor :=
  { name := "finite_domain_csp_solution_count"
    sourceSymbol := "ComplexityReduction.CSP.FiniteDomain.Formula"
    targetSymbol := "ComplexityReduction.CSP.FiniteDomain.countingProblem"
    countTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.Formula.solutionCount_pos_iff_satisfiable"
    status := CSP.CountPreservationStatus.decisionOnly
    roles := ["finite_domain_csp", "counting", "finite_support", "decision_boundary"]
    notes :=
      [ "Counts finite-support assignments on the formula's variable support."
      , "The constructor requires `[Fintype D]` and `[Inhabited D]` for the domain."
      , "The exposed theorem relates positive count to ordinary satisfiability." ] }

/-- Count-preserving pp-expansion route, available only with an explicit certificate. -/
def finiteDomainPPCountPreservingRoute : CSP.CountingRouteDescriptor :=
  { name := "finite_domain_pp_count_preserving_certificate"
    sourceSymbol :=
      "ComplexityReduction.CSP.FiniteDomain.PPDef.CountPreservingRepresentationCertificate"
    targetSymbol := "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaRepresentation"
    countTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.PPDef.solutionCount_viaRepresentation"
    status := CSP.CountPreservationStatus.countPreserving
    roles := ["finite_domain_csp", "pp_expansion", "counting", "certificate_required"]
    notes :=
      [ "Use only when a concrete representation certificate proves exact count preservation."
      , "Plain pp expansion is satisfiability-preserving, not automatically parsimonious." ] }

/-- Count-preserving route obtained from an explicit bijection between solution sets. -/
def finiteDomainSolutionBijectionCountingRoute : CSP.CountingRouteDescriptor :=
  { name := "finite_domain_solution_bijection_counting"
    sourceSymbol := "ComplexityReduction.CSP.FiniteDomain.Formula.SolutionValuation"
    targetSymbol :=
      "ComplexityReduction.CSP.FiniteDomain.Formula.SolutionEquivCertificate"
    countTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.Formula.solutionCount_eq_of_solutionEquiv"
    status := CSP.CountPreservationStatus.countPreserving
    roles :=
      [ "finite_domain_csp", "counting", "solution_bijection", "certificate_required" ]
    notes :=
      [ "Turns an explicit equivalence between finite-support solution valuations into exact count preservation."
      , "Use this route to justify parsimonious/count-preserving gadgets without asserting any counting classification theorem." ] }

/-- Count-preserving route for transporting Boolean CSP formulas to finite-domain `Bool`. -/
def boolBridgeCountingRoute : CSP.CountingRouteDescriptor :=
  { name := "bool_bridge_counting"
    sourceSymbol := "ComplexityReduction.CSP.Formula"
    targetSymbol := "ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula"
    countTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolBridge.solutionCount_formulaOfBoolFormula"
    status := CSP.CountPreservationStatus.countPreserving
    roles := ["boolean_csp", "finite_domain_csp", "counting", "solution_bijection"]
    notes :=
      [ "Counts Boolean finite-support valuations and the finite-domain Bool image."
      , "Backed by an explicit solution-valuation equivalence; it does not assert a counting classification theorem." ] }

/-- Count-preserving route for transporting Boolean CSP formulas to finite-domain `Fin 2`. -/
def boolFin2BridgeCountingRoute : CSP.CountingRouteDescriptor :=
  { name := "bool_fin2_bridge_counting"
    sourceSymbol := "ComplexityReduction.CSP.Formula"
    targetSymbol := "ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaFin2OfBoolFormula"
    countTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolBridge.solutionCount_formulaFin2OfBoolFormula"
    status := CSP.CountPreservationStatus.countPreserving
    roles := ["boolean_csp", "finite_domain_csp", "fin2", "counting", "solution_bijection"]
    notes :=
      [ "Uses the local `Bool`/`Fin 2` value equivalence on finite-support valuations."
      , "The route is exact count preservation for the bridge formulas only." ] }

/-- Count-preserving route for certified Boolean pp transport to finite-domain `Bool`. -/
def boolPPTransportCountingRoute : CSP.CountingRouteDescriptor :=
  { name := "bool_pp_transport_counting"
    sourceSymbol :=
      "ComplexityReduction.CSP.FiniteDomain.BoolPPTransport.CountPreservingBoolRepresentationCertificate"
    targetSymbol :=
      "ComplexityReduction.CSP.FiniteDomain.BoolPPTransport.formulaViaBoolPPTransport"
    countTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolPPTransport.solutionCount_formulaViaBoolPPTransport"
    status := CSP.CountPreservationStatus.countPreserving
    roles :=
      [ "boolean_csp", "finite_domain_csp", "pp_transport", "counting",
        "certificate_required" ]
    notes :=
      [ "Requires a count-preserving certificate for the transported finite-domain Bool pp representation."
      , "Plain Boolean pp transport remains decision-preserving only unless this certificate is supplied." ] }

/-- Count-preserving route for certified Boolean pp transport to finite-domain `Fin 2`. -/
def boolPPTransportFin2CountingRoute : CSP.CountingRouteDescriptor :=
  { name := "bool_fin2_pp_transport_counting"
    sourceSymbol :=
      "ComplexityReduction.CSP.FiniteDomain.BoolPPTransport.CountPreservingFin2RepresentationCertificate"
    targetSymbol :=
      "ComplexityReduction.CSP.FiniteDomain.BoolPPTransport.formulaViaFin2BoolPPTransport"
    countTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolPPTransport.solutionCount_formulaViaFin2BoolPPTransport"
    status := CSP.CountPreservationStatus.countPreserving
    roles :=
      [ "boolean_csp", "finite_domain_csp", "fin2", "pp_transport", "counting",
        "certificate_required" ]
    notes :=
      [ "Requires a count-preserving certificate for the transported finite-domain Fin 2 pp representation."
      , "The Boolean-to-Fin 2 bridge count equality is used only after the certified pp-expansion step." ] }

/-- Count-preserving route for certified finite-domain derived-family expansion. -/
def derivedFamilyCountingRoute : CSP.CountingRouteDescriptor :=
  { name := "finite_domain_derived_family_counting"
    sourceSymbol :=
      "ComplexityReduction.CSP.FiniteDomain.PPDef.DerivedFamilyCountPreservingCertificate"
    targetSymbol :=
      "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaRepresentation"
    countTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.PPDef.solutionCount_viaDerivedFamilyRepresentation"
    status := CSP.CountPreservationStatus.countPreserving
    roles :=
      [ "finite_domain_csp", "derived_family", "pp_expansion", "counting",
        "certificate_required" ]
    notes :=
      [ "Turns a per-formula solution-equivalence certificate into exact count preservation for finite derived families."
      , "Does not claim arbitrary pp-derived families are parsimonious without the certificate." ] }

/-- Tiling-counting route through the finite-domain CSP tiling formula. -/
def finiteDomainTilingCountingRoute : CSP.CountingRouteDescriptor :=
  { name := "finite_domain_tiling_solution_count"
    sourceSymbol := "ComplexityReduction.CSP.FiniteDomain.Tiling.TilingInstance"
    targetSymbol := "ComplexityReduction.CSP.FiniteDomain.Tiling.TilingInstance.solutionCount"
    countTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.Tiling.TilingInstance.solutionCount_pos_iff_tileable"
    status := CSP.CountPreservationStatus.decisionOnly
    roles := ["finite_domain_csp", "tiling", "counting", "finite_support"]
    notes :=
      [ "Counts finite-support satisfying tile placements for the generated local-check formula."
      , "Using the theorem requires an inhabited palette state, i.e. a nonempty finite tile-state domain."
      , "No parsimonious tiling hardness claim is asserted." ] }

/-- Placeholder for Creignou-Hermann style counting-CSP classification work. -/
def sourceGatedCountingClassificationRoute : CSP.CountingRouteDescriptor :=
  { name := "source_gated_counting_csp_classification"
    sourceSymbol := "Creignou-Hermann 1996 generalized satisfiability counting"
    targetSymbol := "future ComplexityReduction counting classification module"
    countTheorem := none
    status := CSP.CountPreservationStatus.sourceGated
    roles := ["counting", "classification", "source_gated"]
    notes :=
      [ "The official source is not locally available in the literature cache."
      , "Do not use this route as a theorem until the source and Lean proof are added." ] }

/-- Public counting-CSP route catalog. -/
def countingCSPRoutes : List CSP.CountingRouteDescriptor :=
  [ finiteDomainCountingProblemRoute
  , finiteDomainPPCountPreservingRoute
  , finiteDomainSolutionBijectionCountingRoute
  , boolBridgeCountingRoute
  , boolFin2BridgeCountingRoute
  , boolPPTransportCountingRoute
  , boolPPTransportFin2CountingRoute
  , derivedFamilyCountingRoute
  , finiteDomainTilingCountingRoute
  , sourceGatedCountingClassificationRoute ]

theorem countingCSPRoutes_length :
    countingCSPRoutes.length = 10 :=
  rfl

theorem sourceGatedCountingClassificationRoute_not_usable :
    sourceGatedCountingClassificationRoute.generatorMayUseAsCountingTheorem = false :=
  rfl

theorem finiteDomainPPCountPreservingRoute_usable_with_certificate :
    finiteDomainPPCountPreservingRoute.generatorMayUseAsCountingTheorem = true :=
  rfl

theorem finiteDomainSolutionBijectionCountingRoute_usable_with_certificate :
    finiteDomainSolutionBijectionCountingRoute.generatorMayUseAsCountingTheorem = true :=
  rfl

theorem boolBridgeCountingRoute_usable :
    boolBridgeCountingRoute.generatorMayUseAsCountingTheorem = true :=
  rfl

theorem boolFin2BridgeCountingRoute_usable :
    boolFin2BridgeCountingRoute.generatorMayUseAsCountingTheorem = true :=
  rfl

theorem boolPPTransportCountingRoute_usable_with_certificate :
    boolPPTransportCountingRoute.generatorMayUseAsCountingTheorem = true :=
  rfl

theorem boolPPTransportFin2CountingRoute_usable_with_certificate :
    boolPPTransportFin2CountingRoute.generatorMayUseAsCountingTheorem = true :=
  rfl

theorem derivedFamilyCountingRoute_usable_with_certificate :
    derivedFamilyCountingRoute.generatorMayUseAsCountingTheorem = true :=
  rfl

end Targets
end ComplexityReduction
