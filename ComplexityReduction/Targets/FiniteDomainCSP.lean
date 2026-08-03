/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain
import ComplexityReduction.SAT.PlanarOneInThree
import ComplexityReduction.Combinatorics.Graph.GadgetReplacementSemantics
import ComplexityReduction.Combinatorics.Graph.GadgetReplacementComposition

/-!
Agent-facing target metadata for finite-domain CSP routes.

The theorem-bearing API lives under `ComplexityReduction.CSP.FiniteDomain`.
This target module gives route planners a compact, typed index for the generic
fixed-template CSP target and the pp-expansion surface.
-/

namespace ComplexityReduction
namespace Targets

/-- Planner metadata for a finite-domain CSP target or expansion route. -/
structure FiniteDomainCSPDescriptor where
  name : String
  descriptorKind : String
  libraryImport : String
  problemSymbol : Option String
  mapSymbol : Option String
  semanticTheorem : Option String
  supportTheorems : List String
  requiredPremises : List String
  roles : List String
  notes : List String
  deriving Repr

/-- Generic fixed-template finite-domain CSP target constructor. -/
def finiteDomainCSPTarget : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_csp_fixed_template"
    descriptorKind := "target_constructor"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain"
    problemSymbol := some "ComplexityReduction.CSP.FiniteDomain.cspDecisionProblem"
    mapSymbol := none
    semanticTheorem := none
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Formula.Satisfiable"
      , "ComplexityReduction.CSP.FiniteDomain.Formula.Satisfies"
      , "ComplexityReduction.CSP.FiniteDomain.Constraint.Satisfies" ]
    requiredPremises :=
      [ "A fixed finite-domain language `Γ : Language D`."
      , "`Γ.finiteDomain` and `Γ.finiteSymbol` are supplied by the language value." ]
    roles := ["finite_domain_csp", "target_constructor"]
    notes :=
      [ "Use this when the generated reduction target is a fixed finite relational template."
      , "The encoded problem is `cspDecisionProblem Γ`." ] }

/-- Generic pp-representation expansion route for finite-domain CSP formulas. -/
def finiteDomainPPExpansionRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_pp_expansion"
    descriptorKind := "semantic_formula_expansion"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain"
    problemSymbol := none
    mapSymbol := some "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaRepresentation"
    semanticTheorem :=
      some "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaRepresentation_satisfiable_iff"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaRepresentationFrom_sound"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaRepresentationFrom_complete"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaRepresentationFrom_length_le_maxBlockConstraints"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaRepresentation_length_le"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaRepresentation_size_le"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.conjunctionListFormula"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.conjunctionListFormula_represents"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.foldProductFormula"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.foldProductFormula_represents"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.relationTable"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.relationTable_complete"
      , "ComplexityReduction.CSP.FiniteDomain.FiniteSupport.sourceFresh_at_formulaVarBound"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.LanguageRepresentation.blockBound" ]
    requiredPremises :=
      [ "A proof-bearing `LanguageRepresentation Δ Γ`."
      , "No manual source freshness or block-width premise is needed for the automatic wrapper." ]
    roles := ["finite_domain_csp", "pp_expansion", "semantic_equivalence"]
    notes :=
      [ "This is the default route for compiling pp-defined source constraints into a target language."
      , "It is based on Jeavons-Cohen-Gyssens pp-definability closure operations." ] }

/-- Costed certificate route for finite-domain pp-representation expansion. -/
def finiteDomainPPCostedRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_pp_costed_certificate"
    descriptorKind := "costed_semantic_formula_expansion"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain"
    problemSymbol := none
    mapSymbol := some "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaRepresentation"
    semanticTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.PPDef.finiteDomainRepresentationReductionCertificateOfLanguageRepresentation"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaRepresentationCostedMap"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaRepresentationPolyTime"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaRepresentationKarpReduction"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.FiniteDomainRepresentationReductionCertificate"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaSingleDerivedRepresentationKarpReduction"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.finiteDomainSingleDerivedRepresentationReductionCertificate"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaDerivedFamilyRepresentationKarpReduction"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.finiteDomainDerivedFamilyRepresentationReductionCertificate" ]
    requiredPremises :=
      [ "A proof-bearing finite-domain `LanguageRepresentation Δ Γ`."
      , "Current formula encodings are raw; the certificate records semantic and syntactic bounds for future structured encodings." ]
    roles := ["finite_domain_csp", "pp_expansion", "costed_certificate", "karp_reduction"]
    notes :=
      [ "Use this route when a generated artifact needs an actual costed Karp wrapper."
      , "The semantic route remains `formulaViaRepresentation_satisfiable_iff`." ] }

/-- Finite-domain polymorphism preservation route. -/
def finiteDomainPolymorphismRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_polymorphism_preservation"
    descriptorKind := "algebraic_preservation"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain"
    problemSymbol := none
    mapSymbol := none
    semanticTheorem :=
      some "ComplexityReduction.CSP.FiniteDomain.PreservesLanguage.of_representation"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.PreservesLanguage.formula_satisfies"
      , "ComplexityReduction.CSP.FiniteDomain.PreservesLanguage.pp_definedRel"
      , "ComplexityReduction.CSP.FiniteDomain.PreservesLanguage.pp_representedRel"
      , "ComplexityReduction.CSP.FiniteDomain.Polymorphism.through_representation"
      , "ComplexityReduction.CSP.FiniteDomain.AlgebraicCatalog.booleanOperationDescriptors"
      , "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolAnd_iff_allRelationsHorn"
      , "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolOr_iff_allRelationsDualHorn"
      , "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolMajority_iff_allRelationsBijunctive"
      , "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolTernaryXor_iff_allRelationsAffine"
      , "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolComplement_iff_allRelationsComplementive"
      , "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolFalse_iff_allRelationsZeroValid"
      , "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolTrue_iff_allRelationsOneValid" ]
    requiredPremises :=
      [ "An operation `op : Operation D n`."
      , "A proof that `op` preserves the target language."
      , "For source transport, a proof-bearing pp `LanguageRepresentation Δ Γ`." ]
    roles := ["finite_domain_csp", "polymorphism", "pp_preservation", "algebraic_metadata"]
    notes :=
      [ "Use this for algebraic CSP side conditions instead of asserting a dichotomy theorem."
      , "The route proves local preservation facts for formulas and pp-represented relations." ] }

/-- One-symbol pp-derived finite-domain CSP route. -/
def finiteDomainSingleDerivedRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_single_derived_relation"
    descriptorKind := "derived_relation_expansion"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain"
    problemSymbol := none
    mapSymbol :=
      some "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaSingleDerivedRepresentation"
    semanticTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaSingleDerivedRepresentation_satisfiable_iff"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.PPDef.singleDerivedLanguage"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.singleDerivedRepresentation"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.atomicRelationFormula_represents"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaSingleDerivedRepresentation_length_le"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaSingleDerivedRepresentation_size_le" ]
    requiredPremises :=
      [ "`[Inhabited D]` for atomic self-representation of old symbols."
      , "A pp block for the new relation." ]
    roles := ["finite_domain_csp", "derived_relation", "pp_expansion"]
    notes := ["Adds one pp-defined relation symbol and expands formulas back to the base language."] }

/-- Finite family pp-derived finite-domain CSP route. -/
def finiteDomainDerivedFamilyRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_derived_relation_family"
    descriptorKind := "derived_family_expansion"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain"
    problemSymbol := none
    mapSymbol :=
      some "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaDerivedFamilyRepresentation"
    semanticTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaDerivedFamilyRepresentation_satisfiable_iff"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.PPDef.derivedFamilyLanguage"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.derivedFamilyLanguage_size"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.derivedFamilyRepresentation"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.derivedFamilyRepresentation_blockBound"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.derivedFamilyRepresentation_auxBlockWidth_le"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaDerivedFamilyRepresentation_length_le"
      , "ComplexityReduction.CSP.FiniteDomain.PPDef.formulaViaDerivedFamilyRepresentation_size_le" ]
    requiredPremises :=
      [ "`[Inhabited D]` for atomic self-representation of old symbols."
      , "`[Fintype NewSym]` for the finite family of new symbols."
      , "A pp block for each new symbol." ]
    roles := ["finite_domain_csp", "derived_family", "pp_expansion"]
    notes := ["Mounts a finite gadget palette as new relation symbols and expands uniformly."] }

/-- Boolean-to-finite-domain CSP transport route. -/
def finiteDomainBoolBridgeRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_bool_bridge"
    descriptorKind := "domain_transport"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain"
    problemSymbol := none
    mapSymbol := some "ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaFin2OfBoolFormula"
    semanticTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaFin2OfBoolFormula_satisfiable_iff"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula_satisfiable_iff"
      , "ComplexityReduction.CSP.FiniteDomain.BoolBridge.relFin2OfBoolRel_holds_iff" ]
    requiredPremises := ["A Boolean CSP language."]
    roles := ["finite_domain_csp", "bool_bridge", "domain_transport"]
    notes := ["Reuses Boolean CSP reductions over `Bool` or `Fin 2` finite-domain templates."] }

/-- Boolean pp-certificate transport into finite-domain CSP. -/
def finiteDomainBoolPPTransportRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_bool_pp_transport"
    descriptorKind := "pp_certificate_domain_transport"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain"
    problemSymbol := none
    mapSymbol :=
      some "ComplexityReduction.CSP.FiniteDomain.BoolPPTransport.formulaViaFin2BoolPPTransport"
    semanticTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolPPTransport.formulaViaFin2BoolPPTransport_satisfiable_iff"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.BoolPPTransport.languageRepresentationOfBool"
      , "ComplexityReduction.CSP.FiniteDomain.BoolPPTransport.languageRepresentationFin2OfBool"
      , "ComplexityReduction.CSP.FiniteDomain.BoolPPTransport.relationFormulaOfBool_represents"
      , "ComplexityReduction.CSP.FiniteDomain.BoolPPTransport.relationFormulaFin2OfBool_represents"
      , "ComplexityReduction.CSP.FiniteDomain.BoolPPTransport.formulaViaBoolPPTransport_satisfiable_iff" ]
    requiredPremises :=
      [ "A proof-bearing `ComplexityReduction.CSP.PPDef.LanguageRepresentation Δ Γ`."
      , "Use the `Fin 2` theorem by default; use the `Bool` theorem when the target domain is literal `Bool`." ]
    roles := ["finite_domain_csp", "bool_bridge", "pp_transport", "semantic_equivalence"]
    notes :=
      [ "Transports existing Boolean pp certificates directly into finite-domain expansion."
      , "This avoids rebuilding Schaefer-side pp blocks after choosing the finite-domain route." ] }

/-- Monotone positive one-in-three SAT bridge to finite-domain Boolean CSP. -/
def finiteDomainPlanarOneInThreeRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_planar_one_in_three_bridge"
    descriptorKind := "monotone_one_in_three_to_finite_domain_csp"
    libraryImport := "ComplexityReduction.SAT.PlanarOneInThree"
    problemSymbol := none
    mapSymbol :=
      some "ComplexityReduction.SAT.PlanarOneInThree.Formula.toFiniteDomainFormula"
    semanticTheorem :=
      some
        "ComplexityReduction.SAT.PlanarOneInThree.Formula.toFiniteDomainFormula_satisfiable_iff"
    supportTheorems :=
      [ "ComplexityReduction.SAT.PlanarOneInThree.Clause"
      , "ComplexityReduction.SAT.PlanarOneInThree.Formula"
      , "ComplexityReduction.SAT.PlanarOneInThree.boolLanguage"
      , "ComplexityReduction.SAT.PlanarOneInThree.finiteDomainLanguage"
      , "ComplexityReduction.SAT.PlanarOneInThree.Clause.toFiniteDomainConstraint_satisfies_iff"
      , "ComplexityReduction.SAT.PlanarOneInThree.Formula.toFiniteDomainFormula_satisfies_iff"
      , "ComplexityReduction.SAT.PlanarOneInThree.Formula.toFiniteDomainFormula_length"
      , "ComplexityReduction.SAT.PlanarOneInThree.Formula.incidenceGraph"
      , "ComplexityReduction.SAT.PlanarOneInThree.Formula.incidenceGraph_wellFormed_of_varsWithinBounds"
      , "ComplexityReduction.SAT.PlanarOneInThree.Formula.IsCubicIncidence" ]
    requiredPremises :=
      [ "A finite list of positive ternary exactly-one clauses."
      , "Use `VarsWithinBounds` for incidence graph well-formedness."
      , "Planarity and cubic incidence are metadata/side conditions here, not a local hardness theorem." ]
    roles :=
      [ "finite_domain_csp", "sat", "one_in_three", "monotone",
        "incidence_graph", "semantic_equivalence" ]
    notes :=
      [ "Bridges a monotone positive one-in-three formula to the finite-domain `Bool` CSP surface."
      , "No Lichtenstein planar-SAT theorem or Moore-Robson hardness theorem is asserted." ] }

/-- H-coloring as a finite-domain CSP route. -/
def finiteDomainHColoringRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_h_coloring"
    descriptorKind := "graph_hom_csp_target"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain"
    problemSymbol := none
    mapSymbol := some "ComplexityReduction.CSP.FiniteDomain.HColoring.graphHomFormula"
    semanticTheorem :=
      some "ComplexityReduction.CSP.FiniteDomain.HColoring.hColorable_iff_graphHom"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.HColoring.templateLanguage"
      , "ComplexityReduction.CSP.FiniteDomain.HColoring.TemplateDescriptor"
      , "ComplexityReduction.CSP.FiniteDomain.HColoring.TemplateDescriptor.toLanguage"
      , "ComplexityReduction.CSP.FiniteDomain.HColoring.TemplateDescriptor.formula_satisfiable_iff_graphHom"
      , "ComplexityReduction.CSP.FiniteDomain.HColoring.graphHomFormula_satisfies_iff" ]
    requiredPremises := ["A fixed graph template `H` and an input graph `G`."]
    roles := ["finite_domain_csp", "h_coloring", "graph_hom"]
    notes := ["Uses Feder-Vardi style fixed-template graph homomorphism as CSP."] }

/-- Standard finite-domain equality and pinning gadgets. -/
def finiteDomainStandardGadgetsRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_standard_gadgets"
    descriptorKind := "standard_relation_gadgets"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain"
    problemSymbol := none
    mapSymbol := none
    semanticTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.StandardGadgets.equalityFormula_satisfies_iff"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.StandardGadgets.pinFormula_satisfies_iff"
      , "ComplexityReduction.CSP.FiniteDomain.StandardGadgets.eqPinEqualityConstraint_satisfies_iff"
      , "ComplexityReduction.CSP.FiniteDomain.StandardGadgets.eqPinPinConstraint_satisfies_iff"
      , "ComplexityReduction.CSP.FiniteDomain.StandardGadgets.singletonTupleRel_holds_iff" ]
    requiredPremises :=
      [ "A finite domain."
      , "For pinning, a concrete domain value." ]
    roles := ["finite_domain_csp", "standard_gadget", "equality", "pinning"]
    notes := ["Reusable one-constraint equality and pinning formulas for finite-domain CSPs."] }

/-- Local finite-region tiling constraints as finite-domain CSP. -/
def finiteDomainTilingRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_tiling_csp"
    descriptorKind := "local_tiling_csp_encoding"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain"
    problemSymbol := none
    mapSymbol := some "ComplexityReduction.CSP.FiniteDomain.Tiling.TilingInstance.tilingFormula"
    semanticTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.Tiling.TilingInstance.tilingFormula_satisfiable_iff"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Tiling.localCheckFormula_satisfies_iff"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.localCheckFormula_length"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.coverageCheck_satisfies_iff"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.adjacencyCheck_satisfies_iff"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.RectangularRegion.cellVar_lt_cellCount_of_contains"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.ExplicitRegion.cellVar_lt_cellCount" ]
    requiredPremises :=
      [ "A finite tile palette and finite list of local coverage/adjacency checks."
      , "This route proves local CSP semantic equivalence, not Moore-Robson NP-hardness." ]
    roles := ["finite_domain_csp", "tiling", "local_constraints", "grid_encoding"]
    notes :=
      [ "Use this as the common target for finite-region tiling gadgets."
      , "Relation symbols are local-check indices, so generated reductions can add checks list-wise." ] }

/-- Rectangular tiling local-rule generator as finite-domain CSP. -/
def finiteDomainRectangularTilingRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_rectangular_tiling_csp"
    descriptorKind := "rectangular_tiling_csp_generator"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain.Tiling.Rectangular"
    problemSymbol := none
    mapSymbol :=
      some
        "ComplexityReduction.CSP.FiniteDomain.Tiling.Rectangular.rectangularTilingFormula"
    semanticTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.Tiling.Rectangular.rectangularTilingFormula_satisfiable_iff"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Tiling.Rectangular.cells"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Rectangular.cells_length"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Rectangular.mem_cells_iff_contains"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Rectangular.horizontalPairs"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Rectangular.verticalPairs"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Rectangular.coverageChecks"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Rectangular.adjacencyChecks"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Rectangular.localChecks"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Rectangular.localChecks_satisfy_iff"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Rectangular.rectangularTilingFormula_length_eq"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Rectangular.localChecks_scope_lt_cellCount" ]
    requiredPremises :=
      [ "A rectangular region, finite tile palette, cell predicate, and nearest-neighbor adjacency predicate."
      , "This route proves generated local-rule CSP equivalence, not Moore-Robson NP-hardness." ]
    roles := ["finite_domain_csp", "tiling", "rectangular_grid", "local_rule_generator"]
    notes :=
      [ "Use this when reductions need all rectangular coverage and nearest-neighbor checks generated automatically."
      , "Generated scopes are proved below `RectangularRegion.cellCount`." ] }

/-- Wang edge-color rectangular tiling local-rule generator as finite-domain CSP. -/
def finiteDomainWangTilingRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_wang_tiling_csp"
    descriptorKind := "wang_edge_color_tiling_csp_generator"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain.Tiling.Wang"
    problemSymbol := none
    mapSymbol :=
      some "ComplexityReduction.CSP.FiniteDomain.Tiling.Wang.rectangularWangTilingFormula"
    semanticTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.Tiling.Wang.rectangularWangTilingFormula_satisfiable_iff"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Tiling.Wang.Side"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Wang.EdgeColoredPalette"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Wang.color"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Wang.compatible"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Wang.compatible_iff_color_eq"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Wang.allowedCell"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Wang.allowedAdj"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Wang.allowedAdj_horizontal_iff"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Wang.allowedAdj_vertical_iff"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Wang.rectangularWangTilingFormula_length_eq"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.Wang.localChecks_scope_lt_cellCount" ]
    requiredPremises :=
      [ "A rectangular finite grid and a finite edge-colored Wang palette."
      , "This route proves local edge-color compatibility as a generated CSP, not tiling NP-hardness." ]
    roles :=
      [ "finite_domain_csp", "tiling", "wang_tile", "edge_color",
        "rectangular_grid", "local_rule_generator" ]
    notes :=
      [ "Use this when generated reductions can specify north/east/south/west colors instead of custom adjacency predicates."
      , "The construction is a thin wrapper over the rectangular tiling compiler." ] }

/-- Moore-Robson tiling gadget vocabulary as metadata descriptors. -/
def finiteDomainMooreRobsonDescriptorRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_moore_robson_tiling_descriptor_catalog"
    descriptorKind := "tiling_gadget_descriptor_catalog"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson"
    problemSymbol := none
    mapSymbol := none
    semanticTheorem := none
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.Signal"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.Port"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.WireDescriptor"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.GateKind"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.GateDescriptor"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.wire"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.andGate"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.notGate"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.splitter"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.variableStart"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.trueTerminal"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.bend"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.phaseChange"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.andGate_truthTable_iff"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.splitter_truthTable_iff"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.gateCatalog_length"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.wireCatalog_length" ]
    requiredPremises :=
      [ "Use this catalog as Moore-Robson gadget vocabulary metadata only."
      , "A separate concrete Wang palette, coordinate embedding, and local tiling proof are required before citing a gadget as a correctness theorem." ]
    roles :=
      [ "finite_domain_csp", "tiling", "moore_robson", "descriptor_catalog",
        "metadata_only" ]
    notes :=
      [ "Names the wire, AND, NOT, splitter, variable-start, true-terminal, bend, and phase-change descriptor shapes."
      , "The catalog exposes arity and truth-table shape lemmas but no NP-hardness or parsimonious tiling theorem." ] }

/-- Proof-carrying local Moore-Robson Wang gadget realization route. -/
def mooreRobsonProofCarryingGadgetRoute : FiniteDomainCSPDescriptor :=
  { name := "moore_robson_proof_carrying_gadget_realization"
    descriptorKind := "proof_carrying_tiling_gadget_realization"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.Realization"
    problemSymbol := none
    mapSymbol :=
      some "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.realizationFormula"
    semanticTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.realization_solutionEquiv_truthTable"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.SignalAssignment"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.PortValuation"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.BoundaryCondition"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.WangGadgetRegion"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.WangGadgetRealization"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.realizationFormula_satisfies_iff"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.realizesWireTruthTable"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.realizesGateTruthTable" ]
    requiredPremises :=
      [ "A concrete rectangular Wang region, edge-colored palette, boundary predicate, and local soundness/completeness proof."
      , "Use this route for local gadget realization only; it is not a global Moore-Robson tiling hardness theorem." ]
    roles :=
      [ "finite_domain_csp", "tiling", "moore_robson", "wang_tile",
        "proof_carrying_realization", "truth_table" ]
    notes :=
      [ "The wrapper connects rectangular Wang formula satisfiability plus boundary conditions to descriptor-level truth tables."
      , "Concrete wire/gate correctness remains a supplied premise of `WangGadgetRealization`." ] }

/-- Moore-Robson local realization example and semantic network route. -/
def mooreRobsonRealizationExampleRoute : FiniteDomainCSPDescriptor :=
  { name := "moore_robson_realization_example"
    descriptorKind := "proof_carrying_tiling_gadget_example"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.Examples"
    problemSymbol := none
    mapSymbol :=
      some "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.TrivialWireRealization"
    semanticTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.trivialWire_realizesWireTruthTable"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.TrivialWireRealization"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.trivialWire_realizesWireTruthTable"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.realizationTruthTableOfWire"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.realizationTruthTableOfGate"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.RealizationStep"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.RealizationNetwork"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.realizationNetwork_sound"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.realizationNetwork_complete"
      , "ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.realizationNetwork_iff" ]
    requiredPremises :=
      [ "Use the trivial wire as a smoke-test and API example only."
      , "Real Moore-Robson wires/gates still require concrete palettes and boundary proofs." ]
    roles :=
      [ "finite_domain_csp", "tiling", "moore_robson", "worked_example",
        "proof_carrying_realization", "composition" ]
    notes :=
      [ "Provides a complete local realization example for route regression tests."
      , "Adds a proof-carrying semantic network wrapper for composing supplied local steps." ] }

/-- Proof-carrying one-site graph gadget replacement semantics route. -/
def graphGadgetReplacementSemanticsRoute : FiniteDomainCSPDescriptor :=
  { name := "graph_gadget_replacement_semantics"
    descriptorKind := "graph_gadget_replacement_semantics"
    libraryImport := "ComplexityReduction.Combinatorics.Graph.GadgetReplacementSemantics"
    problemSymbol := none
    mapSymbol := some "ComplexityReduction.Combinatorics.Graph.Gadget.replaceOne"
    semanticTheorem :=
      some "ComplexityReduction.Combinatorics.Graph.Gadget.replaceOne_semanticIff"
    supportTheorems :=
      [ "ComplexityReduction.Combinatorics.Graph.Gadget.TerminalAssignment"
      , "ComplexityReduction.Combinatorics.Graph.Gadget.ShapePredicate"
      , "ComplexityReduction.Combinatorics.Graph.Gadget.ReplacementSemantics"
      , "ComplexityReduction.Combinatorics.Graph.Gadget.LocalReplacementCertificate"
      , "ComplexityReduction.Combinatorics.Graph.Gadget.replaceOne_semanticSound"
      , "ComplexityReduction.Combinatorics.Graph.Gadget.replaceOne_semanticComplete"
      , "ComplexityReduction.Combinatorics.Graph.Gadget.replaceOne_semanticWellFormed"
      , "ComplexityReduction.Combinatorics.Graph.PlanarGadgetDescriptor.toLocalReplacementCertificate" ]
    requiredPremises :=
      [ "A well-formed host graph, bounded terminal map, well-formed gadget shape, and local semantic soundness/completeness."
      , "The semantics are caller-supplied graph predicates; no concrete crossover or planar-hardness theorem is asserted." ]
    roles :=
      [ "graph_gadget", "replacement", "proof_carrying_semantics",
        "side_condition", "local_certificate" ]
    notes :=
      [ "Wraps one-site syntactic replacement with local semantic soundness and completeness."
      , "Planar gadget descriptors can be converted only after the caller supplies the semantic proof obligations." ] }

/-- Proof-carrying graph gadget replacement chain route. -/
def graphGadgetReplacementChainRoute : FiniteDomainCSPDescriptor :=
  { name := "graph_gadget_replacement_chain_semantics"
    descriptorKind := "graph_gadget_replacement_chain_semantics"
    libraryImport := "ComplexityReduction.Combinatorics.Graph.GadgetReplacementComposition"
    problemSymbol := none
    mapSymbol := some "ComplexityReduction.Combinatorics.Graph.Gadget.replaceChain"
    semanticTheorem :=
      some "ComplexityReduction.Combinatorics.Graph.Gadget.replaceChain_semanticIff"
    supportTheorems :=
      [ "ComplexityReduction.Combinatorics.Graph.Gadget.LocalReplacementChain"
      , "ComplexityReduction.Combinatorics.Graph.Gadget.replaceChain"
      , "ComplexityReduction.Combinatorics.Graph.Gadget.replaceChain_wellFormed"
      , "ComplexityReduction.Combinatorics.Graph.Gadget.replaceChain_semanticSound"
      , "ComplexityReduction.Combinatorics.Graph.Gadget.replaceChain_semanticComplete"
      , "ComplexityReduction.Combinatorics.Graph.Gadget.replaceChain_semanticIff" ]
    requiredPremises :=
      [ "A finite `LocalReplacementChain P G H` whose local certificates preserve the same graph predicate `P`."
      , "The route composes supplied local certificates only; it does not assert concrete crossover, planarity, or hardness." ]
    roles :=
      [ "graph_gadget", "replacement", "proof_carrying_semantics",
        "chain_composition", "side_condition" ]
    notes :=
      [ "Composes one-site replacement certificates by induction over the chain."
      , "Use after each local gadget certificate has already supplied its semantic obligations." ] }

/-- Small worked examples for derived relations and H-coloring templates. -/
def finiteDomainWorkedExamplesRoute : FiniteDomainCSPDescriptor :=
  { name := "finite_domain_worked_examples"
    descriptorKind := "worked_examples"
    libraryImport := "ComplexityReduction.CSP.FiniteDomain"
    problemSymbol := none
    mapSymbol := none
    semanticTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.PPDef.Examples.expandEqPinCopyFamily_satisfiable_iff"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.PPDef.Examples.expandSingleEqualityCopy_satisfiable_iff"
      , "ComplexityReduction.CSP.FiniteDomain.HColoringExamples.twoColoringFormula_satisfiable_iff_graphHom"
      , "ComplexityReduction.CSP.FiniteDomain.HColoringExamples.threeColoringFormula_satisfiable_iff_graphHom" ]
    requiredPremises := ["Use these as examples or smoke-test targets, not as complete hardness claims."]
    roles := ["finite_domain_csp", "worked_example", "derived_family", "h_coloring"]
    notes := ["Named low-friction examples for generated proof tests and route selection prompts."] }

/-- Finite-domain CSP routes visible to the planner. -/
def finiteDomainCSPRoutes : List FiniteDomainCSPDescriptor :=
  [ finiteDomainCSPTarget
  , finiteDomainPPExpansionRoute
  , finiteDomainPPCostedRoute
  , finiteDomainPolymorphismRoute
  , finiteDomainSingleDerivedRoute
  , finiteDomainDerivedFamilyRoute
  , finiteDomainBoolBridgeRoute
  , finiteDomainBoolPPTransportRoute
  , finiteDomainPlanarOneInThreeRoute
  , finiteDomainHColoringRoute
  , finiteDomainStandardGadgetsRoute
  , finiteDomainTilingRoute
  , finiteDomainRectangularTilingRoute
  , finiteDomainWangTilingRoute
  , finiteDomainMooreRobsonDescriptorRoute
  , mooreRobsonProofCarryingGadgetRoute
  , mooreRobsonRealizationExampleRoute
  , graphGadgetReplacementSemanticsRoute
  , graphGadgetReplacementChainRoute
  , finiteDomainWorkedExamplesRoute
  ]

theorem finiteDomainCSPRoutes_length :
    finiteDomainCSPRoutes.length = 20 :=
  rfl

end Targets
end ComplexityReduction
