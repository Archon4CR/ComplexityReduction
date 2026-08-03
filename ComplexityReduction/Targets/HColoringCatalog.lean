/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.HColoring.TemplateCatalog
import ComplexityReduction.CSP.FiniteDomain.HColoringExamples

/-!
Planner catalog for graph-homomorphism and `H`-coloring finite-domain CSP routes.
-/

namespace ComplexityReduction
namespace Targets

/-- Planner metadata for graph-homomorphism routes through finite-domain CSP. -/
structure HColoringRouteDescriptor where
  name : String
  descriptorSymbol : Option String := none
  templateSymbol : String
  formulaSymbol : String
  semanticTheorem : String
  targetKind : String
  roles : List String
  notes : List String
  deriving Repr

/-- Generic fixed-template `H`-coloring route. -/
def hColoringGenericRoute : HColoringRouteDescriptor :=
  { name := "h_coloring_generic"
    descriptorSymbol := some "ComplexityReduction.CSP.FiniteDomain.HColoring.TemplateDescriptor"
    templateSymbol := "ComplexityReduction.CSP.FiniteDomain.HColoring.templateLanguage"
    formulaSymbol := "ComplexityReduction.CSP.FiniteDomain.HColoring.graphHomFormula"
    semanticTheorem := "ComplexityReduction.CSP.FiniteDomain.HColoring.hColorable_iff_graphHom"
    targetKind := "fixed_template_graph_hom"
    roles := ["finite_domain_csp", "graph_hom", "h_coloring"]
    notes :=
      [ "Use for arbitrary fixed finite graph templates."
      , "This is a semantic CSP encoding theorem, not a graph-complexity classification." ] }

/-- Two-coloring template route. -/
def twoColoringRoute : HColoringRouteDescriptor :=
  { name := "two_coloring_template"
    descriptorSymbol :=
      some
        "ComplexityReduction.CSP.FiniteDomain.HColoringExamples.twoColorTemplateDescriptor"
    templateSymbol := "ComplexityReduction.CSP.FiniteDomain.HColoringExamples.twoColorTemplate"
    formulaSymbol := "ComplexityReduction.CSP.FiniteDomain.HColoringExamples.twoColoringFormula"
    semanticTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.HColoringExamples.twoColorTemplateDescriptor_formula_satisfiable_iff_graphHom"
    targetKind := "fixed_template_graph_hom_example"
    roles := ["finite_domain_csp", "graph_hom", "two_coloring", "worked_example"]
    notes := ["Small template example for generated graph-to-CSP proof tests."] }

/-- Three-coloring template route. -/
def threeColoringRoute : HColoringRouteDescriptor :=
  { name := "three_coloring_template"
    descriptorSymbol :=
      some
        "ComplexityReduction.CSP.FiniteDomain.HColoringExamples.threeColorTemplateDescriptor"
    templateSymbol := "ComplexityReduction.CSP.FiniteDomain.HColoringExamples.threeColorTemplate"
    formulaSymbol := "ComplexityReduction.CSP.FiniteDomain.HColoringExamples.threeColoringFormula"
    semanticTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.HColoringExamples.threeColorTemplateDescriptor_formula_satisfiable_iff_graphHom"
    targetKind := "fixed_template_graph_hom_example"
    roles := ["finite_domain_csp", "graph_hom", "three_coloring", "worked_example"]
    notes := ["Small template example for generated graph-to-CSP proof tests."] }

/-- Reusable complete/cycle template catalog route. -/
def hColoringTemplateCatalogRoute : HColoringRouteDescriptor :=
  { name := "h_coloring_template_catalog"
    descriptorSymbol :=
      some "ComplexityReduction.CSP.FiniteDomain.HColoring.TemplateCatalogEntry"
    templateSymbol := "ComplexityReduction.CSP.FiniteDomain.HColoring.templateCatalog"
    formulaSymbol :=
      "ComplexityReduction.CSP.FiniteDomain.HColoring.TemplateDescriptor.formula"
    semanticTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.HColoring.TemplateDescriptor.formula_satisfiable_iff_graphHom"
    targetKind := "fixed_template_graph_hom_catalog"
    roles := ["finite_domain_csp", "graph_hom", "h_coloring", "template_catalog"]
    notes :=
      [ "Catalog of complete-graph and cycle graph template constructors."
      , "This route is semantic graph-homomorphism-to-CSP encoding only, not a hardness classification." ] }

/-- Public graph-homomorphism routes available to the planner. -/
def hColoringRoutes : List HColoringRouteDescriptor :=
  [ hColoringGenericRoute
  , twoColoringRoute
  , threeColoringRoute
  , hColoringTemplateCatalogRoute ]

theorem hColoringRoutes_length :
    hColoringRoutes.length = 4 :=
  rfl

end Targets
end ComplexityReduction
