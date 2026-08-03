/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.HColoring

/-!
Small fixed-template `H`-coloring examples.

These examples expose the common 2-coloring and 3-coloring templates as
finite-domain CSP instances.  They are intentionally thin wrappers around the
generic `HColoring` theorem so generated artifacts can cite stable names.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace HColoringExamples

/-- The loopless complete graph on two vertices, as an undirected template. -/
def twoColorTemplate : ComplexityReduction.Combinatorics.Graph.GraphInput where
  vertices := 2
  edges := [(0, 1)]
  directed := false

/-- The loopless complete graph on three vertices, as an undirected template. -/
def threeColorTemplate : ComplexityReduction.Combinatorics.Graph.GraphInput where
  vertices := 3
  edges := [(0, 1), (0, 2), (1, 2)]
  directed := false

/-- Agent-facing descriptor for the loopless complete graph on two vertices. -/
def twoColorTemplateDescriptor : HColoring.TemplateDescriptor where
  name := "two_coloring_template"
  template := twoColorTemplate
  roles := ["finite_domain_csp", "graph_hom", "two_coloring", "worked_example"]
  notes :=
    [ "Loopless complete graph on two vertices."
    , "Semantic fixed-template CSP example only; no hardness claim is asserted." ]

/-- Agent-facing descriptor for the loopless complete graph on three vertices. -/
def threeColorTemplateDescriptor : HColoring.TemplateDescriptor where
  name := "three_coloring_template"
  template := threeColorTemplate
  roles := ["finite_domain_csp", "graph_hom", "three_coloring", "worked_example"]
  notes :=
    [ "Loopless complete graph on three vertices."
    , "Semantic fixed-template CSP example only; no hardness claim is asserted." ]

@[simp]
theorem twoColorTemplateDescriptor_vertexCount :
    twoColorTemplateDescriptor.vertexCount = 2 :=
  rfl

@[simp]
theorem twoColorTemplateDescriptor_edgeCount :
    twoColorTemplateDescriptor.edgeCount = 1 :=
  rfl

@[simp]
theorem threeColorTemplateDescriptor_vertexCount :
    threeColorTemplateDescriptor.vertexCount = 3 :=
  rfl

@[simp]
theorem threeColorTemplateDescriptor_edgeCount :
    threeColorTemplateDescriptor.edgeCount = 3 :=
  rfl

/-- CSP formula for graph homomorphism into the two-color template. -/
def twoColoringFormula (G : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    Formula (HColoring.templateLanguage twoColorTemplate) :=
  HColoring.graphHomFormula G twoColorTemplate

/-- CSP formula for graph homomorphism into the three-color template. -/
def threeColoringFormula (G : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    Formula (HColoring.templateLanguage threeColorTemplate) :=
  HColoring.graphHomFormula G threeColorTemplate

theorem twoColorable_iff_graphHom
    (G : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    HColoring.HColorable twoColorTemplate G ↔
      HColoring.GraphHom G twoColorTemplate :=
  HColoring.hColorable_iff_graphHom G twoColorTemplate

theorem threeColorable_iff_graphHom
    (G : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    HColoring.HColorable threeColorTemplate G ↔
      HColoring.GraphHom G threeColorTemplate :=
  HColoring.hColorable_iff_graphHom G threeColorTemplate

theorem twoColoringFormula_satisfiable_iff_graphHom
    (G : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    Formula.Satisfiable (twoColoringFormula G) ↔
      HColoring.GraphHom G twoColorTemplate :=
  HColoring.hColorable_iff_graphHom G twoColorTemplate

theorem threeColoringFormula_satisfiable_iff_graphHom
    (G : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    Formula.Satisfiable (threeColoringFormula G) ↔
      HColoring.GraphHom G threeColorTemplate :=
  HColoring.hColorable_iff_graphHom G threeColorTemplate

theorem twoColorTemplateDescriptor_formula_satisfiable_iff_graphHom
    (G : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    Formula.Satisfiable (twoColorTemplateDescriptor.formula G) ↔
      HColoring.GraphHom G twoColorTemplate := by
  simpa [twoColorTemplateDescriptor, HColoring.TemplateDescriptor.graphHom] using
    HColoring.TemplateDescriptor.formula_satisfiable_iff_graphHom
      twoColorTemplateDescriptor G

theorem threeColorTemplateDescriptor_formula_satisfiable_iff_graphHom
    (G : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    Formula.Satisfiable (threeColorTemplateDescriptor.formula G) ↔
      HColoring.GraphHom G threeColorTemplate := by
  simpa [threeColorTemplateDescriptor, HColoring.TemplateDescriptor.graphHom] using
    HColoring.TemplateDescriptor.formula_satisfiable_iff_graphHom
      threeColorTemplateDescriptor G

end HColoringExamples
end FiniteDomain
end CSP
end ComplexityReduction
