/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.CSP.FiniteDomain.Basic
import ComplexityReduction.Combinatorics.Graph.Basic

/-!
`H`-coloring as a fixed-template finite-domain CSP.

Feder-Vardi describe graph coloring and `H`-coloring as fixed-template CSPs:
the input graph supplies variables and edge constraints, while the template graph
supplies the finite domain of colors and the binary edge relation.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace HColoring

/-- The binary edge relation of the fixed undirected template graph `H`. -/
def templateEdgeRel (H : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    Rel (Fin H.vertices) where
  arity := 2
  holds := fun t =>
    ComplexityReduction.Combinatorics.Graph.HasUndirectedEdge H (t 0).val (t 1).val

/-- The one-relation finite-domain CSP language associated to a fixed graph template `H`. -/
def templateLanguage (H : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    Language (Fin H.vertices) where
  finiteDomain := inferInstance
  Symbol := Unit
  finiteSymbol := inferInstance
  relationOf := fun _ => templateEdgeRel H

/-- Convert an input-graph edge into one binary template-edge constraint. -/
def edgeConstraint (H : ComplexityReduction.Combinatorics.Graph.GraphInput) (e : Nat × Nat) :
    Constraint (templateLanguage H) where
  symbol := ()
  vars := fun i => if i.val = 0 then e.1 else e.2

/-- The CSP formula induced by the edge list of an input graph. -/
def graphHomFormula
    (G H : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    Formula (templateLanguage H) :=
  G.edges.map (edgeConstraint H)

/-- Variable-value view of graph homomorphism into the fixed template `H`. -/
def GraphHom
    (G H : ComplexityReduction.Combinatorics.Graph.GraphInput) : Prop :=
  ∃ h : Assignment (Fin H.vertices),
    ∀ e ∈ G.edges,
      ComplexityReduction.Combinatorics.Graph.HasUndirectedEdge H (h e.1).val (h e.2).val

/-- `H`-coloring decision predicate, encoded as satisfiability of the fixed-template CSP. -/
def HColorable
    (H G : ComplexityReduction.Combinatorics.Graph.GraphInput) : Prop :=
  Formula.Satisfiable (graphHomFormula G H)

@[simp]
theorem edgeConstraint_satisfies_iff
    (H : ComplexityReduction.Combinatorics.Graph.GraphInput) (e : Nat × Nat)
    (a : Assignment (Fin H.vertices)) :
    Constraint.Satisfies (edgeConstraint H e) a ↔
      ComplexityReduction.Combinatorics.Graph.HasUndirectedEdge H (a e.1).val (a e.2).val := by
  simp [Constraint.Satisfies, Constraint.assignmentTuple, Rel.Holds, templateLanguage,
    templateEdgeRel, edgeConstraint]

theorem graphHomFormula_satisfies_iff
    (G H : ComplexityReduction.Combinatorics.Graph.GraphInput)
    (a : Assignment (Fin H.vertices)) :
    Formula.Satisfies (graphHomFormula G H) a ↔
      ∀ e ∈ G.edges,
        ComplexityReduction.Combinatorics.Graph.HasUndirectedEdge H
          (a e.1).val (a e.2).val := by
  constructor
  · intro h e he
    exact (edgeConstraint_satisfies_iff H e a).1
      (h (edgeConstraint H e) (List.mem_map.mpr ⟨e, he, rfl⟩))
  · intro h c hc
    rcases List.mem_map.mp hc with ⟨e, he, rfl⟩
    exact (edgeConstraint_satisfies_iff H e a).2 (h e he)

theorem hColorable_iff_graphHom
    (G H : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    HColorable H G ↔ GraphHom G H := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, (graphHomFormula_satisfies_iff G H a).1 h⟩
  · rintro ⟨a, h⟩
    exact ⟨a, (graphHomFormula_satisfies_iff G H a).2 h⟩

/--
Agent-facing descriptor for one fixed graph template.

This is a metadata wrapper around the already-proved fixed-template CSP
encoding.  It records names and planner notes without asserting any graph
homomorphism complexity classification.
-/
structure TemplateDescriptor where
  name : String
  template : ComplexityReduction.Combinatorics.Graph.GraphInput
  roles : List String
  notes : List String
  generatorMayUseAsTheorem : Bool := true
  deriving Repr

namespace TemplateDescriptor

/-- Number of vertices in the fixed template graph. -/
def vertexCount (T : TemplateDescriptor) : Nat :=
  T.template.vertices

/-- Number of listed template edges. -/
def edgeCount (T : TemplateDescriptor) : Nat :=
  T.template.edges.length

/-- Finite-domain CSP language induced by the fixed template graph. -/
def toLanguage (T : TemplateDescriptor) : Language (Fin T.template.vertices) :=
  templateLanguage T.template

/-- CSP formula for graph homomorphism into the descriptor's template. -/
def formula (T : TemplateDescriptor)
    (G : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    Formula T.toLanguage :=
  graphHomFormula G T.template

/-- Graph-homomorphism predicate for the descriptor's template. -/
def graphHom (T : TemplateDescriptor)
    (G : ComplexityReduction.Combinatorics.Graph.GraphInput) : Prop :=
  GraphHom G T.template

/-- H-colorability predicate for the descriptor's template. -/
def hColorable (T : TemplateDescriptor)
    (G : ComplexityReduction.Combinatorics.Graph.GraphInput) : Prop :=
  HColorable T.template G

/-- Descriptor formulas are the generic graph-homomorphism formulas. -/
theorem formula_eq_graphHomFormula (T : TemplateDescriptor)
    (G : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    T.formula G = graphHomFormula G T.template :=
  rfl

/-- Formula satisfaction for a template descriptor is edge preservation. -/
theorem formula_satisfies_iff (T : TemplateDescriptor)
    (G : ComplexityReduction.Combinatorics.Graph.GraphInput)
    (a : Assignment (Fin T.template.vertices)) :
    Formula.Satisfies (T.formula G) a ↔
      ∀ e ∈ G.edges,
        ComplexityReduction.Combinatorics.Graph.HasUndirectedEdge T.template
          (a e.1).val (a e.2).val := by
  simpa [formula, toLanguage] using graphHomFormula_satisfies_iff G T.template a

/-- Descriptor-level H-colorability is exactly graph homomorphism into the template. -/
theorem hColorable_iff_graphHom (T : TemplateDescriptor)
    (G : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    T.hColorable G ↔ T.graphHom G := by
  simpa [hColorable, graphHom] using
    ComplexityReduction.CSP.FiniteDomain.HColoring.hColorable_iff_graphHom G T.template

/-- Descriptor-level CSP satisfiability is exactly graph homomorphism into the template. -/
theorem formula_satisfiable_iff_graphHom (T : TemplateDescriptor)
    (G : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    Formula.Satisfiable (T.formula G) ↔ T.graphHom G := by
  simpa [formula, graphHom, toLanguage] using
    ComplexityReduction.CSP.FiniteDomain.HColoring.hColorable_iff_graphHom G T.template

end TemplateDescriptor

end HColoring
end FiniteDomain
end CSP
end ComplexityReduction
