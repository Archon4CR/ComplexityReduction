/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.CSP.FiniteDomain.HColoring

/-!
Reusable fixed-template catalog entries for `H`-coloring.

This module adds theorem-bearing constructors for common finite graph templates
without asserting any Hell-Nesetril complexity classification.  The semantic
theorems are exactly the existing fixed-template graph-homomorphism/CSP
equivalence specialized to catalog descriptors.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace HColoring

/-- Template family tag for planner-visible `H`-coloring catalog entries. -/
inductive TemplateKind where
  | completeGraph (n : Nat)
  | cycle (n : Nat)
  | custom (name : String)
  deriving Repr

/-- Ordered list of loopless complete-graph edges, represented once per unordered pair. -/
def completeGraphEdges (n : Nat) : List (Nat × Nat) :=
  ((List.range n).product (List.range n)).filter fun e => e.1 < e.2

/-- Loopless complete graph template on `n` vertices. -/
def completeGraphTemplate (n : Nat) : ComplexityReduction.Combinatorics.Graph.GraphInput where
  vertices := n
  edges := completeGraphEdges n
  directed := false

/-- Cycle graph template with edges `i -> i+1 mod n`. -/
def cycleTemplate (n : Nat) : ComplexityReduction.Combinatorics.Graph.GraphInput where
  vertices := n
  edges := List.ofFn fun i : Fin n => (i.val, (i.val + 1) % n)
  directed := false

/-- The complete graph template has the requested vertex count. -/
@[simp]
theorem completeGraphTemplate_vertices (n : Nat) :
    (completeGraphTemplate n).vertices = n :=
  rfl

/-- The cycle template has the requested vertex count. -/
@[simp]
theorem cycleTemplate_vertices (n : Nat) :
    (cycleTemplate n).vertices = n :=
  rfl

/-- The cycle template has one listed edge per vertex index. -/
@[simp]
theorem cycleTemplate_edges_length (n : Nat) :
    (cycleTemplate n).edges.length = n := by
  simp [cycleTemplate]

/-- Complete-graph template edges are inside the vertex range. -/
theorem completeGraphTemplate_wellFormed (n : Nat) :
    ComplexityReduction.Combinatorics.Graph.WellFormed (completeGraphTemplate n) := by
  intro e he
  have hMem :
      e ∈ (List.range n).product (List.range n) ∧ e.1 < e.2 := by
    simpa [completeGraphTemplate, completeGraphEdges] using he
  rcases hMem with ⟨hProduct, _hlt⟩
  rcases List.mem_product.mp hProduct with ⟨hLeft, hRight⟩
  simp [ComplexityReduction.Combinatorics.Graph.EdgeWithinBounds] at hLeft hRight ⊢
  exact ⟨hLeft, hRight⟩

/-- Cycle-template edges are inside the vertex range. -/
theorem cycleTemplate_wellFormed (n : Nat) :
    ComplexityReduction.Combinatorics.Graph.WellFormed (cycleTemplate n) := by
  intro e he
  rcases List.mem_ofFn.mp (by simpa [cycleTemplate] using he) with ⟨i, rfl⟩
  have hn : 0 < n := by
    by_contra hzero
    have hZero : n = 0 := Nat.eq_zero_of_not_pos hzero
    have : i.val < 0 := by simpa [hZero] using i.isLt
    omega
  exact ⟨i.isLt, Nat.mod_lt _ hn⟩

/-- Descriptor for a loopless complete graph template. -/
def completeGraphTemplateDescriptor (n : Nat) : TemplateDescriptor where
  name := "complete_graph_" ++ toString n
  template := completeGraphTemplate n
  roles := ["finite_domain_csp", "graph_hom", "complete_graph_template"]
  notes :=
    [ "Loopless complete graph template constructor."
    , "Semantic fixed-template CSP route only; no H-coloring hardness theorem is asserted." ]

/-- Descriptor for a cycle graph template. -/
def cycleTemplateDescriptor (n : Nat) : TemplateDescriptor where
  name := "cycle_graph_" ++ toString n
  template := cycleTemplate n
  roles := ["finite_domain_csp", "graph_hom", "cycle_template"]
  notes :=
    [ "Cycle graph template constructor using row-order cyclic edges."
    , "Semantic fixed-template CSP route only; no H-coloring hardness theorem is asserted." ]

@[simp]
theorem completeGraphTemplateDescriptor_vertexCount (n : Nat) :
    (completeGraphTemplateDescriptor n).vertexCount = n :=
  rfl

@[simp]
theorem cycleTemplateDescriptor_vertexCount (n : Nat) :
    (cycleTemplateDescriptor n).vertexCount = n :=
  rfl

/-- Complete-graph descriptor formulas are exactly graph homomorphism into the template. -/
theorem completeGraphTemplateDescriptor_formula_satisfiable_iff_graphHom
    (n : Nat) (G : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    Formula.Satisfiable ((completeGraphTemplateDescriptor n).formula G) ↔
      (completeGraphTemplateDescriptor n).graphHom G :=
  TemplateDescriptor.formula_satisfiable_iff_graphHom (completeGraphTemplateDescriptor n) G

/-- Cycle descriptor formulas are exactly graph homomorphism into the template. -/
theorem cycleTemplateDescriptor_formula_satisfiable_iff_graphHom
    (n : Nat) (G : ComplexityReduction.Combinatorics.Graph.GraphInput) :
    Formula.Satisfiable ((cycleTemplateDescriptor n).formula G) ↔
      (cycleTemplateDescriptor n).graphHom G :=
  TemplateDescriptor.formula_satisfiable_iff_graphHom (cycleTemplateDescriptor n) G

/-- Planner-visible entry for a fixed `H`-coloring template. -/
structure TemplateCatalogEntry where
  kind : TemplateKind
  descriptor : TemplateDescriptor
  semanticTheorem : String
  generatorMayUseAsTheorem : Bool := true
  notes : List String := []
  deriving Repr

/-- Small reusable template catalog for generated graph-homomorphism artifacts. -/
def templateCatalog : List TemplateCatalogEntry :=
  [ { kind := TemplateKind.completeGraph 2
      descriptor := completeGraphTemplateDescriptor 2
      semanticTheorem :=
        "ComplexityReduction.CSP.FiniteDomain.HColoring.completeGraphTemplateDescriptor_formula_satisfiable_iff_graphHom"
      notes := ["Generalizes the existing two-coloring template descriptor."] }
  , { kind := TemplateKind.completeGraph 3
      descriptor := completeGraphTemplateDescriptor 3
      semanticTheorem :=
        "ComplexityReduction.CSP.FiniteDomain.HColoring.completeGraphTemplateDescriptor_formula_satisfiable_iff_graphHom"
      notes := ["Generalizes the existing three-coloring template descriptor."] }
  , { kind := TemplateKind.cycle 3
      descriptor := cycleTemplateDescriptor 3
      semanticTheorem :=
        "ComplexityReduction.CSP.FiniteDomain.HColoring.cycleTemplateDescriptor_formula_satisfiable_iff_graphHom"
      notes := ["Small cycle template smoke-test entry."] }
  , { kind := TemplateKind.cycle 4
      descriptor := cycleTemplateDescriptor 4
      semanticTheorem :=
        "ComplexityReduction.CSP.FiniteDomain.HColoring.cycleTemplateDescriptor_formula_satisfiable_iff_graphHom"
      notes := ["Even cycle template smoke-test entry."] } ]

@[simp]
theorem templateCatalog_length :
    templateCatalog.length = 4 :=
  rfl

end HColoring
end FiniteDomain
end CSP
end ComplexityReduction
