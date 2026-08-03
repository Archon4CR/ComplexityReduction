/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.Combinatorics.Graph.PlanarEmbedding

/-!
Syntactic graph gadget replacement skeleton.

This module provides finite, list-based vertex allocation and edge mapping for a
single graph gadget shape.  It deliberately proves only construction
well-formedness and endpoint bounds; concrete gadget truth-table preservation,
graph-homomorphism preservation, and topological planarity are separate layers.
-/

namespace ComplexityReduction
namespace Combinatorics
namespace Graph
namespace Gadget

/--
One local gadget replacement specification.

Terminals of `shape` are mapped to existing vertices of a host graph.  Internal
vertices of `shape` are mapped to consecutive vertices starting at
`internalBase`.
-/
structure ReplacementSpec where
  shape : GadgetShape
  terminalMap : Fin shape.terminalCount → Nat
  internalBase : Nat

namespace ReplacementSpec

/-- Host-graph bound for mapped terminal vertices. -/
def MapsTerminalsWithinBounds (spec : ReplacementSpec) (G : GraphInput) : Prop :=
  ∀ i : Fin spec.shape.terminalCount, spec.terminalMap i < G.vertices

/-- Internal vertices are allocated at or after the host graph's vertex range. -/
def InternalsFreshFor (spec : ReplacementSpec) (G : GraphInput) : Prop :=
  G.vertices ≤ spec.internalBase

/-- Vertex count after attaching the replacement shape. -/
def replacementVertexCount (spec : ReplacementSpec) (G : GraphInput) : Nat :=
  max G.vertices (spec.internalBase + spec.shape.internalCount)

/-- Host-graph bound for mapped internal vertices in the replacement graph. -/
def MapsInternalsWithinBounds (spec : ReplacementSpec) (G : GraphInput) : Prop :=
  ∀ i : Fin spec.shape.internalCount,
    spec.internalBase + i.val < spec.replacementVertexCount G

/-- Map a gadget-local vertex into the replacement graph. -/
def mapVertex (spec : ReplacementSpec) (v : Nat) : Nat :=
  if h : v < spec.shape.terminalCount then
    spec.terminalMap ⟨v, h⟩
  else
    spec.internalBase + (v - spec.shape.terminalCount)

/-- Map a gadget-local edge into the replacement graph. -/
def mapEdge (spec : ReplacementSpec) (e : Nat × Nat) : Nat × Nat :=
  (spec.mapVertex e.1, spec.mapVertex e.2)

@[simp]
theorem mapVertex_terminal (spec : ReplacementSpec)
    (i : Fin spec.shape.terminalCount) :
    spec.mapVertex (spec.shape.terminalVertex i) = spec.terminalMap i := by
  dsimp [mapVertex, GadgetShape.terminalVertex]
  simp

@[simp]
theorem mapVertex_internal (spec : ReplacementSpec)
    (i : Fin spec.shape.internalCount) :
    spec.mapVertex (spec.shape.internalVertex i) = spec.internalBase + i.val := by
  have hnot : ¬ spec.shape.terminalCount + i.val < spec.shape.terminalCount := by
    omega
  simp [mapVertex, GadgetShape.internalVertex, hnot]

/-- Internal allocation is always below the replacement vertex count. -/
theorem mapsInternalsWithinBounds (spec : ReplacementSpec) (G : GraphInput) :
    spec.MapsInternalsWithinBounds G := by
  intro i
  exact lt_of_lt_of_le
    (Nat.add_lt_add_left i.isLt spec.internalBase)
    (Nat.le_max_right G.vertices (spec.internalBase + spec.shape.internalCount))

/-- A mapped terminal vertex is below the replacement graph vertex count. -/
theorem mapTerminal_lt_replacementVertexCount {spec : ReplacementSpec}
    {G : GraphInput} (hTerm : spec.MapsTerminalsWithinBounds G)
    (i : Fin spec.shape.terminalCount) :
    spec.mapVertex (spec.shape.terminalVertex i) < spec.replacementVertexCount G := by
  exact lt_of_lt_of_le (by simpa using hTerm i)
    (Nat.le_max_left G.vertices (spec.internalBase + spec.shape.internalCount))

/-- A mapped internal vertex is below the replacement graph vertex count. -/
theorem mapInternal_lt_replacementVertexCount (spec : ReplacementSpec)
    (G : GraphInput) (i : Fin spec.shape.internalCount) :
    spec.mapVertex (spec.shape.internalVertex i) < spec.replacementVertexCount G := by
  simpa using spec.mapsInternalsWithinBounds G i

/-- Any in-shape vertex maps below the replacement graph vertex count. -/
theorem mapVertex_lt_replacementVertexCount_of_shape_vertex_lt
    {spec : ReplacementSpec} {G : GraphInput}
    (hTerm : spec.MapsTerminalsWithinBounds G) {v : Nat}
    (hv : v < spec.shape.vertexCount) :
    spec.mapVertex v < spec.replacementVertexCount G := by
  by_cases htv : v < spec.shape.terminalCount
  · exact lt_of_lt_of_le (by simpa [mapVertex, htv] using hTerm ⟨v, htv⟩)
      (Nat.le_max_left G.vertices (spec.internalBase + spec.shape.internalCount))
  · have hvInternal : v - spec.shape.terminalCount < spec.shape.internalCount := by
      dsimp [GadgetShape.vertexCount] at hv
      omega
    have hMapped :
        spec.mapVertex v < spec.internalBase + spec.shape.internalCount := by
      simpa [mapVertex, htv] using Nat.add_lt_add_left hvInternal spec.internalBase
    exact lt_of_lt_of_le hMapped
      (Nat.le_max_right G.vertices (spec.internalBase + spec.shape.internalCount))

/-- A mapped gadget edge has endpoints below the replacement graph vertex count. -/
theorem mapEdgeWithinBounds_of_shapeEdge {spec : ReplacementSpec} {G : GraphInput}
    (hTerm : spec.MapsTerminalsWithinBounds G) {e : Nat × Nat}
    (hEdge : EdgeWithinBounds spec.shape.toGraphInput e) :
    e |> spec.mapEdge |> fun e' =>
      e'.1 < spec.replacementVertexCount G ∧ e'.2 < spec.replacementVertexCount G := by
  exact
    ⟨mapVertex_lt_replacementVertexCount_of_shape_vertex_lt
        (spec := spec) (G := G) hTerm hEdge.1,
      mapVertex_lt_replacementVertexCount_of_shape_vertex_lt
        (spec := spec) (G := G) hTerm hEdge.2⟩

end ReplacementSpec

/-- Replace one local site syntactically by appending the mapped gadget edges. -/
def replaceOne (G : GraphInput) (spec : ReplacementSpec) : GraphInput where
  vertices := spec.replacementVertexCount G
  edges := G.edges ++ spec.shape.edges.map spec.mapEdge
  directed := G.directed || spec.shape.directed

@[simp]
theorem replaceOne_vertices (G : GraphInput) (spec : ReplacementSpec) :
    (replaceOne G spec).vertices = spec.replacementVertexCount G :=
  rfl

@[simp]
theorem replaceOne_edges (G : GraphInput) (spec : ReplacementSpec) :
    (replaceOne G spec).edges = G.edges ++ spec.shape.edges.map spec.mapEdge :=
  rfl

/-- Old host edges remain endpoint-bounded after replacement. -/
theorem replaceOne_baseEdgeWithinBounds {G : GraphInput} {spec : ReplacementSpec}
    (hG : WellFormed G) {e : Nat × Nat} (he : e ∈ G.edges) :
    EdgeWithinBounds (replaceOne G spec) e := by
  have hBounds := hG e he
  exact
    ⟨lt_of_lt_of_le hBounds.1
        (Nat.le_max_left G.vertices (spec.internalBase + spec.shape.internalCount)),
      lt_of_lt_of_le hBounds.2
        (Nat.le_max_left G.vertices (spec.internalBase + spec.shape.internalCount))⟩

/-- Mapped gadget edges are endpoint-bounded after replacement. -/
theorem replaceOne_mappedEdgeWithinBounds {G : GraphInput} {spec : ReplacementSpec}
    (hTerm : spec.MapsTerminalsWithinBounds G)
    (hShape : WellFormed spec.shape.toGraphInput)
    {e : Nat × Nat} (he : e ∈ spec.shape.edges) :
    EdgeWithinBounds (replaceOne G spec) (spec.mapEdge e) := by
  have hEdge := hShape e he
  exact spec.mapEdgeWithinBounds_of_shapeEdge (G := G) hTerm hEdge

/-- Every edge in the replacement graph is endpoint-bounded. -/
theorem replaceOne_edgeWithinBounds {G : GraphInput} {spec : ReplacementSpec}
    (hG : WellFormed G) (hTerm : spec.MapsTerminalsWithinBounds G)
    (hShape : WellFormed spec.shape.toGraphInput)
    {e : Nat × Nat} (he : e ∈ (replaceOne G spec).edges) :
    EdgeWithinBounds (replaceOne G spec) e := by
  rw [replaceOne_edges] at he
  rcases List.mem_append.mp he with heBase | heMapped
  · exact replaceOne_baseEdgeWithinBounds (G := G) (spec := spec) hG heBase
  · rcases List.mem_map.mp heMapped with ⟨shapeEdge, hShapeEdge, rfl⟩
    exact replaceOne_mappedEdgeWithinBounds (G := G) (spec := spec) hTerm hShape hShapeEdge

/-- Well-formedness of the syntactic one-gadget replacement graph. -/
theorem replaceOne_wellFormed {G : GraphInput} {spec : ReplacementSpec}
    (hG : WellFormed G) (hTerm : spec.MapsTerminalsWithinBounds G)
    (hShape : WellFormed spec.shape.toGraphInput) :
    WellFormed (replaceOne G spec) := by
  intro e he
  exact replaceOne_edgeWithinBounds (G := G) (spec := spec) hG hTerm hShape he

/-- The replacement graph vertex count is the explicit max allocation bound. -/
theorem replaceOne_vertexCount (G : GraphInput) (spec : ReplacementSpec) :
    (replaceOne G spec).vertices =
      max G.vertices (spec.internalBase + spec.shape.internalCount) :=
  rfl

/-- Mapped terminal vertices are vertices of the replacement graph. -/
theorem replaceOne_terminal_mem_vertices {G : GraphInput} {spec : ReplacementSpec}
    (hTerm : spec.MapsTerminalsWithinBounds G) (i : Fin spec.shape.terminalCount) :
    spec.mapVertex (spec.shape.terminalVertex i) < (replaceOne G spec).vertices := by
  simpa [replaceOne] using
    spec.mapTerminal_lt_replacementVertexCount (G := G) hTerm i

/-- Mapped internal vertices are vertices of the replacement graph. -/
theorem replaceOne_internal_mem_vertices (G : GraphInput) (spec : ReplacementSpec)
    (i : Fin spec.shape.internalCount) :
    spec.mapVertex (spec.shape.internalVertex i) < (replaceOne G spec).vertices := by
  simpa [replaceOne] using
    spec.mapInternal_lt_replacementVertexCount G i

end Gadget
end Graph
end Combinatorics
end ComplexityReduction
