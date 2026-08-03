/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Combinatorics.Graph.GadgetReplacement

/-!
Planar gadget descriptor consistency layer.

This module connects finite planar-embedding metadata with the syntactic
`Gadget.ReplacementSpec` interface.  It proves only list-level consistency:
embedding edge use, face-boundary bounds, terminal boundary references, and
terminal-map bounds.  It does not prove topological planarity or any concrete
crossover/gadget truth-table correctness.
-/

namespace ComplexityReduction
namespace Combinatorics
namespace Graph

/-- Descriptor for a graph gadget together with finite embedding metadata. -/
structure PlanarGadgetDescriptor where
  shape : Gadget.GadgetShape
  embedding : PlanarEmbeddingDescriptor
  terminals : List Nat
  terminalMap : Fin shape.terminalCount → Nat
  internalBase : Nat

namespace PlanarGadgetDescriptor

/-- The embedding graph is exactly the graph view of the gadget shape. -/
def EmbeddingGraphMatchesShape (D : PlanarGadgetDescriptor) : Prop :=
  D.embedding.graph = D.shape.toGraphInput

/-- Every incidence record in the embedding names a graph edge of the gadget shape. -/
def UsesOnlyGraphEdges (D : PlanarGadgetDescriptor) : Prop :=
  D.EmbeddingGraphMatchesShape ∧ EmbeddingUsesGraph D.embedding

/-- The listed descriptor terminals are exactly the terminal vertices of the shape. -/
def TerminalsMatchShape (D : PlanarGadgetDescriptor) : Prop :=
  D.terminals = List.ofFn D.shape.terminalVertex

/-- Every listed terminal appears on some recorded face boundary. -/
def TerminalsOnBoundary (D : PlanarGadgetDescriptor) : Prop :=
  ∀ v ∈ D.terminals, ∃ face ∈ D.embedding.faces, v ∈ face.boundary

/-- Face-boundary references are inside the embedding graph's vertex range. -/
def FaceBoundaryConsistent (D : PlanarGadgetDescriptor) : Prop :=
  EmbeddingFaceBoundariesWithinBounds D.embedding

/-- Terminal maps point inside a host graph. -/
def MapsTerminalsWithinHost (D : PlanarGadgetDescriptor) (G : GraphInput) : Prop :=
  ∀ i : Fin D.shape.terminalCount, D.terminalMap i < G.vertices

/-- Convert the descriptor to the syntactic one-gadget replacement interface. -/
def toReplacementSpec (D : PlanarGadgetDescriptor) : Gadget.ReplacementSpec where
  shape := D.shape
  terminalMap := D.terminalMap
  internalBase := D.internalBase

@[simp]
theorem toReplacementSpec_shape (D : PlanarGadgetDescriptor) :
    D.toReplacementSpec.shape = D.shape :=
  rfl

@[simp]
theorem toReplacementSpec_internalBase (D : PlanarGadgetDescriptor) :
    D.toReplacementSpec.internalBase = D.internalBase :=
  rfl

@[simp]
theorem toReplacementSpec_terminalMap (D : PlanarGadgetDescriptor)
    (i : Fin D.shape.terminalCount) :
    D.toReplacementSpec.terminalMap i = D.terminalMap i :=
  rfl

/-- Shape-matching terminal metadata has the declared terminal count. -/
theorem terminals_length_of_match {D : PlanarGadgetDescriptor}
    (h : D.TerminalsMatchShape) :
    D.terminals.length = D.shape.terminalCount := by
  rw [h]
  simp

/-- Shape terminals listed by `TerminalsMatchShape` are in the terminal list. -/
theorem terminalVertex_mem_terminals_of_match {D : PlanarGadgetDescriptor}
    (h : D.TerminalsMatchShape) (i : Fin D.shape.terminalCount) :
    D.shape.terminalVertex i ∈ D.terminals := by
  rw [h]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-- `UsesOnlyGraphEdges` exposes the existing embedding edge-use predicate. -/
theorem embeddingUsesGraph_of_usesOnlyGraphEdges {D : PlanarGadgetDescriptor}
    (h : D.UsesOnlyGraphEdges) :
    EmbeddingUsesGraph D.embedding :=
  h.2

/-- Shape well-formedness transfers to the embedding graph when the graphs match. -/
theorem embeddingEdgesWithinBounds_of_shape_wellFormed {D : PlanarGadgetDescriptor}
    (hUses : D.UsesOnlyGraphEdges)
    (hShape : WellFormed D.shape.toGraphInput) :
    EmbeddingEdgesWithinBounds D.embedding := by
  rw [EmbeddingEdgesWithinBounds, hUses.1]
  exact hShape

/-- Face-boundary consistency is exactly the existing embedding face-bound predicate. -/
theorem embeddingFaceBoundariesWithinBounds_of_consistent
    {D : PlanarGadgetDescriptor}
    (h : D.FaceBoundaryConsistent) :
    EmbeddingFaceBoundariesWithinBounds D.embedding :=
  h

/-- A terminal appearing on a consistent face boundary is within the embedding graph. -/
theorem terminal_lt_embedding_vertices_of_boundary
    {D : PlanarGadgetDescriptor} (hFaces : D.FaceBoundaryConsistent)
    (hBoundary : D.TerminalsOnBoundary) {v : Nat} (hv : v ∈ D.terminals) :
    v < D.embedding.graph.vertices := by
  rcases hBoundary v hv with ⟨face, hface, hvFace⟩
  exact faceBoundary_vertex_lt_of_mem hFaces hface hvFace

/-- If terminals match the shape and boundaries are consistent, every shape terminal is bounded. -/
theorem shape_terminal_lt_embedding_vertices_of_boundary
    {D : PlanarGadgetDescriptor} (hMatch : D.TerminalsMatchShape)
    (hFaces : D.FaceBoundaryConsistent) (hBoundary : D.TerminalsOnBoundary)
    (i : Fin D.shape.terminalCount) :
    D.shape.terminalVertex i < D.embedding.graph.vertices :=
  terminal_lt_embedding_vertices_of_boundary hFaces hBoundary
    (terminalVertex_mem_terminals_of_match hMatch i)

/-- The descriptor's replacement spec has terminal maps inside the host graph. -/
theorem toReplacementSpec_mapsTerminalsWithinBounds
    {D : PlanarGadgetDescriptor} {G : GraphInput}
    (h : D.MapsTerminalsWithinHost G) :
    D.toReplacementSpec.MapsTerminalsWithinBounds G := by
  intro i
  exact h i

/-- Internal vertices of the descriptor replacement are bounded by the replacement graph size. -/
theorem toReplacementSpec_mapsInternalsWithinBounds
    (D : PlanarGadgetDescriptor) (G : GraphInput) :
    D.toReplacementSpec.MapsInternalsWithinBounds G :=
  D.toReplacementSpec.mapsInternalsWithinBounds G

/-- Syntactic replacement well-formedness specialized to a planar gadget descriptor. -/
theorem replaceOne_wellFormed
    {D : PlanarGadgetDescriptor} {G : GraphInput}
    (hG : WellFormed G)
    (hTerm : D.MapsTerminalsWithinHost G)
    (hShape : WellFormed D.shape.toGraphInput) :
    WellFormed (Gadget.replaceOne G D.toReplacementSpec) :=
  Gadget.replaceOne_wellFormed hG
    (D.toReplacementSpec_mapsTerminalsWithinBounds hTerm) hShape

end PlanarGadgetDescriptor

end Graph
end Combinatorics
end ComplexityReduction
