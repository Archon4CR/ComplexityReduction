/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.Combinatorics.Graph.BoundedDegree
import ComplexityReduction.Combinatorics.Graph.GadgetComposition

/-!
Lightweight planar-embedding metadata for graph gadget reductions.

This module deliberately does not prove topological planarity.  It records the
finite, list-based side conditions that planar gadget constructions need before
one attempts a certified crossover or face gadget.
-/

namespace ComplexityReduction
namespace Combinatorics
namespace Graph

/-- A vertex placement in an embedding descriptor. -/
structure VertexPlacement where
  vertex : Nat
  x : Int
  y : Int
  deriving Repr

/-- A graph incidence record used by embedding and face-boundary descriptors. -/
structure IncidenceRecord where
  source : Nat
  target : Nat
  edge : Nat × Nat
  deriving Repr

namespace IncidenceRecord

/-- The incidence record names a listed graph edge with matching endpoints. -/
def UsesGraph (rec : IncidenceRecord) (g : GraphInput) : Prop :=
  rec.edge ∈ g.edges ∧ rec.edge.1 = rec.source ∧ rec.edge.2 = rec.target

theorem edge_mem_of_usesGraph {rec : IncidenceRecord} {g : GraphInput}
    (h : rec.UsesGraph g) :
    rec.edge ∈ g.edges :=
  h.1

theorem source_eq_edge_left_of_usesGraph {rec : IncidenceRecord} {g : GraphInput}
    (h : rec.UsesGraph g) :
    rec.edge.1 = rec.source :=
  h.2.1

theorem target_eq_edge_right_of_usesGraph {rec : IncidenceRecord} {g : GraphInput}
    (h : rec.UsesGraph g) :
    rec.edge.2 = rec.target :=
  h.2.2

end IncidenceRecord

/-- A finite face boundary recorded as a cyclic list of graph vertices. -/
structure FaceBoundary where
  faceId : Nat
  boundary : List Nat
  deriving Repr

namespace FaceBoundary

/-- Every boundary vertex lies in the graph's declared vertex range. -/
def VerticesWithinBounds (face : FaceBoundary) (g : GraphInput) : Prop :=
  ∀ v ∈ face.boundary, v < g.vertices

end FaceBoundary

/--
Descriptor for the incidence graph of a variable-clause formula.

The graph has variables first and clauses second; each incidence `(v, c)` is
encoded as an undirected edge from `v` to `variableCount + c`.
-/
structure IncidenceGraphDescriptor where
  variableCount : Nat
  clauseCount : Nat
  incidences : List (Nat × Nat)
  deriving Repr

namespace IncidenceGraphDescriptor

/-- Every variable-clause incidence lies inside the declared ranges. -/
def IncidencesWithinBounds (I : IncidenceGraphDescriptor) : Prop :=
  ∀ inc ∈ I.incidences, inc.1 < I.variableCount ∧ inc.2 < I.clauseCount

/-- Interpret a variable-clause incidence descriptor as a graph input. -/
def toGraphInput (I : IncidenceGraphDescriptor) : GraphInput where
  vertices := I.variableCount + I.clauseCount
  edges := I.incidences.map fun inc => (inc.1, I.variableCount + inc.2)
  directed := false

/-- Incidence bounds imply well-formedness of the associated graph input. -/
theorem toGraphInput_wellFormed (I : IncidenceGraphDescriptor)
    (h : I.IncidencesWithinBounds) :
    WellFormed I.toGraphInput := by
  intro e he
  rcases List.mem_map.mp he with ⟨inc, hinc, rfl⟩
  have hBounds := h inc hinc
  change
    inc.1 < I.variableCount + I.clauseCount ∧
      I.variableCount + inc.2 < I.variableCount + I.clauseCount
  constructor
  · omega
  · omega

end IncidenceGraphDescriptor

/--
Finite embedding descriptor for future planar gadget routes.

`isPlanarLike` is intentionally metadata supplied by a construction; the local
library only verifies list-side consistency of placements, incidences, faces,
edges, and degree bounds.
-/
structure PlanarEmbeddingDescriptor where
  graph : GraphInput
  vertexPlacements : List VertexPlacement
  incidences : List IncidenceRecord
  faces : List FaceBoundary
  isPlanarLike : Prop := True

/-- Every listed vertex placement points at a declared graph vertex. -/
def EmbeddingVerticesWithinBounds (E : PlanarEmbeddingDescriptor) : Prop :=
  ∀ p ∈ E.vertexPlacements, p.vertex < E.graph.vertices

/-- Every incidence record names a listed edge of the embedded graph. -/
def EmbeddingUsesGraph (E : PlanarEmbeddingDescriptor) : Prop :=
  ∀ rec ∈ E.incidences, rec.UsesGraph E.graph

/-- Every graph edge lies inside the declared vertex range. -/
def EmbeddingEdgesWithinBounds (E : PlanarEmbeddingDescriptor) : Prop :=
  WellFormed E.graph

/-- Every recorded face boundary uses declared graph vertices. -/
def EmbeddingFaceBoundariesWithinBounds (E : PlanarEmbeddingDescriptor) : Prop :=
  ∀ face ∈ E.faces, face.VerticesWithinBounds E.graph

/-- The embedded graph satisfies a uniform degree bound. -/
def EmbeddingDegreeBounded (E : PlanarEmbeddingDescriptor) (k : Nat) : Prop :=
  IsDegreeBounded E.graph k

/-- The embedded graph is subcubic. -/
def EmbeddingSubcubic (E : PlanarEmbeddingDescriptor) : Prop :=
  EmbeddingDegreeBounded E 3

theorem embeddingEdgesWithinBounds_iff_wellFormed (E : PlanarEmbeddingDescriptor) :
    EmbeddingEdgesWithinBounds E ↔ WellFormed E.graph :=
  Iff.rfl

theorem embeddingDegreeBounded_iff_isDegreeBounded
    (E : PlanarEmbeddingDescriptor) (k : Nat) :
    EmbeddingDegreeBounded E k ↔ IsDegreeBounded E.graph k :=
  Iff.rfl

theorem embeddingDegreeBounded_iff_maxDegree_le
    (E : PlanarEmbeddingDescriptor) (k : Nat) :
    EmbeddingDegreeBounded E k ↔ maxDegree E.graph ≤ k :=
  isDegreeBounded_iff_maxDegree_le E.graph k

theorem embeddingSubcubic_iff_maxDegree_le_three (E : PlanarEmbeddingDescriptor) :
    EmbeddingSubcubic E ↔ maxDegree E.graph ≤ 3 := by
  simpa [EmbeddingSubcubic] using embeddingDegreeBounded_iff_maxDegree_le E 3

/-- If incidence metadata uses graph edges, well-formedness bounds its source and target. -/
theorem incidenceRecord_bounds_of_embeddingEdgesWithinBounds
    {E : PlanarEmbeddingDescriptor} {rec : IncidenceRecord}
    (hEdges : EmbeddingEdgesWithinBounds E)
    (hUses : EmbeddingUsesGraph E)
    (hrec : rec ∈ E.incidences) :
    rec.source < E.graph.vertices ∧ rec.target < E.graph.vertices := by
  have hUse := hUses rec hrec
  have hEdgeBounds := hEdges rec.edge (IncidenceRecord.edge_mem_of_usesGraph hUse)
  have hSource := IncidenceRecord.source_eq_edge_left_of_usesGraph hUse
  have hTarget := IncidenceRecord.target_eq_edge_right_of_usesGraph hUse
  constructor
  · simpa [hSource] using hEdgeBounds.1
  · simpa [hTarget] using hEdgeBounds.2

/-- Face-boundary bounds can be unpacked for any listed face and vertex. -/
theorem faceBoundary_vertex_lt_of_mem
    {E : PlanarEmbeddingDescriptor} {face : FaceBoundary} {v : Nat}
    (hFaces : EmbeddingFaceBoundariesWithinBounds E)
    (hface : face ∈ E.faces)
    (hv : v ∈ face.boundary) :
    v < E.graph.vertices :=
  hFaces face hface v hv

/-- Vertex-placement bounds can be unpacked for any listed placement. -/
theorem vertexPlacement_vertex_lt_of_mem
    {E : PlanarEmbeddingDescriptor} {p : VertexPlacement}
    (hVertices : EmbeddingVerticesWithinBounds E)
    (hp : p ∈ E.vertexPlacements) :
    p.vertex < E.graph.vertices :=
  hVertices p hp

end Graph
end Combinatorics
end ComplexityReduction
