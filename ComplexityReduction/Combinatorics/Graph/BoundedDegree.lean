/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.Combinatorics.Graph.Basic

/-!
Bounded-degree infrastructure for edge-list graph inputs.

The graph schema stores edges as a raw list of endpoint pairs.  The degree
notions here use undirected endpoint incidence, which is the invariant needed by
restricted graph gadget reductions such as subcubic reductions.
-/

namespace ComplexityReduction
namespace Combinatorics
namespace Graph

/-- A listed edge is incident to vertex `v` when `v` is either endpoint. -/
def EdgeIncident (v : Nat) (e : Nat × Nat) : Prop :=
  e.1 = v ∨ e.2 = v

instance instDecidableEdgeIncident (v : Nat) (e : Nat × Nat) :
    Decidable (EdgeIncident v e) := by
  unfold EdgeIncident
  infer_instance

/-- Undirected degree of a vertex, counted with multiplicity in the raw edge list. -/
def degree (g : GraphInput) (v : Nat) : Nat :=
  (g.edges.filter fun e => decide (EdgeIncident v e)).length

/-- Maximum undirected degree among vertices inside the declared vertex range. -/
noncomputable def maxDegree (g : GraphInput) : Nat :=
  (Finset.range g.vertices).sup (degree g)

/-- Every vertex in the declared vertex range has degree at most `k`. -/
def IsDegreeBounded (g : GraphInput) (k : Nat) : Prop :=
  ∀ v, v < g.vertices → degree g v ≤ k

/-- A graph is subcubic when every declared vertex has degree at most three. -/
def IsSubcubic (g : GraphInput) : Prop :=
  IsDegreeBounded g 3

@[simp]
theorem edgeIncident_left (u v : Nat) :
    EdgeIncident u (u, v) := by
  simp [EdgeIncident]

@[simp]
theorem edgeIncident_right (u v : Nat) :
    EdgeIncident v (u, v) := by
  simp [EdgeIncident]

/-- Degree is always bounded by the length of the raw edge list. -/
theorem degree_le_edges_length (g : GraphInput) (v : Nat) :
    degree g v ≤ g.edges.length := by
  unfold degree
  exact List.length_filter_le _ _

/-- A listed outgoing endpoint contributes a positive incident degree. -/
theorem degree_pos_of_left_edge_mem {g : GraphInput} {u v : Nat}
    (hEdge : (u, v) ∈ g.edges) :
    0 < degree g u := by
  unfold degree
  exact List.length_pos_of_mem
    (List.mem_filter.mpr ⟨hEdge, by simp [EdgeIncident]⟩)

/-- A listed incoming endpoint contributes a positive incident degree. -/
theorem degree_pos_of_right_edge_mem {g : GraphInput} {u v : Nat}
    (hEdge : (u, v) ∈ g.edges) :
    0 < degree g v := by
  unfold degree
  exact List.length_pos_of_mem
    (List.mem_filter.mpr ⟨hEdge, by simp [EdgeIncident]⟩)

/-- Well-formed directed edge membership gives both endpoint bounds. -/
theorem edgeWithinBounds_of_hasDirectedEdge {g : GraphInput} {u v : Nat}
    (hg : WellFormed g) (hEdge : HasDirectedEdge g u v) :
    u < g.vertices ∧ v < g.vertices :=
  hg (u, v) hEdge

/-- Well-formed undirected edge membership gives both endpoint bounds. -/
theorem edgeWithinBounds_of_hasUndirectedEdge {g : GraphInput} {u v : Nat}
    (hg : WellFormed g) (hEdge : HasUndirectedEdge g u v) :
    u < g.vertices ∧ v < g.vertices := by
  rcases hEdge with h | h
  · exact hg (u, v) h
  · exact And.symm (hg (v, u) h)

/-- Every in-range vertex degree is bounded by `maxDegree`. -/
theorem degree_le_maxDegree (g : GraphInput) {v : Nat} (hv : v < g.vertices) :
    degree g v ≤ maxDegree g := by
  classical
  unfold maxDegree
  exact Finset.le_sup (s := Finset.range g.vertices) (f := degree g)
    (b := v) (Finset.mem_range.mpr hv)

/-- The maximum degree is below any uniform degree bound. -/
theorem maxDegree_le_of_isDegreeBounded {g : GraphInput} {k : Nat}
    (h : IsDegreeBounded g k) :
    maxDegree g ≤ k := by
  classical
  unfold maxDegree
  exact Finset.sup_le fun v hv => h v (Finset.mem_range.mp hv)

/-- Uniform degree boundedness is equivalent to bounding `maxDegree`. -/
theorem isDegreeBounded_iff_maxDegree_le (g : GraphInput) (k : Nat) :
    IsDegreeBounded g k ↔ maxDegree g ≤ k := by
  constructor
  · exact maxDegree_le_of_isDegreeBounded
  · intro h v hv
    exact le_trans (degree_le_maxDegree g hv) h

/-- The canonical maximum degree bound. -/
theorem isDegreeBounded_maxDegree (g : GraphInput) :
    IsDegreeBounded g (maxDegree g) := by
  intro v hv
  exact degree_le_maxDegree g hv

/-- Subcubic graphs are exactly those whose maximum degree is at most three. -/
theorem isSubcubic_iff_maxDegree_le_three (g : GraphInput) :
    IsSubcubic g ↔ maxDegree g ≤ 3 := by
  simp [IsSubcubic, isDegreeBounded_iff_maxDegree_le]

end Graph
end Combinatorics
end ComplexityReduction
