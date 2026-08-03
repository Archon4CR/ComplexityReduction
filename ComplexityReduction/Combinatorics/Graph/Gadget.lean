/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.HColoring

/-!
Basic graph gadget interfaces.

This is a small semantic interface for graph transformations and gadget shapes.
Specialized planar or bounded-degree gadgets can later refine this layer with
additional invariants.
-/

namespace ComplexityReduction
namespace Combinatorics
namespace Graph
namespace Gadget

/-- A finite graph gadget shape with terminal vertices first, then internal vertices. -/
structure GadgetShape where
  terminalCount : Nat
  internalCount : Nat
  edges : List (Nat × Nat)
  directed : Bool := false
  deriving Repr

namespace GadgetShape

/-- Total number of vertices in the gadget. -/
def vertexCount (shape : GadgetShape) : Nat :=
  shape.terminalCount + shape.internalCount

/-- The `i`th terminal vertex. -/
def terminalVertex (shape : GadgetShape) (i : Fin shape.terminalCount) : Nat :=
  i.val

/-- The `i`th internal vertex. -/
def internalVertex (shape : GadgetShape) (i : Fin shape.internalCount) : Nat :=
  shape.terminalCount + i.val

/-- Interpret a gadget shape as a graph input. -/
def toGraphInput (shape : GadgetShape) : GraphInput where
  vertices := shape.vertexCount
  edges := shape.edges
  directed := shape.directed

theorem terminalVertex_lt_vertexCount (shape : GadgetShape)
    (i : Fin shape.terminalCount) :
    shape.terminalVertex i < shape.vertexCount := by
  dsimp [terminalVertex, vertexCount]
  omega

theorem internalVertex_lt_vertexCount (shape : GadgetShape)
    (i : Fin shape.internalCount) :
    shape.internalVertex i < shape.vertexCount := by
  dsimp [internalVertex, vertexCount]
  omega

end GadgetShape

/-- A graph transformation that can be used as a gadget replacement step. -/
structure GraphTransform where
  name : String
  map : GraphInput → GraphInput

namespace GraphTransform

/-- Preservation predicate for graph homomorphism into every fixed template. -/
def PreservesGraphHom (T : GraphTransform) : Prop :=
  ∀ G H : GraphInput,
    ComplexityReduction.CSP.FiniteDomain.HColoring.GraphHom (T.map G) H ↔
      ComplexityReduction.CSP.FiniteDomain.HColoring.GraphHom G H

/-- Preservation predicate for the finite-domain CSP `H`-coloring formulation. -/
def PreservesHColorable (T : GraphTransform) : Prop :=
  ∀ G H : GraphInput,
    ComplexityReduction.CSP.FiniteDomain.HColoring.HColorable H (T.map G) ↔
      ComplexityReduction.CSP.FiniteDomain.HColoring.HColorable H G

end GraphTransform

/-- The identity graph transformation, useful as a baseline gadget route. -/
def identityTransform : GraphTransform where
  name := "identity_graph_transform"
  map := id

theorem identityTransform_preservesGraphHom :
    identityTransform.PreservesGraphHom := by
  intro G H
  rfl

theorem identityTransform_preservesHColorable :
    identityTransform.PreservesHColorable := by
  intro G H
  rfl

end Gadget
end Graph
end Combinatorics
end ComplexityReduction
