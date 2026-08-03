/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Combinatorics.Graph.Gadget

/-!
Composition helpers for graph gadget transformations.

The core gadget interface records semantic preservation predicates for graph
homomorphism and `H`-colorability.  This module proves that those predicates are
closed under ordinary function composition of graph transformations.
-/

namespace ComplexityReduction
namespace Combinatorics
namespace Graph
namespace Gadget

namespace GraphTransform

/-- Compose two graph transformations, applying `before` first and `after` second. -/
def comp (after before : GraphTransform) : GraphTransform where
  name := after.name ++ "_after_" ++ before.name
  map := fun G => after.map (before.map G)

@[simp]
theorem comp_map (after before : GraphTransform) (G : GraphInput) :
    (after.comp before).map G = after.map (before.map G) :=
  rfl

@[simp]
theorem identity_comp_map (T : GraphTransform) (G : GraphInput) :
    (identityTransform.comp T).map G = T.map G :=
  rfl

@[simp]
theorem comp_identity_map (T : GraphTransform) (G : GraphInput) :
    (T.comp identityTransform).map G = T.map G :=
  rfl

/-- Associativity of transformation composition at the map level. -/
theorem comp_assoc_map (T₃ T₂ T₁ : GraphTransform) (G : GraphInput) :
    (T₃.comp (T₂.comp T₁)).map G = ((T₃.comp T₂).comp T₁).map G :=
  rfl

/-- Graph-homomorphism preservation is closed under graph-transform composition. -/
theorem PreservesGraphHom.comp {after before : GraphTransform}
    (hAfter : after.PreservesGraphHom) (hBefore : before.PreservesGraphHom) :
    (after.comp before).PreservesGraphHom := by
  intro G H
  exact (hAfter (before.map G) H).trans (hBefore G H)

/-- `H`-colorability preservation is closed under graph-transform composition. -/
theorem PreservesHColorable.comp {after before : GraphTransform}
    (hAfter : after.PreservesHColorable) (hBefore : before.PreservesHColorable) :
    (after.comp before).PreservesHColorable := by
  intro G H
  exact (hAfter (before.map G) H).trans (hBefore G H)

end GraphTransform
end Gadget
end Graph
end Combinatorics
end ComplexityReduction
