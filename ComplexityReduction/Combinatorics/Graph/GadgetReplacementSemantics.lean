/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Combinatorics.Graph.PlanarGadgets

/-!
Proof-carrying semantics for one-site graph gadget replacement.

`GadgetReplacement` builds the replacement graph and proves endpoint bounds.
This module adds a parametric semantic certificate: callers supply the host and
replacement predicates together with local soundness/completeness, and the
wrapper exposes standard theorem names for generated reductions.  No concrete
crossover, coloring, planarity, or hardness theorem is asserted here.
-/

namespace ComplexityReduction
namespace Combinatorics
namespace Graph
namespace Gadget

/-- Assignment of semantic values to the terminal vertices of a gadget shape. -/
abbrev TerminalAssignment (shape : GadgetShape) (Value : Type) : Type :=
  Fin shape.terminalCount → Value

/-- Predicate on a terminal assignment of a gadget shape. -/
abbrev ShapePredicate (shape : GadgetShape) (Value : Type) : Type :=
  TerminalAssignment shape Value → Prop

/-- Pair of graph-level predicates related by a local replacement certificate. -/
structure ReplacementSemantics where
  hostPredicate : GraphInput → Prop
  replacementPredicate : GraphInput → Prop

/--
Local proof-carrying certificate for one syntactic replacement.

The semantic predicates are intentionally parametric.  The certificate also
stores the standard syntactic side conditions needed to recover well-formedness
of the replacement graph.
-/
structure LocalReplacementCertificate (G : GraphInput) (spec : ReplacementSpec) where
  semantics : ReplacementSemantics
  hostWellFormed : WellFormed G
  terminalsWithinBounds : spec.MapsTerminalsWithinBounds G
  shapeWellFormed : WellFormed spec.shape.toGraphInput
  sound :
    semantics.replacementPredicate (replaceOne G spec) →
      semantics.hostPredicate G
  complete :
    semantics.hostPredicate G →
      semantics.replacementPredicate (replaceOne G spec)
  notes : List String := []

/-- The semantic soundness direction packaged by a local replacement certificate. -/
theorem replaceOne_semanticSound {G : GraphInput} {spec : ReplacementSpec}
    (cert : LocalReplacementCertificate G spec) :
    cert.semantics.replacementPredicate (replaceOne G spec) →
      cert.semantics.hostPredicate G :=
  cert.sound

/-- The semantic completeness direction packaged by a local replacement certificate. -/
theorem replaceOne_semanticComplete {G : GraphInput} {spec : ReplacementSpec}
    (cert : LocalReplacementCertificate G spec) :
    cert.semantics.hostPredicate G →
      cert.semantics.replacementPredicate (replaceOne G spec) :=
  cert.complete

/-- A local replacement certificate gives an iff between host and replacement predicates. -/
theorem replaceOne_semanticIff {G : GraphInput} {spec : ReplacementSpec}
    (cert : LocalReplacementCertificate G spec) :
    cert.semantics.replacementPredicate (replaceOne G spec) ↔
      cert.semantics.hostPredicate G :=
  ⟨cert.sound, cert.complete⟩

/-- The replacement graph in a local semantic certificate is well-formed. -/
theorem replaceOne_semanticWellFormed {G : GraphInput} {spec : ReplacementSpec}
    (cert : LocalReplacementCertificate G spec) :
    WellFormed (replaceOne G spec) :=
  replaceOne_wellFormed cert.hostWellFormed cert.terminalsWithinBounds cert.shapeWellFormed

end Gadget

namespace PlanarGadgetDescriptor

/--
Turn a planar gadget descriptor into a one-site semantic replacement
certificate once the caller supplies the semantic proof obligations.
-/
def toLocalReplacementCertificate
    (D : PlanarGadgetDescriptor) (G : GraphInput)
    (semantics : Gadget.ReplacementSemantics)
    (hG : WellFormed G)
    (hTerm : D.MapsTerminalsWithinHost G)
    (hShape : WellFormed D.shape.toGraphInput)
    (sound :
      semantics.replacementPredicate (Gadget.replaceOne G D.toReplacementSpec) →
        semantics.hostPredicate G)
    (complete :
      semantics.hostPredicate G →
        semantics.replacementPredicate (Gadget.replaceOne G D.toReplacementSpec))
    (notes : List String := []) :
    Gadget.LocalReplacementCertificate G D.toReplacementSpec where
  semantics := semantics
  hostWellFormed := hG
  terminalsWithinBounds := D.toReplacementSpec_mapsTerminalsWithinBounds hTerm
  shapeWellFormed := hShape
  sound := sound
  complete := complete
  notes := notes

end PlanarGadgetDescriptor
end Graph
end Combinatorics
end ComplexityReduction
