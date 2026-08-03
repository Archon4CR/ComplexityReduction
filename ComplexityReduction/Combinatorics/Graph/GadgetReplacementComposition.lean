/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Combinatorics.Graph.GadgetReplacementSemantics

/-!
Composition of proof-carrying graph gadget replacements.

This module chains one-site replacement certificates for a single graph
predicate `P`.  It proves well-formedness transport and semantic equivalence by
induction over the chain, without introducing any concrete crossover,
planarity, or hardness theorem.
-/

namespace ComplexityReduction
namespace Combinatorics
namespace Graph
namespace Gadget

/--
A finite chain of one-site replacement certificates preserving a graph
predicate `P`.

Each local certificate may store its own predicate pair; the equalities require
both endpoints to be the global predicate `P`, which is what enables induction.
-/
inductive LocalReplacementChain (P : GraphInput -> Prop) : GraphInput -> GraphInput -> Type where
  | nil (G : GraphInput) : LocalReplacementChain P G G
  | cons (G H : GraphInput) (spec : ReplacementSpec)
      (cert : LocalReplacementCertificate G spec)
      (hostPredicate_eq : cert.semantics.hostPredicate = P)
      (replacementPredicate_eq : cert.semantics.replacementPredicate = P)
      (tail : LocalReplacementChain P (replaceOne G spec) H) :
      LocalReplacementChain P G H

/-- The target graph produced by a replacement chain. -/
def replaceChain {P : GraphInput -> Prop} {G H : GraphInput}
    (_chain : LocalReplacementChain P G H) : GraphInput :=
  H

/-- Well-formedness is preserved along a local replacement chain. -/
theorem replaceChain_wellFormed {P : GraphInput -> Prop} {G H : GraphInput}
    (chain : LocalReplacementChain P G H) (hG : WellFormed G) :
    WellFormed (replaceChain chain) := by
  induction chain with
  | nil G =>
      simpa [replaceChain] using hG
  | cons G H spec cert _hostPredicate_eq _replacementPredicate_eq tail ih =>
      have hMid : WellFormed (replaceOne G spec) :=
        replaceOne_semanticWellFormed cert
      exact ih hMid

/-- Semantic soundness is preserved along a local replacement chain. -/
theorem replaceChain_semanticSound {P : GraphInput -> Prop} {G H : GraphInput}
    (chain : LocalReplacementChain P G H) :
    P (replaceChain chain) -> P G := by
  induction chain with
  | nil G =>
      intro h
      simpa [replaceChain] using h
  | cons G H spec cert hostPredicate_eq replacementPredicate_eq tail ih =>
      intro hTarget
      have hMid : P (replaceChain tail) := by
        simpa [replaceChain] using hTarget
      have hMidSource : P (replaceOne G spec) :=
        ih hMid
      have hReplacement :
          cert.semantics.replacementPredicate (replaceOne G spec) := by
        rw [replacementPredicate_eq]
        exact hMidSource
      have hHost := cert.sound hReplacement
      rw [hostPredicate_eq] at hHost
      exact hHost

/-- Semantic completeness is preserved along a local replacement chain. -/
theorem replaceChain_semanticComplete {P : GraphInput -> Prop} {G H : GraphInput}
    (chain : LocalReplacementChain P G H) :
    P G -> P (replaceChain chain) := by
  induction chain with
  | nil G =>
      intro h
      simpa [replaceChain] using h
  | cons G H spec cert hostPredicate_eq replacementPredicate_eq tail ih =>
      intro hSource
      have hHost :
          cert.semantics.hostPredicate G := by
        rw [hostPredicate_eq]
        exact hSource
      have hReplacement := cert.complete hHost
      have hMid : P (replaceOne G spec) := by
        rw [replacementPredicate_eq] at hReplacement
        exact hReplacement
      exact ih hMid

/-- A local replacement chain gives semantic equivalence between final and initial graphs. -/
theorem replaceChain_semanticIff {P : GraphInput -> Prop} {G H : GraphInput}
    (chain : LocalReplacementChain P G H) :
    P (replaceChain chain) ↔ P G :=
  ⟨replaceChain_semanticSound chain, replaceChain_semanticComplete chain⟩

#check LocalReplacementChain
#check replaceChain
#check replaceChain_wellFormed
#check replaceChain_semanticSound
#check replaceChain_semanticComplete
#check replaceChain_semanticIff

end Gadget
end Graph
end Combinatorics
end ComplexityReduction
