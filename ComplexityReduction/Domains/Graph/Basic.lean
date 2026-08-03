/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Templates

namespace ComplexityReduction

namespace Domains

namespace Graph

/-- A tiny graph format: number of vertices and a list of directed edges. -/
structure SimpleGraphInput where
  vertices : Nat
  edges : List (Nat × Nat)
  deriving Repr

/-- Encoding for edge pairs using the generic product encoding. -/
def EdgeEnc : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

/-- Encoding for edge lists. -/
def EdgeListEnc : EncodedType :=
  EncodedType.list EdgeEnc

/-- Encoding for the toy graph input. -/
def GraphEnc : EncodedType where
  Carrier := SimpleGraphInput
  Symbol := Option (Bool ⊕ EdgeListEnc.Symbol)
  finite_symbol := inferInstance
  encode := fun g =>
    (EncodedType.nat.encode g.vertices).map
      (fun b : Bool => (some (Sum.inl b) : Option (Bool ⊕ EdgeListEnc.Symbol))) ++
      [none] ++
      (EdgeListEnc.encode g.edges).map
        (fun s : EdgeListEnc.Symbol => (some (Sum.inr s) : Option (Bool ⊕ EdgeListEnc.Symbol)))

/-- Toy graph predicate: the encoded graph has no edges. -/
def edgeFree (g : SimpleGraphInput) : Prop :=
  g.edges = []

/-- Alias predicate used to exercise the same subset-lifting template off the SAT domain. -/
def edgeFreeAlias (g : SimpleGraphInput) : Prop :=
  edgeFree g

/-- Toy graph source problem. -/
def EdgeFreeProblem : EncodedDecisionProblem where
  Instance := GraphEnc
  isYes := edgeFree

/-- Toy graph target problem. -/
def EdgeFreeAliasProblem : EncodedDecisionProblem where
  Instance := GraphEnc
  isYes := edgeFreeAlias

theorem edgeFree_iff_alias (g : SimpleGraphInput) :
    edgeFree g ↔ edgeFreeAlias g :=
  Iff.rfl

/-- Benchmark: the same subset lifting template used for a non-SAT domain. -/
def edgeFreeSubsetLift :
    LogReductionCert EdgeFreeProblem EdgeFreeAliasProblem := by
  change LogReductionCert
    ({ Instance := GraphEnc, isYes := edgeFree } : EncodedDecisionProblem)
    ({ Instance := GraphEnc, isYes := edgeFreeAlias } : EncodedDecisionProblem)
  exact Templates.logSubsetLift (X := GraphEnc) edgeFree edgeFreeAlias edgeFree_iff_alias

/-- Toy block template mapping each edge to a fixed empty block. -/
def edgeEmptyBlock : Templates.BlockTemplate EdgeEnc EdgeEnc where
  blockOf := fun _ => []
  block_costed :=
    CostedPolyTimeMap.const_map (X := EdgeEnc) (Y := EncodedType.list EdgeEnc)
      ([] : List (Nat × Nat))

end Graph

end Domains

end ComplexityReduction
