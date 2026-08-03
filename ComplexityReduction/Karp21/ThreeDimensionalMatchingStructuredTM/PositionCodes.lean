/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.Support
import ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute
import ComplexityReduction.Karp21.Partition.StructuredTM.Arithmetic

/-!
Executable membership-position code helpers for the compact
Exact-Cover-to-3-Dimensional-Matching route.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactPositionCodeInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat EncodedType.nat)

def compactPositionCodeFromCounts (p : Nat × Nat × Nat) : Nat :=
  p.2.2 * p.1 + p.2.1

theorem compactPositionCodeFromCounts_eq
    (I : ExactCoverInput) (x j : Nat) :
    compactPositionCodeFromCounts (I.system.universeSize, x, j) =
      compactPositionCode I x j := by
  rfl

theorem compactPositionCodeFromCounts_tm_polytime :
    TMPolyTimeMap
      compactPositionCodeInputEncodedType
      EncodedType.nat
      compactPositionCodeFromCounts := by
  let X := compactPositionCodeInputEncodedType
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat × Nat => p.1) := by
    simpa [X, compactPositionCodeInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat × Nat => p.2) := by
    simpa [X, compactPositionCodeInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat × Nat => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat × Nat => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hMulInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat × Nat => (p.2.2, p.1)) :=
    TMPolyTimeMap.prod_mk hJ hUniverse
  have hMul : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × Nat × Nat => p.2.2 * p.1) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_mul hMulInput
    simpa [Function.comp, X] using hComp
  have hAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : Nat × Nat × Nat => (p.2.2 * p.1, p.2.1)) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk hMul hX
  have hAdd := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
  simpa [Function.comp, compactPositionCodeFromCounts, X, natAddInputEncodedType]
    using hAdd

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
