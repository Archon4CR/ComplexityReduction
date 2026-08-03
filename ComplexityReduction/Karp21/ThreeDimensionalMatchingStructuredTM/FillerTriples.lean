/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.PositionCodes

/-!
Executable filler-triple helpers for the compact
Exact-Cover-to-3-Dimensional-Matching route.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactFillerTripleFromDataInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat)))

def compactFillerTripleFromData
    (p : Nat × Nat × Nat × Nat × Nat) : Nat × Nat × Nat :=
  let beta := p.2.1
  let j := p.2.2.1
  let x := p.2.2.2.1
  let next := p.2.2.2.2
  (beta, compactPositionCodeFromCounts (p.1, x, j),
    compactPositionCodeFromCounts (p.1, next, j))

theorem compactFillerTripleFromData_tm_polytime :
    TMPolyTimeMap
      compactFillerTripleFromDataInputEncodedType
      tripleStructuredEncodedType
      compactFillerTripleFromData := by
  let X := compactFillerTripleFromDataInputEncodedType
  have hUniverse : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × Nat × Nat × Nat × Nat => p.1) := by
    simpa [X, compactFillerTripleFromDataInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat EncodedType.nat)))
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat EncodedType.nat)))
        (fun p : Nat × Nat × Nat × Nat × Nat => p.2) := by
    simpa [X, compactFillerTripleFromDataInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat EncodedType.nat)))
  have hBeta : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × Nat × Nat × Nat × Nat => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat))
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hTail2 :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : Nat × Nat × Nat × Nat × Nat => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat))
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hJ : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × Nat × Nat × Nat × Nat => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hTail2
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat × Nat × Nat × Nat => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hTail2
    simpa [Function.comp, X] using hComp
  have hX : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × Nat × Nat × Nat × Nat => p.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPair
    simpa [Function.comp, X] using hComp
  have hNext : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × Nat × Nat × Nat × Nat => p.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPair
    simpa [Function.comp, X] using hComp
  have hCodeInput :
      TMPolyTimeMap X compactPositionCodeInputEncodedType
        (fun p : Nat × Nat × Nat × Nat × Nat => (p.1, p.2.2.2.1, p.2.2.1)) := by
    simpa [compactPositionCodeInputEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse (TMPolyTimeMap.prod_mk hX hJ)
  have hCode :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Nat × Nat × Nat × Nat × Nat =>
          compactPositionCodeFromCounts (p.1, p.2.2.2.1, p.2.2.1)) := by
    have hComp := TMPolyTimeMap.comp compactPositionCodeFromCounts_tm_polytime hCodeInput
    simpa [Function.comp, X] using hComp
  have hNextCodeInput :
      TMPolyTimeMap X compactPositionCodeInputEncodedType
        (fun p : Nat × Nat × Nat × Nat × Nat => (p.1, p.2.2.2.2, p.2.2.1)) := by
    simpa [compactPositionCodeInputEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse (TMPolyTimeMap.prod_mk hNext hJ)
  have hNextCode :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Nat × Nat × Nat × Nat × Nat =>
          compactPositionCodeFromCounts (p.1, p.2.2.2.2, p.2.2.1)) := by
    have hComp := TMPolyTimeMap.comp compactPositionCodeFromCounts_tm_polytime hNextCodeInput
    simpa [Function.comp, X] using hComp
  have hTailOut :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat × Nat × Nat × Nat =>
          (compactPositionCodeFromCounts (p.1, p.2.2.2.1, p.2.2.1),
            compactPositionCodeFromCounts (p.1, p.2.2.2.2, p.2.2.1))) :=
    TMPolyTimeMap.prod_mk hCode hNextCode
  have hOut := TMPolyTimeMap.prod_mk hBeta hTailOut
  simpa [compactFillerTripleFromData, tripleStructuredEncodedType, X] using hOut

theorem compactFillerTripleFromData_eq_compactFillerTriple
    (I : ExactCoverInput) (beta x j next : Nat)
    (hnext : next = compactNextInSet I j x) :
    compactFillerTripleFromData (I.system.universeSize, beta, j, x, next) =
      compactFillerTriple I beta x j := by
  subst next
  simp [compactFillerTripleFromData, compactFillerTriple,
    compactPositionCodeFromCounts_eq]

theorem compactFillerTripleFromData_inputSize_le
    (N universeSize beta j x next : Nat)
    (hUniverse : universeSize + 1 ≤ N)
    (hBeta : beta + 1 ≤ N)
    (hj : j + 1 ≤ N) (hx : x + 1 ≤ N) (hNext : next + 1 ≤ N) :
    tripleStructuredEncodedType.inputSize
        (compactFillerTripleFromData (universeSize, beta, j, x, next)) ≤
      10 * (N * N) + 10 := by
  have hUniverseLe : universeSize ≤ N := by omega
  have hBetaLe : beta ≤ N := by omega
  have hJLe : j ≤ N := by omega
  have hXLe : x ≤ N := by omega
  have hNextLe : next ≤ N := by omega
  have hCodeProduct : j * universeSize ≤ N * N :=
    Nat.mul_le_mul hJLe hUniverseLe
  have hCode : compactPositionCodeFromCounts (universeSize, x, j) ≤ 2 * (N * N) := by
    simp [compactPositionCodeFromCounts]
    nlinarith [hCodeProduct, hXLe, sq_nonneg (N : Int)]
  have hNextCode :
      compactPositionCodeFromCounts (universeSize, next, j) ≤ 2 * (N * N) := by
    simp [compactPositionCodeFromCounts]
    nlinarith [hCodeProduct, hNextLe, sq_nonneg (N : Int)]
  simp [compactFillerTripleFromData, tripleStructuredEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat]
  nlinarith [hBetaLe, hCode, hNextCode, sq_nonneg (N : Int)]

theorem compactFillerTripleFromData_singleton_inputSize_le
    (N universeSize beta j x next : Nat)
    (hUniverse : universeSize + 1 ≤ N)
    (hBeta : beta + 1 ≤ N)
    (hj : j + 1 ≤ N) (hx : x + 1 ≤ N) (hNext : next + 1 ≤ N) :
    tripleListStructuredEncodedType.inputSize
        [compactFillerTripleFromData (universeSize, beta, j, x, next)] ≤
      10 * (N * N) + 20 := by
  have hTriple :=
    compactFillerTripleFromData_inputSize_le
      N universeSize beta j x next hUniverse hBeta hj hx hNext
  simp [tripleListStructuredEncodedType, EncodedType.inputSize_list_cons,
    EncodedType.inputSize_list_nil]
  omega

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
