/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.Alpha

/-!
Executable cover-triple helpers for the compact
Exact-Cover-to-3-Dimensional-Matching route.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactCoverTripleFromDataInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod setFamilyStructuredEncodedType
      (EncodedType.prod EncodedType.nat EncodedType.nat))

def compactCoverTripleFromData
    (p : Nat × List (List Nat) × Nat × Nat) : Nat × Nat × Nat :=
  let alpha := compactAlphaCodeFromData (p.1, p.2.1, p.2.2.2)
  let code := compactPositionCodeFromCounts (p.1, p.2.2.2, p.2.2.1)
  (alpha, code, code)

theorem compactCoverTripleFromData_tm_polytime :
    TMPolyTimeMap
      compactCoverTripleFromDataInputEncodedType
      tripleStructuredEncodedType
      compactCoverTripleFromData := by
  let X := compactCoverTripleFromDataInputEncodedType
  have hUniverse : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × List (List Nat) × Nat × Nat => p.1) := by
    simpa [X, compactCoverTripleFromDataInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod setFamilyStructuredEncodedType
          (EncodedType.prod EncodedType.nat EncodedType.nat))
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod setFamilyStructuredEncodedType
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : Nat × List (List Nat) × Nat × Nat => p.2) := by
    simpa [X, compactCoverTripleFromDataInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod setFamilyStructuredEncodedType
          (EncodedType.prod EncodedType.nat EncodedType.nat))
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun p : Nat × List (List Nat) × Nat × Nat => p.2.1) := by
    have hFst := TMPolyTimeMap.fst setFamilyStructuredEncodedType
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × List (List Nat) × Nat × Nat => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd setFamilyStructuredEncodedType
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hJ : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × List (List Nat) × Nat × Nat => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hX : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × List (List Nat) × Nat × Nat => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hAlphaInput :
      TMPolyTimeMap X compactAlphaCodeFromDataInputEncodedType
        (fun p : Nat × List (List Nat) × Nat × Nat => (p.1, p.2.1, p.2.2.2)) := by
    simpa [compactAlphaCodeFromDataInputEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse (TMPolyTimeMap.prod_mk hSets hX)
  have hAlpha :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Nat × List (List Nat) × Nat × Nat =>
          compactAlphaCodeFromData (p.1, p.2.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp compactAlphaCodeFromData_tm_polytime hAlphaInput
    simpa [Function.comp, X] using hComp
  have hCodeInput :
      TMPolyTimeMap X compactPositionCodeInputEncodedType
        (fun p : Nat × List (List Nat) × Nat × Nat => (p.1, p.2.2.2, p.2.2.1)) := by
    simpa [compactPositionCodeInputEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse (TMPolyTimeMap.prod_mk hX hJ)
  have hCode :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Nat × List (List Nat) × Nat × Nat =>
          compactPositionCodeFromCounts (p.1, p.2.2.2, p.2.2.1)) := by
    have hComp := TMPolyTimeMap.comp compactPositionCodeFromCounts_tm_polytime hCodeInput
    simpa [Function.comp, X] using hComp
  have hTailOut :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × List (List Nat) × Nat × Nat =>
          (compactPositionCodeFromCounts (p.1, p.2.2.2, p.2.2.1),
            compactPositionCodeFromCounts (p.1, p.2.2.2, p.2.2.1))) :=
    TMPolyTimeMap.prod_mk hCode hCode
  have hOut := TMPolyTimeMap.prod_mk hAlpha hTailOut
  simpa [compactCoverTripleFromData, tripleStructuredEncodedType, X] using hOut

theorem compactCoverTripleFromData_eq_compactCoverTriple
    (I : ExactCoverInput) (x j : Nat) (hOccurs : compactElementOccurs I x) :
    compactCoverTripleFromData (I.system.universeSize, I.system.sets, j, x) =
      compactCoverTriple I x j := by
  simp [compactCoverTripleFromData, compactCoverTriple,
    compactAlphaCodeFromData_eq_compactAlphaCode I x hOccurs,
    compactPositionCodeFromCounts_eq]

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
