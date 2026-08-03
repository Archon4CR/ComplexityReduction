/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.PositionCodes
import ComplexityReduction.Karp21.HittingSet.IndexRunner
import ComplexityReduction.Karp21.MaxCut.StructuredTM.Lookup

/-!
Executable `α`-choice helpers for the compact
Exact-Cover-to-3-Dimensional-Matching route.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactAlphaSetIndexInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType

def compactAlphaSetIndexExecutable (p : Nat × List (List Nat)) : Nat :=
  MaxCut.natListGetDFromInput (0, HittingSet.setIndexIndicesFromFamily p)

theorem compactAlphaSetIndexExecutable_tm_polytime :
    TMPolyTimeMap
      compactAlphaSetIndexInputEncodedType
      EncodedType.nat
      compactAlphaSetIndexExecutable := by
  let X := compactAlphaSetIndexInputEncodedType
  have hZero :
      TMPolyTimeMap X EncodedType.nat
        (fun _ : Nat × List (List Nat) => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hIndices :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => HittingSet.setIndexIndicesFromFamily p) := by
    simpa [X, compactAlphaSetIndexInputEncodedType,
      HittingSet.setIndexInstructionInputEncodedType] using
      HittingSet.setIndexIndicesFromFamily_tm_polytime
  have hInput :
      TMPolyTimeMap X MaxCut.natListGetDInputEncodedType
        (fun p : Nat × List (List Nat) =>
          ((0 : Nat), HittingSet.setIndexIndicesFromFamily p)) := by
    simpa [MaxCut.natListGetDInputEncodedType, partitionWeightsStructuredEncodedType] using
      TMPolyTimeMap.prod_mk hZero hIndices
  have hComp := TMPolyTimeMap.comp MaxCut.natListGetDFromInput_tm_polytime hInput
  simpa [Function.comp, compactAlphaSetIndexExecutable, X] using hComp

theorem compactAlphaSetIndexExecutable_eq_findIdx
    (I : ExactCoverInput) (x : Nat) (hOccurs : compactElementOccurs I x) :
    compactAlphaSetIndexExecutable (x, I.system.sets) =
      I.system.sets.findIdx (fun S => HittingSet.setContainsBool (x, S)) := by
  classical
  let pred := fun S : List Nat => HittingSet.setContainsBool (x, S)
  rcases hOccurs with ⟨j, hj, hx⟩
  have hxSet : x ∈ I.system.sets[j] := by
    have hxSet' := ((mem_compactSupport_iff I (compactSourceSetAt I j) x).1 hx).2
    have hSource :
        compactSourceSetAt I j = I.system.sets[j] := by
      rw [compactSourceSetAt, List.getD_eq_getElem (l := I.system.sets) (d := []) hj]
    simpa [hSource] using hxSet'
  have hExistsPred : ∃ S ∈ I.system.sets, pred S = true := by
    refine ⟨I.system.sets[j], List.getElem_mem hj, ?_⟩
    exact (HittingSet.setContainsBool_eq_true_iff (x, I.system.sets[j])).2 hxSet
  have hFindLt :
      I.system.sets.findIdx pred < I.system.sets.length :=
    List.findIdx_lt_length_of_exists hExistsPred
  have hFindMem :
      I.system.sets.findIdx pred ∈ I.system.sets.findIdxs pred :=
    List.findIdx_mem_findIdxs hFindLt
  have hLen : 0 < (I.system.sets.findIdxs pred).length :=
    List.length_pos_of_mem hFindMem
  rw [compactAlphaSetIndexExecutable, MaxCut.natListGetDFromInput_eq_getD,
    HittingSet.setIndexIndicesFromFamily_eq_findIdxs]
  rw [List.getD_eq_getElem (l := I.system.sets.findIdxs pred) (d := 0) hLen]
  exact List.getElem_zero_findIdxs_eq_findIdx hLen

theorem compactAlphaSetIndexExecutable_eq_compactAlphaSetIndex
    (I : ExactCoverInput) (x : Nat) (hOccurs : compactElementOccurs I x) :
    compactAlphaSetIndexExecutable (x, I.system.sets) = compactAlphaSetIndex I x := by
  classical
  let pred := fun S : List Nat => HittingSet.setContainsBool (x, S)
  have hFindEq :
      I.system.sets.findIdx pred = Nat.find hOccurs := by
    have hxU : x < I.system.universeSize := by
      rcases hOccurs with ⟨j, _hj, hx⟩
      exact ((mem_compactSupport_iff I (compactSourceSetAt I j) x).1 hx).1
    have hExistsPred : ∃ S ∈ I.system.sets, pred S = true := by
      rcases hOccurs with ⟨j, hj, hx⟩
      have hxSet : x ∈ I.system.sets[j] := by
        have hxSet' := ((mem_compactSupport_iff I (compactSourceSetAt I j) x).1 hx).2
        have hSource :
            compactSourceSetAt I j = I.system.sets[j] := by
          rw [compactSourceSetAt, List.getD_eq_getElem (l := I.system.sets) (d := []) hj]
        simpa [hSource] using hxSet'
      refine ⟨I.system.sets[j], List.getElem_mem hj, ?_⟩
      exact (HittingSet.setContainsBool_eq_true_iff (x, I.system.sets[j])).2 hxSet
    have hFindLt :
        I.system.sets.findIdx pred < I.system.sets.length :=
      List.findIdx_lt_length_of_exists hExistsPred
    have hPredAt :
        pred I.system.sets[I.system.sets.findIdx pred] = true := by
      simpa [pred] using List.findIdx_getElem (w := hFindLt)
    symm
    rw [Nat.find_eq_iff hOccurs]
    constructor
    · constructor
      · exact hFindLt
      · have hxSet :
            x ∈ I.system.sets[I.system.sets.findIdx pred] :=
          (HittingSet.setContainsBool_eq_true_iff
            (x, I.system.sets[I.system.sets.findIdx pred])).1 hPredAt
        have hSource :
            compactSourceSetAt I (I.system.sets.findIdx pred) =
              I.system.sets[I.system.sets.findIdx pred] := by
          rw [compactSourceSetAt,
            List.getD_eq_getElem (l := I.system.sets) (d := []) hFindLt]
        exact (mem_compactSupport_iff I
          (compactSourceSetAt I (I.system.sets.findIdx pred)) x).2
            ⟨hxU, by simpa [hSource] using hxSet⟩
    · intro m hm hM
      have hmLt : m < I.system.sets.length := hM.1
      have hxSet' := ((mem_compactSupport_iff I (compactSourceSetAt I m) x).1 hM.2).2
      have hSource :
          compactSourceSetAt I m = I.system.sets[m] := by
        rw [compactSourceSetAt, List.getD_eq_getElem (l := I.system.sets) (d := []) hmLt]
      have hPredM : pred I.system.sets[m] = true :=
        (HittingSet.setContainsBool_eq_true_iff (x, I.system.sets[m])).2
          (by simpa [hSource] using hxSet')
      have hFalse := List.not_of_lt_findIdx (xs := I.system.sets) (p := pred) hm
      exact Bool.false_ne_true (hFalse.symm.trans hPredM)
  rw [compactAlphaSetIndexExecutable_eq_findIdx I x hOccurs, hFindEq]
  simp [compactAlphaSetIndex, hOccurs]

def compactAlphaCodeExecutable (I : ExactCoverInput) (x : Nat) : Nat :=
  compactPositionCode I x (compactAlphaSetIndexExecutable (x, I.system.sets))

theorem compactAlphaCodeExecutable_eq_compactAlphaCode
    (I : ExactCoverInput) (x : Nat) (hOccurs : compactElementOccurs I x) :
    compactAlphaCodeExecutable I x = compactAlphaCode I x := by
  simp [compactAlphaCodeExecutable, compactAlphaCode,
    compactAlphaSetIndexExecutable_eq_compactAlphaSetIndex I x hOccurs]

def compactAlphaCodeFromDataInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat)

def compactAlphaCodeFromData (p : Nat × List (List Nat) × Nat) : Nat :=
  compactPositionCodeFromCounts
    (p.1, p.2.2, compactAlphaSetIndexExecutable (p.2.2, p.2.1))

theorem compactAlphaCodeFromData_tm_polytime :
    TMPolyTimeMap
      compactAlphaCodeFromDataInputEncodedType
      EncodedType.nat
      compactAlphaCodeFromData := by
  let X := compactAlphaCodeFromDataInputEncodedType
  have hUniverse : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × List (List Nat) × Nat => p.1) := by
    simpa [X, compactAlphaCodeFromDataInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat)
  have hTail :
      TMPolyTimeMap X (EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat)
        (fun p : Nat × List (List Nat) × Nat => p.2) := by
    simpa [X, compactAlphaCodeFromDataInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat)
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun p : Nat × List (List Nat) × Nat => p.2.1) := by
    have hFst := TMPolyTimeMap.fst setFamilyStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hX : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × List (List Nat) × Nat => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd setFamilyStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hAlphaIndexInput :
      TMPolyTimeMap X compactAlphaSetIndexInputEncodedType
        (fun p : Nat × List (List Nat) × Nat => (p.2.2, p.2.1)) := by
    simpa [compactAlphaSetIndexInputEncodedType] using TMPolyTimeMap.prod_mk hX hSets
  have hAlphaIndex :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Nat × List (List Nat) × Nat =>
          compactAlphaSetIndexExecutable (p.2.2, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp compactAlphaSetIndexExecutable_tm_polytime hAlphaIndexInput
    simpa [Function.comp, X] using hComp
  have hCodeInput :
      TMPolyTimeMap X compactPositionCodeInputEncodedType
        (fun p : Nat × List (List Nat) × Nat =>
          (p.1, p.2.2, compactAlphaSetIndexExecutable (p.2.2, p.2.1))) := by
    simpa [compactPositionCodeInputEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse (TMPolyTimeMap.prod_mk hX hAlphaIndex)
  have hComp := TMPolyTimeMap.comp compactPositionCodeFromCounts_tm_polytime hCodeInput
  simpa [Function.comp, compactAlphaCodeFromData, X] using hComp

theorem compactAlphaCodeFromData_eq_compactAlphaCode
    (I : ExactCoverInput) (x : Nat) (hOccurs : compactElementOccurs I x) :
    compactAlphaCodeFromData (I.system.universeSize, I.system.sets, x) =
      compactAlphaCode I x := by
  simp [compactAlphaCodeFromData, compactPositionCodeFromCounts_eq,
    compactAlphaSetIndexExecutable_eq_compactAlphaSetIndex I x hOccurs,
    compactAlphaCode]

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
