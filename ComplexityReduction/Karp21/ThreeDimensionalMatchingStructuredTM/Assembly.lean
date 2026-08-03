/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.Guard

/-!
Direct TM-backed final assembly for the compact
Exact-Cover-to-3-Dimensional-Matching route.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

/-! ### Executable compact triples and tuple assembly -/

def compactTriplesExecutable (I : ExactCoverInput) : List (Nat × Nat × Nat) :=
  compactCoverTriplesExecutable
      (I.system.universeSize, I.system.sets.length, I.system.sets) ++
    compactFillerTriplesExecutable
      (I.system.universeSize, I.system.sets.length, I.system.sets)

theorem compactTriplesExecutable_eq_compactTriples
    (I : ExactCoverInput) (hEvery : compactEveryElementOccurs I) :
    compactTriplesExecutable I = compactTriples I := by
  simp [compactTriplesExecutable, compactTriples,
    compactCoverTriplesExecutable_eq_compactCoverTriples,
    compactFillerTriplesExecutable_eq_compactFillerTriples I hEvery]

theorem compactTriplesExecutable_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      tripleListStructuredEncodedType
      compactTriplesExecutable := by
  let X := exactCoverStructuredEncodedType
  have hUniverse :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.system.universeSize) := by
    simpa [X] using exactCoverUniverseSize_tm_polytime
  have hSetCount :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.system.sets.length) := by
    simpa [X] using exactCoverSetsLength_tm_polytime
  have hSets :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun I : X.Carrier => I.system.sets) := by
    simpa [X] using exactCoverSets_tm_polytime
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
        (fun I : X.Carrier => (I.system.sets.length, I.system.sets)) :=
    TMPolyTimeMap.prod_mk hSetCount hSets
  have hContext :
      TMPolyTimeMap X compactPositionFamilyContextEncodedType
        (fun I : X.Carrier =>
          (I.system.universeSize, I.system.sets.length, I.system.sets)) := by
    simpa [compactPositionFamilyContextEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse hPayload
  have hCover :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun I : X.Carrier =>
          compactCoverTriplesExecutable
            (I.system.universeSize, I.system.sets.length, I.system.sets)) := by
    have hComp := TMPolyTimeMap.comp compactCoverTriplesExecutable_tm_polytime hContext
    simpa [Function.comp, X, compactCoverFamilyInputEncodedType,
      compactCoverFamilyContextEncodedType, compactPositionFamilyContextEncodedType] using hComp
  have hFiller :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun I : X.Carrier =>
          compactFillerTriplesExecutable
            (I.system.universeSize, I.system.sets.length, I.system.sets)) := by
    have hComp := TMPolyTimeMap.comp compactFillerTriplesExecutable_tm_polytime hContext
    simpa [Function.comp, X, compactFillerFamilyInputEncodedType,
      compactFillerFamilyContextEncodedType, compactPositionFamilyContextEncodedType] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType)
        (fun I : X.Carrier =>
          (compactCoverTriplesExecutable
              (I.system.universeSize, I.system.sets.length, I.system.sets),
            compactFillerTriplesExecutable
              (I.system.universeSize, I.system.sets.length, I.system.sets))) :=
    TMPolyTimeMap.prod_mk hCover hFiller
  have hAppend :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_append tripleStructuredEncodedType) hAppendInput
  simpa [Function.comp, compactTriplesExecutable, tripleListStructuredEncodedType, X] using hAppend

def compactCoordBoundExecutable (I : ExactCoverInput) : Nat :=
  I.system.sets.length * I.system.universeSize

theorem compactCoordBoundExecutable_eq_compactCoordBound (I : ExactCoverInput) :
    compactCoordBoundExecutable I = compactCoordBound I := by
  rfl

theorem compactCoordBoundExecutable_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      EncodedType.nat
      compactCoordBoundExecutable := by
  let X := exactCoverStructuredEncodedType
  have hUniverse :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.system.universeSize) := by
    simpa [X] using exactCoverUniverseSize_tm_polytime
  have hSetCount :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.system.sets.length) := by
    simpa [X] using exactCoverSetsLength_tm_polytime
  have hMulInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun I : X.Carrier => (I.system.sets.length, I.system.universeSize)) :=
    TMPolyTimeMap.prod_mk hSetCount hUniverse
  have hMul := TMPolyTimeMap.comp TMPolyTimeMap.nat_mul hMulInput
  simpa [Function.comp, compactCoordBoundExecutable, X] using hMul

def compactPositionCodeCountExecutable (I : ExactCoverInput) : Nat :=
  (compactPositionCodesExecutable
    (I.system.universeSize, I.system.sets.length, I.system.sets)).length

theorem compactPositionCodeCountExecutable_eq (I : ExactCoverInput) :
    compactPositionCodeCountExecutable I = (compactPositionCodes I).length := by
  simp [compactPositionCodeCountExecutable, compactPositionCodesExecutable_eq_compactPositionCodes]

theorem compactPositionCodeCountExecutable_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      EncodedType.nat
      compactPositionCodeCountExecutable := by
  let X := exactCoverStructuredEncodedType
  have hUniverse :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.system.universeSize) := by
    simpa [X] using exactCoverUniverseSize_tm_polytime
  have hSetCount :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.system.sets.length) := by
    simpa [X] using exactCoverSetsLength_tm_polytime
  have hSets :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun I : X.Carrier => I.system.sets) := by
    simpa [X] using exactCoverSets_tm_polytime
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
        (fun I : X.Carrier => (I.system.sets.length, I.system.sets)) :=
    TMPolyTimeMap.prod_mk hSetCount hSets
  have hContext :
      TMPolyTimeMap X compactPositionFamilyInputEncodedType
        (fun I : X.Carrier =>
          (I.system.universeSize, I.system.sets.length, I.system.sets)) := by
    simpa [compactPositionFamilyInputEncodedType, compactPositionFamilyContextEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse hPayload
  have hCodes :
      TMPolyTimeMap X compactPositionCodeListEncodedType
        (fun I : X.Carrier =>
          compactPositionCodesExecutable
            (I.system.universeSize, I.system.sets.length, I.system.sets)) := by
    have hComp := TMPolyTimeMap.comp compactPositionCodesExecutable_tm_polytime hContext
    simpa [Function.comp, X] using hComp
  have hLength := TMPolyTimeMap.comp
    (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime hCodes
  simpa [Function.comp, compactPositionCodeCountExecutable,
    compactPositionCodeListEncodedType, X] using hLength

def compactMapCoreExecutable (I : ExactCoverInput) : ThreeDimensionalMatchingInput where
  xSize := compactCoordBoundExecutable I
  ySize := compactCoordBoundExecutable I
  zSize := compactCoordBoundExecutable I
  triples := compactTriplesExecutable I
  k := compactPositionCodeCountExecutable I

theorem compactMapCoreExecutable_eq_compactMapCore
    (I : ExactCoverInput) (hEvery : compactEveryElementOccurs I) :
    compactMapCoreExecutable I = compactMapCore I := by
  simp [compactMapCoreExecutable, compactMapCore,
    compactCoordBoundExecutable_eq_compactCoordBound,
    compactTriplesExecutable_eq_compactTriples I hEvery,
    compactPositionCodeCountExecutable_eq]

theorem compactMapCoreExecutable_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      threeDimensionalMatchingStructuredEncodedType
      compactMapCoreExecutable := by
  let X := exactCoverStructuredEncodedType
  have hCoord :
      TMPolyTimeMap X EncodedType.nat compactCoordBoundExecutable := by
    simpa [X] using compactCoordBoundExecutable_tm_polytime
  have hTriples :
      TMPolyTimeMap X tripleListStructuredEncodedType compactTriplesExecutable := by
    simpa [X] using compactTriplesExecutable_tm_polytime
  have hK :
      TMPolyTimeMap X EncodedType.nat compactPositionCodeCountExecutable := by
    simpa [X] using compactPositionCodeCountExecutable_tm_polytime
  have hZPayload :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod tripleListStructuredEncodedType EncodedType.nat))
        (fun I : X.Carrier =>
          (compactCoordBoundExecutable I, (compactTriplesExecutable I,
            compactPositionCodeCountExecutable I))) := by
    simpa using TMPolyTimeMap.prod_mk hCoord (TMPolyTimeMap.prod_mk hTriples hK)
  have hYPayload :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod tripleListStructuredEncodedType EncodedType.nat)))
        (fun I : X.Carrier =>
          (compactCoordBoundExecutable I,
            (compactCoordBoundExecutable I, (compactTriplesExecutable I,
              compactPositionCodeCountExecutable I)))) := by
    simpa using TMPolyTimeMap.prod_mk hCoord hZPayload
  have hTuple :
      TMPolyTimeMap X threeDimensionalMatchingTupleStructuredEncodedType
        (fun I : X.Carrier =>
          (compactCoordBoundExecutable I,
            (compactCoordBoundExecutable I,
              (compactCoordBoundExecutable I,
                (compactTriplesExecutable I, compactPositionCodeCountExecutable I))))) := by
    simpa [threeDimensionalMatchingTupleStructuredEncodedType] using
      TMPolyTimeMap.prod_mk hCoord hYPayload
  have hOut :=
    TMPolyTimeMap.comp threeDimensionalMatchingTupleToInputTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, threeDimensionalMatchingTupleToInput, compactMapCoreExecutable, X]
    using hOut

/-! ### Guarded public map and reductions -/

def compactGuardBool (I : ExactCoverInput) : Bool :=
  graphBoolAndPair
    (SteinerTree.exactCoverWellFormedBool I,
      compactEveryElementOccursBool (I.system.universeSize, I.system.sets))

theorem compactGuardBool_eq_true_iff (I : ExactCoverInput) :
    compactGuardBool I = true ↔
      SetSystemWellFormed I.system ∧ compactEveryElementOccurs I := by
  simp [compactGuardBool, graphBoolAndPair_eq_true_iff,
    SteinerTree.exactCoverWellFormedBool_eq_true_iff,
    compactEveryElementOccursBool_eq_compactEveryElementOccurs]

theorem compactGuardBool_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      EncodedType.bool
      compactGuardBool := by
  let X := exactCoverStructuredEncodedType
  have hWell :
      TMPolyTimeMap X EncodedType.bool SteinerTree.exactCoverWellFormedBool := by
    simpa [X] using SteinerTree.exactCoverWellFormedBool_tm_polytime
  have hUniverse :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.system.universeSize) := by
    simpa [X] using exactCoverUniverseSize_tm_polytime
  have hSets :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun I : X.Carrier => I.system.sets) := by
    simpa [X] using exactCoverSets_tm_polytime
  have hEveryInput :
      TMPolyTimeMap X compactEveryElementGuardInputEncodedType
        (fun I : X.Carrier => (I.system.universeSize, I.system.sets)) := by
    simpa [compactEveryElementGuardInputEncodedType,
      compactEveryElementGuardContextEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse hSets
  have hEvery :
      TMPolyTimeMap X EncodedType.bool
        (fun I : X.Carrier =>
          compactEveryElementOccursBool (I.system.universeSize, I.system.sets)) := by
    have hComp := TMPolyTimeMap.comp compactEveryElementOccursBool_tm_polytime hEveryInput
    simpa [Function.comp, X] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun I : X.Carrier =>
          (SteinerTree.exactCoverWellFormedBool I,
            compactEveryElementOccursBool (I.system.universeSize, I.system.sets))) :=
    TMPolyTimeMap.prod_mk hWell hEvery
  have hAnd := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
  simpa [Function.comp, compactGuardBool, X] using hAnd

def exactCoverToThreeDimensionalMatchingCompactStructuredTMMap
    (I : ExactCoverInput) : ThreeDimensionalMatchingInput :=
  match compactGuardBool I with
  | true => compactMapCoreExecutable I
  | false => noInput

theorem exactCoverToThreeDimensionalMatchingCompactStructuredTMMap_eq_compactMap
    (I : ExactCoverInput) :
    exactCoverToThreeDimensionalMatchingCompactStructuredTMMap I = compactMap I := by
  by_cases hGuard : SetSystemWellFormed I.system ∧ compactEveryElementOccurs I
  · have hBool : compactGuardBool I = true := (compactGuardBool_eq_true_iff I).2 hGuard
    simp [exactCoverToThreeDimensionalMatchingCompactStructuredTMMap, compactMap,
      hBool, hGuard, compactMapCoreExecutable_eq_compactMapCore I hGuard.2]
  · have hBool : compactGuardBool I = false := by
      cases h : compactGuardBool I with
      | false => rfl
      | true =>
          have hSem := (compactGuardBool_eq_true_iff I).1 h
          exact False.elim (hGuard hSem)
    simp [exactCoverToThreeDimensionalMatchingCompactStructuredTMMap, compactMap,
      hBool, hGuard]

theorem exactCoverToThreeDimensionalMatchingCompactStructured_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      threeDimensionalMatchingStructuredEncodedType
      exactCoverToThreeDimensionalMatchingCompactStructuredTMMap := by
  let X := exactCoverStructuredEncodedType
  have hGuard :
      TMPolyTimeMap X EncodedType.bool compactGuardBool := by
    simpa [X] using compactGuardBool_tm_polytime
  have hCore :
      TMPolyTimeMap X threeDimensionalMatchingStructuredEncodedType compactMapCoreExecutable := by
    simpa [X] using compactMapCoreExecutable_tm_polytime
  have hNo :
      TMPolyTimeMap X threeDimensionalMatchingStructuredEncodedType (fun _ : X.Carrier => noInput) :=
    TMPolyTimeMap.const X threeDimensionalMatchingStructuredEncodedType noInput
  have hTagged :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun I : X.Carrier => (compactGuardBool I, I)) :=
    TMPolyTimeMap.prod_mk hGuard (TMPolyTimeMap.id X)
  have hDispatch :=
    graphBoolProduct_dispatch_tm_polytime X threeDimensionalMatchingStructuredEncodedType
      (fFalse := fun _ : X.Carrier => noInput)
      (fTrue := compactMapCoreExecutable)
      hNo hCore
  have hComp := TMPolyTimeMap.comp hDispatch hTagged
  simpa [Function.comp, exactCoverToThreeDimensionalMatchingCompactStructuredTMMap] using hComp

theorem exactCoverToThreeDimensionalMatchingCompactStructuredTMMap_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : ExactCoverInput => exactCoverStructuredEncodedType.inputSize I)
      (fun J : ThreeDimensionalMatchingInput =>
        threeDimensionalMatchingStructuredEncodedType.inputSize J)
      exactCoverToThreeDimensionalMatchingCompactStructuredTMMap := by
  refine ⟨6, 2048, 0, ?_⟩
  intro I
  rw [exactCoverToThreeDimensionalMatchingCompactStructuredTMMap_eq_compactMap]
  exact compactMap_structured_inputSize_le_source_poly I

noncomputable def exactCoverToThreeDimensionalMatchingCompactStructuredTMBackedMap :
    TMBackedCostedMap
      exactCoverStructuredEncodedType
      threeDimensionalMatchingStructuredEncodedType
      exactCoverToThreeDimensionalMatchingCompactStructuredTMMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      exactCoverToThreeDimensionalMatchingCompactStructuredTMMap_polynomialSizeBound
  tm_polytime := exactCoverToThreeDimensionalMatchingCompactStructured_tm_polytime

theorem exactCoverToThreeDimensionalMatchingCompactStructuredTMMap_correct
    (I : ExactCoverInput) :
    exactCoverStructuredDecisionProblem.isYes I ↔
      threeDimensionalMatchingStructuredDecisionProblem.isYes
        (exactCoverToThreeDimensionalMatchingCompactStructuredTMMap I) := by
  rw [exactCoverToThreeDimensionalMatchingCompactStructuredTMMap_eq_compactMap]
  simpa [exactCoverStructuredDecisionProblem, threeDimensionalMatchingStructuredDecisionProblem]
    using compactMap_correct I

noncomputable def exactCoverToThreeDimensionalMatchingCompactStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      exactCoverStructuredDecisionProblem
      threeDimensionalMatchingStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    exactCoverToThreeDimensionalMatchingCompactStructuredTMBackedMap
    (by
      intro I
      exact exactCoverToThreeDimensionalMatchingCompactStructuredTMMap_correct I)

/--
Public P16c structured finite-alphabet Exact-Cover-to-3DM reduction, projected
from the direct TM-backed compact triple assembly.
-/
noncomputable def exactCoverToThreeDimensionalMatchingCompactStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      exactCoverStructuredDecisionProblem
      threeDimensionalMatchingStructuredDecisionProblem :=
  exactCoverToThreeDimensionalMatchingCompactStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- Direct TM-facing structured Exact-Cover-to-3DM reduction. -/
noncomputable def exactCoverToThreeDimensionalMatchingCompactStructuredTMKarpReduction :
    TMKarpReduction
      exactCoverStructuredDecisionProblem
      threeDimensionalMatchingStructuredDecisionProblem :=
  exactCoverToThreeDimensionalMatchingCompactStructuredTMBackedKarpReduction.toTMKarpReduction

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
