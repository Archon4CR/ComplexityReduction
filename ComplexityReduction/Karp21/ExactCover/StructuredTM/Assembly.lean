import ComplexityReduction.Karp21.ExactCover.StructuredTM.BlockFamilies
import ComplexityReduction.Karp21.GraphStructuredTM.EdgeScan
import ComplexityReduction.Karp21.SetCovering.Base

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Direct TM-backed final assembly for the compact
Chromatic-Number-to-Exact-Cover route.
-/

def colorUniverseSizeExecutable (I : ChromaticNumberInput) : Nat :=
  I.graph.vertices + I.graph.edges.length * I.colors

theorem colorUniverseSizeExecutable_eq_colorUniverseSize (I : ChromaticNumberInput) :
    colorUniverseSizeExecutable I = colorUniverseSize I := by
  simp [colorUniverseSizeExecutable, colorUniverseSize, colorEdgeColorPairs_length]

theorem colorUniverseSizeExecutable_tm_polytime :
    TMPolyTimeMap
      chromaticNumberStructuredEncodedType
      EncodedType.nat
      colorUniverseSizeExecutable := by
  let X := chromaticNumberStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType (fun I : X.Carrier => I.graph) := by
    simpa [X] using chromaticNumberGraphTMBackedMap.tm_polytime
  have hVertices :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : X.Carrier => graphPayloadOfGraph I.graph) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun I : X.Carrier => I.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X] using hComp
  have hEdgeCount :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.graph.edges.length) := by
    have hComp :=
      TMPolyTimeMap.comp (HittingSet.listLengthTMBackedMap edgeStructuredEncodedType).tm_polytime
        hEdges
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hColors :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.colors) := by
    simpa [X] using chromaticNumberColorsTMBackedMap.tm_polytime
  have hMulInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun I : X.Carrier => (I.graph.edges.length, I.colors)) :=
    TMPolyTimeMap.prod_mk hEdgeCount hColors
  have hMul :
      TMPolyTimeMap X EncodedType.nat
        (fun I : X.Carrier => I.graph.edges.length * I.colors) := by
    have hComp := TMPolyTimeMap.comp GenericNatTM.natMul_tm_polytime hMulInput
    simpa [Function.comp, X] using hComp
  have hAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun I : X.Carrier => (I.graph.vertices, I.graph.edges.length * I.colors)) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk hVertices hMul
  have hOut := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
  simpa [Function.comp, natAddInputEncodedType, colorUniverseSizeExecutable, X] using hOut

def colorExactCoverSetFamilyExecutable (I : ChromaticNumberInput) : List (List Nat) :=
  colorChoiceBlocksExecutable I ++ colorFillerBlocksExecutable I

theorem colorExactCoverSetFamilyExecutable_eq (I : ChromaticNumberInput) :
    colorExactCoverSetFamilyExecutable I =
      colorChoiceBlocks I ++ colorFillerBlocks I := by
  simp [colorExactCoverSetFamilyExecutable,
    colorChoiceBlocksExecutable_eq_colorChoiceBlocks,
    colorFillerBlocksExecutable_eq_colorFillerBlocks]

theorem colorExactCoverSetFamilyExecutable_tm_polytime :
    TMPolyTimeMap
      chromaticNumberStructuredEncodedType
      setFamilyStructuredEncodedType
      colorExactCoverSetFamilyExecutable := by
  let X := chromaticNumberStructuredEncodedType
  have hChoice :
      TMPolyTimeMap X setFamilyStructuredEncodedType colorChoiceBlocksExecutable := by
    simpa [X] using colorChoiceBlocksExecutable_tm_polytime
  have hFiller :
      TMPolyTimeMap X setFamilyStructuredEncodedType colorFillerBlocksExecutable := by
    simpa [X] using colorFillerBlocksExecutable_tm_polytime
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod setFamilyStructuredEncodedType setFamilyStructuredEncodedType)
        (fun I : X.Carrier => (colorChoiceBlocksExecutable I, colorFillerBlocksExecutable I)) :=
    TMPolyTimeMap.prod_mk hChoice hFiller
  have hAppend :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_append setStructuredEncodedType) hAppendInput
  simpa [Function.comp, colorExactCoverSetFamilyExecutable, setFamilyStructuredEncodedType, X]
    using hAppend

def colorExactCoverSetSystemExecutable (I : ChromaticNumberInput) : SetSystemInput where
  universeSize := colorUniverseSizeExecutable I
  sets := colorExactCoverSetFamilyExecutable I

theorem colorExactCoverSetSystemExecutable_eq_colorExactCoverSetSystem
    (I : ChromaticNumberInput) :
    colorExactCoverSetSystemExecutable I = colorExactCoverSetSystem I := by
  cases I
  simp [colorExactCoverSetSystemExecutable, colorExactCoverSetSystem,
    colorUniverseSizeExecutable_eq_colorUniverseSize, colorExactCoverSetFamilyExecutable_eq]

theorem colorExactCoverSetSystemExecutable_tm_polytime :
    TMPolyTimeMap
      chromaticNumberStructuredEncodedType
      setSystemStructuredEncodedType
      colorExactCoverSetSystemExecutable := by
  let X := chromaticNumberStructuredEncodedType
  have hUniverse :
      TMPolyTimeMap X EncodedType.nat colorUniverseSizeExecutable := by
    simpa [X] using colorUniverseSizeExecutable_tm_polytime
  have hSets :
      TMPolyTimeMap X setFamilyStructuredEncodedType colorExactCoverSetFamilyExecutable := by
    simpa [X] using colorExactCoverSetFamilyExecutable_tm_polytime
  have hTuple :
      TMPolyTimeMap X setSystemTupleStructuredEncodedType
        (fun I : X.Carrier =>
          (colorUniverseSizeExecutable I, colorExactCoverSetFamilyExecutable I)) := by
    simpa [setSystemTupleStructuredEncodedType] using TMPolyTimeMap.prod_mk hUniverse hSets
  have hOut :=
    TMPolyTimeMap.comp SetCovering.setSystemTupleToSetSystemInputTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, SetCovering.setSystemTupleToSetSystemInput,
    colorExactCoverSetSystemExecutable, X] using hOut

def colorExactCoverCoreExecutable (I : ChromaticNumberInput) : ExactCoverInput :=
  exactCoverInputFromSystem (colorExactCoverSetSystemExecutable I)

theorem colorExactCoverCoreExecutable_eq_colorExactCoverCore (I : ChromaticNumberInput) :
    colorExactCoverCoreExecutable I = colorExactCoverCore I := by
  simp [colorExactCoverCoreExecutable, colorExactCoverCore,
    colorExactCoverSetSystemExecutable_eq_colorExactCoverSetSystem, exactCoverInputFromSystem]

theorem colorExactCoverCoreExecutable_tm_polytime :
    TMPolyTimeMap
      chromaticNumberStructuredEncodedType
      exactCoverStructuredEncodedType
      colorExactCoverCoreExecutable := by
  have hSystem := colorExactCoverSetSystemExecutable_tm_polytime
  have hOut := TMPolyTimeMap.comp exactCoverInputFromSystemTMBackedMap.tm_polytime hSystem
  simpa [Function.comp, colorExactCoverCoreExecutable] using hOut

def chromaticNumberToExactCoverStructuredTMMap (I : ChromaticNumberInput) :
    ExactCoverInput :=
  match colorGraphHasSelfLoopBool I with
  | true => noInput
  | false => colorExactCoverCoreExecutable I

theorem chromaticNumberToExactCoverStructuredTMMap_eq_map
    (I : ChromaticNumberInput) :
    chromaticNumberToExactCoverStructuredTMMap I = chromaticNumberToExactCoverMap I := by
  cases hLoop : colorGraphHasSelfLoopBool I <;>
    simp [chromaticNumberToExactCoverStructuredTMMap, chromaticNumberToExactCoverMap,
      hLoop, colorExactCoverCoreExecutable_eq_colorExactCoverCore]

theorem chromaticNumberToExactCoverStructured_tm_polytime :
    TMPolyTimeMap
      chromaticNumberStructuredEncodedType
      exactCoverStructuredEncodedType
      chromaticNumberToExactCoverStructuredTMMap := by
  let X := chromaticNumberStructuredEncodedType
  have hGuard :
      TMPolyTimeMap X EncodedType.bool colorGraphHasSelfLoopBool := by
    simpa [X] using colorGraphHasSelfLoopBool_tm_polytime
  have hCore :
      TMPolyTimeMap X exactCoverStructuredEncodedType colorExactCoverCoreExecutable := by
    simpa [X] using colorExactCoverCoreExecutable_tm_polytime
  have hNo :
      TMPolyTimeMap X exactCoverStructuredEncodedType (fun _ : X.Carrier => noInput) :=
    TMPolyTimeMap.const X exactCoverStructuredEncodedType noInput
  have hTagged :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun I : X.Carrier => (colorGraphHasSelfLoopBool I, I)) :=
    TMPolyTimeMap.prod_mk hGuard (TMPolyTimeMap.id X)
  have hDispatch :=
    graphBoolProduct_dispatch_tm_polytime X exactCoverStructuredEncodedType
      (fFalse := colorExactCoverCoreExecutable)
      (fTrue := fun _ : X.Carrier => noInput)
      hCore hNo
  have hComp := TMPolyTimeMap.comp hDispatch hTagged
  simpa [Function.comp, chromaticNumberToExactCoverStructuredTMMap] using hComp

theorem chromaticNumberToExactCoverStructuredTMMap_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : ChromaticNumberInput => chromaticNumberStructuredEncodedType.inputSize I)
      (fun J : ExactCoverInput => exactCoverStructuredEncodedType.inputSize J)
      chromaticNumberToExactCoverStructuredTMMap := by
  refine PolynomialSizeBound.intro_with 6 1000000 1000000 ?_
  intro I
  rw [chromaticNumberToExactCoverStructuredTMMap_eq_map]
  exact chromaticNumberToExactCoverMap_structured_inputSize_le_source_poly I

noncomputable def chromaticNumberToExactCoverStructuredTMBackedMap :
    TMBackedCostedMap
      chromaticNumberStructuredEncodedType
      exactCoverStructuredEncodedType
      chromaticNumberToExactCoverStructuredTMMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      chromaticNumberToExactCoverStructuredTMMap_polynomialSizeBound
  tm_polytime := chromaticNumberToExactCoverStructured_tm_polytime

theorem chromaticNumberToExactCoverStructuredTMMap_correct
    (I : ChromaticNumberInput) :
    chromaticNumberStructuredDecisionProblem.isYes I ↔
      exactCoverStructuredDecisionProblem.isYes
        (chromaticNumberToExactCoverStructuredTMMap I) := by
  rw [chromaticNumberToExactCoverStructuredTMMap_eq_map]
  simpa [chromaticNumberStructuredDecisionProblem, exactCoverStructuredDecisionProblem]
    using chromaticNumberToExactCoverMap_correct I

noncomputable def chromaticNumberToExactCoverStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      chromaticNumberStructuredDecisionProblem
      exactCoverStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    chromaticNumberToExactCoverStructuredTMBackedMap
    (by
      intro I
      exact chromaticNumberToExactCoverStructuredTMMap_correct I)

/--
Public P16c structured finite-alphabet Chromatic-Number-to-Exact-Cover
reduction, projected from the direct TM-backed block assembly.
-/
noncomputable def chromaticNumberToExactCoverStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      chromaticNumberStructuredDecisionProblem
      exactCoverStructuredDecisionProblem :=
  chromaticNumberToExactCoverStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- Direct TM-facing structured Chromatic-Number-to-Exact-Cover reduction. -/
noncomputable def chromaticNumberToExactCoverStructuredTMKarpReduction :
    TMKarpReduction
      chromaticNumberStructuredDecisionProblem
      exactCoverStructuredDecisionProblem :=
  chromaticNumberToExactCoverStructuredTMBackedKarpReduction.toTMKarpReduction

end ExactCover
end Karp21
end ComplexityReduction
