import ComplexityReduction.Karp21.ExactCover.StructuredTM.BlockInputFamily
import ComplexityReduction.Karp21.ExactCover.StructuredTM.FillerBlock
import ComplexityReduction.Karp21.HittingSet.StructuredRoute

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Executable set-family constructors for the compact
Chromatic-Number-to-Exact-Cover route.

This module reuses the rectangular block-input family generator and maps each
input through the already checked single-block choice/filler machines.
-/

def colorChoiceBlockFamilyContext (I : ChromaticNumberInput) : ColorBlockInputRowContext :=
  (I, (I.graph.vertices, I.colors))

def colorFillerBlockFamilyContext (I : ChromaticNumberInput) : ColorBlockInputRowContext :=
  (I, (I.graph.edges.length, I.colors))

def colorChoiceBlockInputsExecutable
    (I : ChromaticNumberInput) : List colorBlockInputEncodedType.Carrier :=
  colorBlockInputsExecutable (colorChoiceBlockFamilyContext I)

def colorFillerBlockInputsExecutable
    (I : ChromaticNumberInput) : List colorBlockInputEncodedType.Carrier :=
  colorBlockInputsExecutable (colorFillerBlockFamilyContext I)

def colorChoiceBlocksExecutable (I : ChromaticNumberInput) : List (List Nat) :=
  (colorChoiceBlockInputsExecutable I).map colorChoiceBlockExecutable

def colorFillerBlocksExecutable (I : ChromaticNumberInput) : List (List Nat) :=
  (colorFillerBlockInputsExecutable I).map colorFillerBlockExecutable

/-! ### Semantics -/

theorem colorChoiceBlockInputsExecutable_eq_flatMap (I : ChromaticNumberInput) :
    colorChoiceBlockInputsExecutable I =
      (List.range I.graph.vertices).flatMap (fun v =>
        (List.range I.colors).map fun c => (I, (v, c))) := by
  simpa [colorChoiceBlockInputsExecutable, colorChoiceBlockFamilyContext] using
    colorBlockInputsExecutable_eq_flatMap (colorChoiceBlockFamilyContext I)

theorem colorFillerBlockInputsExecutable_eq_flatMap (I : ChromaticNumberInput) :
    colorFillerBlockInputsExecutable I =
      (List.range I.graph.edges.length).flatMap (fun i =>
        (List.range I.colors).map fun c => (I, (i, c))) := by
  simpa [colorFillerBlockInputsExecutable, colorFillerBlockFamilyContext] using
    colorBlockInputsExecutable_eq_flatMap (colorFillerBlockFamilyContext I)

theorem colorChoiceBlocksExecutable_eq_colorChoiceBlocks (I : ChromaticNumberInput) :
    colorChoiceBlocksExecutable I = colorChoiceBlocks I := by
  rw [colorChoiceBlocksExecutable, colorChoiceBlockInputsExecutable_eq_flatMap]
  simp [colorChoiceBlocks, List.map_flatMap]
  apply List.flatMap_congr
  intro v _hv
  apply List.map_congr_left
  intro c hc
  have hc' : c < I.colors := by
    simpa using hc
  simpa [colorChoiceBlockFast] using
    colorChoiceBlockFast_eq_colorChoiceBlock (I := I) (v := v) (c := c) hc'

theorem colorFillerBlocksExecutable_eq_colorFillerBlocks (I : ChromaticNumberInput) :
    colorFillerBlocksExecutable I = colorFillerBlocks I := by
  rw [colorFillerBlocksExecutable, colorFillerBlockInputsExecutable_eq_flatMap]
  simp [colorFillerBlocks, List.map_flatMap]
  apply List.flatMap_congr
  intro i hi
  have hi' : i < I.graph.edges.length := by
    simpa using hi
  apply List.map_congr_left
  intro c hc
  have hc' : c < I.colors := by
    simpa using hc
  simpa [colorFillerBlockExecutable] using
    colorFillerBlockFast_eq_colorFillerBlock (I := I) (i := i) (c := c) hi' hc'

/-! ### TM witnesses -/

theorem colorChoiceBlockFamilyContext_tm_polytime :
    TMPolyTimeMap
      chromaticNumberStructuredEncodedType
      colorBlockInputRowContextEncodedType
      colorChoiceBlockFamilyContext := by
  let X := chromaticNumberStructuredEncodedType
  have hSource : TMPolyTimeMap X X (fun I : X.Carrier => I) := TMPolyTimeMap.id X
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType (fun I : X.Carrier => I.graph) := by
    simpa [X] using chromaticNumberGraphTMBackedMap.tm_polytime
  have hVertices :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hColors :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.colors) := by
    simpa [X] using chromaticNumberColorsTMBackedMap.tm_polytime
  have hCounts :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun I : X.Carrier => (I.graph.vertices, I.colors)) :=
    TMPolyTimeMap.prod_mk hVertices hColors
  have hOut := TMPolyTimeMap.prod_mk hSource hCounts
  simpa [colorChoiceBlockFamilyContext, colorBlockInputRowContextEncodedType,
    colorBlockInputEncodedType, colorChoiceCodeInputEncodedType, X] using hOut

theorem colorFillerBlockFamilyContext_tm_polytime :
    TMPolyTimeMap
      chromaticNumberStructuredEncodedType
      colorBlockInputRowContextEncodedType
      colorFillerBlockFamilyContext := by
  let X := chromaticNumberStructuredEncodedType
  have hSource : TMPolyTimeMap X X (fun I : X.Carrier => I) := TMPolyTimeMap.id X
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType (fun I : X.Carrier => I.graph) := by
    simpa [X] using chromaticNumberGraphTMBackedMap.tm_polytime
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
  have hCounts :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun I : X.Carrier => (I.graph.edges.length, I.colors)) :=
    TMPolyTimeMap.prod_mk hEdgeCount hColors
  have hOut := TMPolyTimeMap.prod_mk hSource hCounts
  simpa [colorFillerBlockFamilyContext, colorBlockInputRowContextEncodedType,
    colorBlockInputEncodedType, colorChoiceCodeInputEncodedType, X] using hOut

theorem colorChoiceBlockInputsExecutable_tm_polytime :
    TMPolyTimeMap
      chromaticNumberStructuredEncodedType
      colorBlockInputListEncodedType
      colorChoiceBlockInputsExecutable := by
  have hComp :=
    TMPolyTimeMap.comp colorBlockInputsExecutable_tm_polytime
      colorChoiceBlockFamilyContext_tm_polytime
  simpa [Function.comp, colorChoiceBlockInputsExecutable] using hComp

theorem colorFillerBlockInputsExecutable_tm_polytime :
    TMPolyTimeMap
      chromaticNumberStructuredEncodedType
      colorBlockInputListEncodedType
      colorFillerBlockInputsExecutable := by
  have hComp :=
    TMPolyTimeMap.comp colorBlockInputsExecutable_tm_polytime
      colorFillerBlockFamilyContext_tm_polytime
  simpa [Function.comp, colorFillerBlockInputsExecutable] using hComp

theorem colorChoiceBlocksExecutable_tm_polytime :
    TMPolyTimeMap
      chromaticNumberStructuredEncodedType
      setFamilyStructuredEncodedType
      colorChoiceBlocksExecutable := by
  have hMap := TMPolyTimeMap.list_map colorChoiceBlockExecutable_tm_polytime
  have hComp := TMPolyTimeMap.comp hMap colorChoiceBlockInputsExecutable_tm_polytime
  simpa [Function.comp, colorChoiceBlocksExecutable, colorBlockInputListEncodedType,
    colorBlockInputEncodedType, colorChoiceCodeInputEncodedType, setFamilyStructuredEncodedType]
    using hComp

theorem colorFillerBlocksExecutable_tm_polytime :
    TMPolyTimeMap
      chromaticNumberStructuredEncodedType
      setFamilyStructuredEncodedType
      colorFillerBlocksExecutable := by
  have hFiller :
      TMPolyTimeMap colorBlockInputEncodedType setStructuredEncodedType
        colorFillerBlockExecutable := by
    simpa [colorBlockInputEncodedType, colorChoiceCodeInputEncodedType,
      colorFillerBlockInputEncodedType] using colorFillerBlockExecutable_tm_polytime
  have hMap := TMPolyTimeMap.list_map hFiller
  have hComp := TMPolyTimeMap.comp hMap colorFillerBlockInputsExecutable_tm_polytime
  simpa [Function.comp, colorFillerBlocksExecutable, colorBlockInputListEncodedType,
    colorBlockInputEncodedType, colorChoiceCodeInputEncodedType, setFamilyStructuredEncodedType]
    using hComp

end ExactCover
end Karp21
end ComplexityReduction
