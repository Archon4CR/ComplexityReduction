/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.PackagedEdgeTransfers
import ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.UnaryToBinary
import ComplexityReduction.Karp21.Partition.StructuredTM.UnaryToBinary
import ComplexityReduction.Karp21.MaxCut.StructuredTM.UnaryToBinary

/-!
Packaged standard-TM NP-completeness facts for Karp21 structured targets.

This file bundles the explicit Cook-Levin package domains and composes
them along already-verified direct `TMKarpReduction` edges.  Target
`TMInNP` membership remains an explicit hypothesis at every edge.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-- All explicit direct-TM packaged NP-completeness variants for one target. -/
structure PackagedTMNPComplete (K : EncodedDecisionProblem) : Prop where
  checkedSuffixValidity : SAT.TMNPCompleteEncWithCheckedSuffixValidity K
  rawInputSound : SAT.TMNPCompleteEncWithRawInputSound K
  rawInputNormalizer : SAT.TMNPCompleteEncWithRawInputNormalizer K
  rawSuffixNormalizer : SAT.TMNPCompleteEncWithRawSuffixNormalizer K
  checkedSuffixDecoder : SAT.TMNPCompleteEncWithCheckedSuffixDecoder K
  rawSuffixDecodingNormalizer : SAT.TMNPCompleteEncWithRawSuffixDecodingNormalizer K

namespace PackagedTMNPComplete

/--
Transfer all packaged NP-completeness facts along a packaged direct edge.
This does not build target membership; it consumes the explicit `TMInNP B`
witness required by each packaged transfer theorem.
-/
theorem transfer {A B : EncodedDecisionProblem}
    (hA : PackagedTMNPComplete A)
    (edge : PackagedTMNPCompleteEdge A B)
    (hB : TMInNP B) :
    PackagedTMNPComplete B where
  checkedSuffixValidity := edge.checkedSuffixValidity hA.checkedSuffixValidity hB
  rawInputSound := edge.rawInputSound hA.rawInputSound hB
  rawInputNormalizer := edge.rawInputNormalizer hA.rawInputNormalizer hB
  rawSuffixNormalizer := edge.rawSuffixNormalizer hA.rawSuffixNormalizer hB
  checkedSuffixDecoder := edge.checkedSuffixDecoder hA.checkedSuffixDecoder hB
  rawSuffixDecodingNormalizer :=
    edge.rawSuffixDecodingNormalizer hA.rawSuffixDecodingNormalizer hB

/-- Transfer all packaged NP-completeness facts along one direct TM Karp reduction. -/
theorem transferTMKarpReduction {A B : EncodedDecisionProblem}
    (hA : PackagedTMNPComplete A)
    (r : TMKarpReduction A B)
    (hB : TMInNP B) :
    PackagedTMNPComplete B :=
  transfer hA (PackagedTMNPCompleteEdge.ofTMKarpReduction r) hB

end PackagedTMNPComplete

/-! ### Root packages -/

/-- Historical bundled 3SAT carries all explicit packaged roots. -/
theorem threeSATBundledPackagedTMNPComplete :
    PackagedTMNPComplete SAT.threeSATDecisionProblem where
  checkedSuffixValidity := SAT.threeSAT_TMNPComplete_with_checkedSuffixValidity
  rawInputSound := SAT.threeSAT_TMNPComplete_with_rawInputSound
  rawInputNormalizer := SAT.threeSAT_TMNPComplete_with_rawInputNormalizer
  rawSuffixNormalizer := SAT.threeSAT_TMNPComplete_with_rawSuffixNormalizer
  checkedSuffixDecoder := SAT.threeSAT_TMNPComplete_with_checkedSuffixDecoder
  rawSuffixDecodingNormalizer := SAT.threeSAT_TMNPComplete_with_rawSuffixDecodingNormalizer

/-- Faithful structured 3SAT carries all explicit packaged roots. -/
theorem threeSATStructuredPackagedTMNPComplete :
    PackagedTMNPComplete threeSATStructuredDecisionProblem where
  checkedSuffixValidity := SAT.threeSATStructured_TMNPComplete_with_checkedSuffixValidity
  rawInputSound := SAT.threeSATStructured_TMNPComplete_with_rawInputSound
  rawInputNormalizer := SAT.threeSATStructured_TMNPComplete_with_rawInputNormalizer
  rawSuffixNormalizer := SAT.threeSATStructured_TMNPComplete_with_rawSuffixNormalizer
  checkedSuffixDecoder := SAT.threeSATStructured_TMNPComplete_with_checkedSuffixDecoder
  rawSuffixDecodingNormalizer :=
    SAT.threeSATStructured_TMNPComplete_with_rawSuffixDecodingNormalizer

/-! ### Direct root outgoing edges -/

theorem satisfiabilityStructuredPackagedTMNPComplete
    (hTarget : TMInNP satisfiabilityStructuredDecisionProblem) :
    PackagedTMNPComplete satisfiabilityStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    threeSATStructuredPackagedTMNPComplete
    satisfiabilityStructuredPackagedTMNPCompleteEdge
    hTarget

theorem zeroOneIPStructuredPackagedTMNPComplete
    (hTarget : TMInNP zeroOneIntegerProgrammingStructuredDecisionProblem) :
    PackagedTMNPComplete zeroOneIntegerProgrammingStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    threeSATStructuredPackagedTMNPComplete
    zeroOneIPStructuredPackagedTMNPCompleteEdge
    hTarget

theorem zeroOneIPBinaryStructuredPackagedTMNPCompleteOfStructured
    (hSource : PackagedTMNPComplete zeroOneIntegerProgrammingStructuredDecisionProblem)
    (hTarget : TMInNP zeroOneIntegerProgrammingBinaryStructuredDecisionProblem) :
    PackagedTMNPComplete zeroOneIntegerProgrammingBinaryStructuredDecisionProblem :=
  PackagedTMNPComplete.transferTMKarpReduction
    hSource
    ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction
    hTarget

theorem cliqueStructuredPackagedTMNPComplete
    (hTarget : TMInNP cliqueStructuredDecisionProblem) :
    PackagedTMNPComplete cliqueStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    threeSATStructuredPackagedTMNPComplete
    cliqueStructuredPackagedTMNPCompleteEdge
    hTarget

theorem chromaticNumberStructuredPackagedTMNPComplete
    (hTarget : TMInNP chromaticNumberStructuredDecisionProblem) :
    PackagedTMNPComplete chromaticNumberStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    threeSATStructuredPackagedTMNPComplete
    chromaticNumberStructuredPackagedTMNPCompleteEdge
    hTarget

/-! ### Faithful structured edge transfers from packaged sources -/

theorem setPackingStructuredPackagedTMNPCompleteOfClique
    (hSource : PackagedTMNPComplete cliqueStructuredDecisionProblem)
    (hTarget : TMInNP setPackingStructuredDecisionProblem) :
    PackagedTMNPComplete setPackingStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    setPackingStructuredPackagedTMNPCompleteEdge
    hTarget

theorem vertexCoverStructuredPackagedTMNPCompleteOfClique
    (hSource : PackagedTMNPComplete cliqueStructuredDecisionProblem)
    (hTarget : TMInNP vertexCoverStructuredDecisionProblem) :
    PackagedTMNPComplete vertexCoverStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    vertexCoverStructuredPackagedTMNPCompleteEdge
    hTarget

theorem setCoveringStructuredPackagedTMNPCompleteOfVertexCover
    (hSource : PackagedTMNPComplete vertexCoverStructuredDecisionProblem)
    (hTarget : TMInNP setCoveringStructuredDecisionProblem) :
    PackagedTMNPComplete setCoveringStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    setCoveringStructuredPackagedTMNPCompleteEdge
    hTarget

theorem feedbackNodeSetStructuredPackagedTMNPCompleteOfVertexCover
    (hSource : PackagedTMNPComplete vertexCoverStructuredDecisionProblem)
    (hTarget : TMInNP feedbackNodeSetStructuredDecisionProblem) :
    PackagedTMNPComplete feedbackNodeSetStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    feedbackNodeSetStructuredPackagedTMNPCompleteEdge
    hTarget

theorem feedbackArcSetStructuredPackagedTMNPCompleteOfFeedbackNodeSet
    (hSource : PackagedTMNPComplete feedbackNodeSetStructuredDecisionProblem)
    (hTarget : TMInNP feedbackArcSetStructuredDecisionProblem) :
    PackagedTMNPComplete feedbackArcSetStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    feedbackArcSetStructuredPackagedTMNPCompleteEdge
    hTarget

theorem directedHamiltonianCircuitStructuredPackagedTMNPCompleteOfVertexCover
    (hSource : PackagedTMNPComplete vertexCoverStructuredDecisionProblem)
    (hTarget : TMInNP directedHamiltonianCircuitStructuredDecisionProblem) :
    PackagedTMNPComplete directedHamiltonianCircuitStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    directedHamiltonianCircuitStructuredPackagedTMNPCompleteEdge
    hTarget

theorem undirectedHamiltonianCircuitStructuredPackagedTMNPCompleteOfDirected
    (hSource : PackagedTMNPComplete directedHamiltonianCircuitStructuredDecisionProblem)
    (hTarget : TMInNP undirectedHamiltonianCircuitStructuredDecisionProblem) :
    PackagedTMNPComplete undirectedHamiltonianCircuitStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    undirectedHamiltonianCircuitStructuredPackagedTMNPCompleteEdge
    hTarget

theorem cliqueCoverStructuredPackagedTMNPCompleteOfChromaticNumber
    (hSource : PackagedTMNPComplete chromaticNumberStructuredDecisionProblem)
    (hTarget : TMInNP cliqueCoverStructuredDecisionProblem) :
    PackagedTMNPComplete cliqueCoverStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    cliqueCoverStructuredPackagedTMNPCompleteEdge
    hTarget

theorem exactCoverStructuredPackagedTMNPCompleteOfSetCovering
    (hSource : PackagedTMNPComplete setCoveringStructuredDecisionProblem)
    (hTarget : TMInNP exactCoverStructuredDecisionProblem) :
    PackagedTMNPComplete exactCoverStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    exactCoverStructuredPackagedTMNPCompleteEdge
    hTarget

theorem hittingSetStructuredPackagedTMNPCompleteOfSetCovering
    (hSource : PackagedTMNPComplete setCoveringStructuredDecisionProblem)
    (hTarget : TMInNP hittingSetStructuredDecisionProblem) :
    PackagedTMNPComplete hittingSetStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    hittingSetStructuredPackagedTMNPCompleteEdge
    hTarget

theorem steinerTreeStructuredPackagedTMNPCompleteOfExactCover
    (hSource : PackagedTMNPComplete exactCoverStructuredDecisionProblem)
    (hTarget : TMInNP steinerTreeStructuredDecisionProblem) :
    PackagedTMNPComplete steinerTreeStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    steinerTreeStructuredPackagedTMNPCompleteEdge
    hTarget

theorem threeDimensionalMatchingStructuredPackagedTMNPCompleteOfExactCover
    (hSource : PackagedTMNPComplete exactCoverStructuredDecisionProblem)
    (hTarget : TMInNP threeDimensionalMatchingStructuredDecisionProblem) :
    PackagedTMNPComplete threeDimensionalMatchingStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    threeDimensionalMatchingStructuredPackagedTMNPCompleteEdge
    hTarget

theorem knapsackBinaryStructuredPackagedTMNPCompleteOfZeroOneIPBinary
    (hSource :
      PackagedTMNPComplete zeroOneIntegerProgrammingBinaryStructuredDecisionProblem)
    (hTarget : TMInNP knapsackBinaryStructuredDecisionProblem) :
    PackagedTMNPComplete knapsackBinaryStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    knapsackBinaryStructuredPackagedTMNPCompleteEdge
    hTarget

theorem jobSequencingBinaryStructuredPackagedTMNPCompleteOfKnapsackBinary
    (hSource : PackagedTMNPComplete knapsackBinaryStructuredDecisionProblem)
    (hTarget : TMInNP jobSequencingBinaryStructuredDecisionProblem) :
    PackagedTMNPComplete jobSequencingBinaryStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    jobSequencingBinaryStructuredPackagedTMNPCompleteEdge
    hTarget

theorem partitionBinaryStructuredPackagedTMNPCompleteOfStructured
    (hSource : PackagedTMNPComplete partitionStructuredDecisionProblem)
    (hTarget : TMInNP partitionBinaryStructuredDecisionProblem) :
    PackagedTMNPComplete partitionBinaryStructuredDecisionProblem :=
  PackagedTMNPComplete.transferTMKarpReduction
    hSource
    Partition.partitionStructuredToBinaryStructuredTMKarpReduction
    hTarget

theorem jobSequencingStructuredPackagedTMNPCompleteOfKnapsack
    (hSource : PackagedTMNPComplete knapsackStructuredDecisionProblem)
    (hTarget : TMInNP jobSequencingStructuredDecisionProblem) :
    PackagedTMNPComplete jobSequencingStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    jobSequencingStructuredPackagedTMNPCompleteEdge
    hTarget

theorem partitionStructuredPackagedTMNPCompleteOfKnapsack
    (hSource : PackagedTMNPComplete knapsackStructuredDecisionProblem)
    (hTarget : TMInNP partitionStructuredDecisionProblem) :
    PackagedTMNPComplete partitionStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    partitionStructuredPackagedTMNPCompleteEdge
    hTarget

theorem maxCutStructuredPackagedTMNPCompleteOfPartition
    (hSource : PackagedTMNPComplete partitionStructuredDecisionProblem)
    (hTarget : TMInNP maxCutStructuredDecisionProblem) :
    PackagedTMNPComplete maxCutStructuredDecisionProblem :=
  PackagedTMNPComplete.transfer
    hSource
    maxCutStructuredPackagedTMNPCompleteEdge
    hTarget

theorem maxCutBinaryStructuredPackagedTMNPCompleteOfStructured
    (hSource : PackagedTMNPComplete maxCutStructuredDecisionProblem)
    (hTarget : TMInNP maxCutBinaryStructuredDecisionProblem) :
    PackagedTMNPComplete maxCutBinaryStructuredDecisionProblem :=
  PackagedTMNPComplete.transferTMKarpReduction
    hSource
    MaxCut.maxCutStructuredToBinaryStructuredTMKarpReduction
    hTarget

end Karp21
end ComplexityReduction
