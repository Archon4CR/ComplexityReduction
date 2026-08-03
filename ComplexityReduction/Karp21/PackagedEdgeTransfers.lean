/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21
import ComplexityReduction.Karp21.ThreeSATTMRootDecoding

/-!
Packaged standard-TM NP-completeness transfer witnesses for Karp21 structured
edges.

These declarations only transport hardness along already-verified direct
`TMKarpReduction`s.  They deliberately keep the target `TMInNP` membership
obligation explicit.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/--
All six explicit Cook-Levin package domains transfer along one direct
standard-TM Karp reduction, provided the target has an ordinary direct-TM NP
verifier.
-/
structure PackagedTMNPCompleteEdge (A B : EncodedDecisionProblem) where
  checkedSuffixValidity :
    SAT.TMNPCompleteEncWithCheckedSuffixValidity A →
      TMInNP B → SAT.TMNPCompleteEncWithCheckedSuffixValidity B
  rawInputSound :
    SAT.TMNPCompleteEncWithRawInputSound A →
      TMInNP B → SAT.TMNPCompleteEncWithRawInputSound B
  rawInputNormalizer :
    SAT.TMNPCompleteEncWithRawInputNormalizer A →
      TMInNP B → SAT.TMNPCompleteEncWithRawInputNormalizer B
  rawSuffixNormalizer :
    SAT.TMNPCompleteEncWithRawSuffixNormalizer A →
      TMInNP B → SAT.TMNPCompleteEncWithRawSuffixNormalizer B
  checkedSuffixDecoder :
    SAT.TMNPCompleteEncWithCheckedSuffixDecoder A →
      TMInNP B → SAT.TMNPCompleteEncWithCheckedSuffixDecoder B
  rawSuffixDecodingNormalizer :
    SAT.TMNPCompleteEncWithRawSuffixDecodingNormalizer A →
      TMInNP B → SAT.TMNPCompleteEncWithRawSuffixDecodingNormalizer B

namespace PackagedTMNPCompleteEdge

/-- Build packaged-completeness transfer data from a direct TM Karp reduction. -/
def ofTMKarpReduction {A B : EncodedDecisionProblem} (r : TMKarpReduction A B) :
    PackagedTMNPCompleteEdge A B where
  checkedSuffixValidity hA hB :=
    SAT.TMNPCompleteEncWithCheckedSuffixValidity.transfer hA ⟨r⟩ hB
  rawInputSound hA hB :=
    SAT.TMNPCompleteEncWithRawInputSound.transfer hA ⟨r⟩ hB
  rawInputNormalizer hA hB :=
    SAT.TMNPCompleteEncWithRawInputNormalizer.transfer hA ⟨r⟩ hB
  rawSuffixNormalizer hA hB :=
    SAT.TMNPCompleteEncWithRawSuffixNormalizer.transfer hA ⟨r⟩ hB
  checkedSuffixDecoder hA hB :=
    SAT.TMNPCompleteEncWithCheckedSuffixDecoder.transfer hA ⟨r⟩ hB
  rawSuffixDecodingNormalizer hA hB :=
    SAT.TMNPCompleteEncWithRawSuffixDecodingNormalizer.transfer hA ⟨r⟩ hB

end PackagedTMNPCompleteEdge

/-! ### Karp21 structured edge witnesses -/

noncomputable def satisfiabilityStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      threeSATStructuredDecisionProblem
      satisfiabilityStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction threeSATToCNFSATStructuredTMKarpReduction

noncomputable def zeroOneIPStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      threeSATStructuredDecisionProblem
      zeroOneIntegerProgrammingStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    ZeroOneIP.threeSATToZeroOneIPStructuredTMKarpReduction

noncomputable def cliqueStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      threeSATStructuredDecisionProblem
      cliqueStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction Clique.threeSATToCliqueStructuredTMKarpReduction

noncomputable def setPackingStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      cliqueStructuredDecisionProblem
      setPackingStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    SetPacking.cliqueToSetPackingStructuredTMKarpReduction

noncomputable def vertexCoverStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      cliqueStructuredDecisionProblem
      vertexCoverStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    VertexCover.cliqueToVertexCoverStructuredTMKarpReduction

noncomputable def setCoveringStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      vertexCoverStructuredDecisionProblem
      setCoveringStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    SetCovering.vertexCoverToSetCoveringStructuredTMKarpReduction

noncomputable def feedbackNodeSetStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      vertexCoverStructuredDecisionProblem
      feedbackNodeSetStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    FeedbackNodeSet.vertexCoverToFeedbackNodeSetStructuredTMKarpReduction

noncomputable def feedbackArcSetStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      feedbackNodeSetStructuredDecisionProblem
      feedbackArcSetStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    FeedbackArcSet.feedbackNodeSetToFeedbackArcSetStructuredTMKarpReduction

noncomputable def directedHamiltonianCircuitStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      vertexCoverStructuredDecisionProblem
      directedHamiltonianCircuitStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    DirectedHamiltonianCircuit.vertexCoverToDirectedHamiltonianCircuitStructuredTMKarpReduction

noncomputable def undirectedHamiltonianCircuitStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      directedHamiltonianCircuitStructuredDecisionProblem
      undirectedHamiltonianCircuitStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    UndirectedHamiltonianCircuit.directedToUndirectedHamiltonianCircuitStructuredTMKarpReduction

noncomputable def chromaticNumberStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      threeSATStructuredDecisionProblem
      chromaticNumberStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    ChromaticNumber.threeSATToChromaticNumberStructuredTMKarpReduction

noncomputable def cliqueCoverStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      chromaticNumberStructuredDecisionProblem
      cliqueCoverStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    CliqueCover.chromaticNumberToCliqueCoverStructuredTMKarpReduction

noncomputable def exactCoverStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      setCoveringStructuredDecisionProblem
      exactCoverStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    ExactCover.setCoveringToExactCoverViaCNFStructuredTMKarpReduction

noncomputable def hittingSetStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      setCoveringStructuredDecisionProblem
      hittingSetStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    HittingSet.setCoveringToHittingSetStructuredTMKarpReduction

noncomputable def steinerTreeStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      exactCoverStructuredDecisionProblem
      steinerTreeStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    SteinerTree.exactCoverToSteinerTreeCompactStructuredTMKarpReduction

noncomputable def threeDimensionalMatchingStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      exactCoverStructuredDecisionProblem
      threeDimensionalMatchingStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    ThreeDimensionalMatching.exactCoverToThreeDimensionalMatchingCompactStructuredTMKarpReduction

noncomputable def knapsackBinaryStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      zeroOneIntegerProgrammingBinaryStructuredDecisionProblem
      knapsackBinaryStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    Knapsack.zeroOneIPToKnapsackBinaryStructuredTMKarpReduction

noncomputable def jobSequencingBinaryStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      knapsackBinaryStructuredDecisionProblem
      jobSequencingBinaryStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    JobSequencing.knapsackToJobSequencingBinaryStructuredTMKarpReduction

noncomputable def jobSequencingStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      knapsackStructuredDecisionProblem
      jobSequencingStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    JobSequencing.knapsackToJobSequencingStructuredTMKarpReduction

noncomputable def partitionStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      knapsackStructuredDecisionProblem
      partitionStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    Partition.knapsackToPartitionStructuredTMKarpReduction

noncomputable def maxCutStructuredPackagedTMNPCompleteEdge :
    PackagedTMNPCompleteEdge
      partitionStructuredDecisionProblem
      maxCutStructuredDecisionProblem :=
  PackagedTMNPCompleteEdge.ofTMKarpReduction
    MaxCut.partitionToMaxCutStructuredTMKarpReduction

end Karp21
end ComplexityReduction
