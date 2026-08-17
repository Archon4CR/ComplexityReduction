-- Aggregation module for ComplexityReduction.Karp21
-- Auto-generated: imports all submodules.

import ComplexityReduction.Karp21.Basic
import ComplexityReduction.Karp21.ChromaticNumber
import ComplexityReduction.Karp21.ChromaticNumber.Part1
import ComplexityReduction.Karp21.ChromaticNumber.Part2
import ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute
import ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute.ClauseEdges
import ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute.ClauseFold
import ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute.TextbookMap
import ComplexityReduction.Karp21.Clique
import ComplexityReduction.Karp21.Clique.Part1
import ComplexityReduction.Karp21.Clique.Part10
import ComplexityReduction.Karp21.Clique.Part2
import ComplexityReduction.Karp21.Clique.Part3
import ComplexityReduction.Karp21.Clique.Part4
import ComplexityReduction.Karp21.Clique.Part5
import ComplexityReduction.Karp21.Clique.Part6
import ComplexityReduction.Karp21.Clique.Part7
import ComplexityReduction.Karp21.Clique.Part8
import ComplexityReduction.Karp21.Clique.Part9
import ComplexityReduction.Karp21.CliqueCover
import ComplexityReduction.Karp21.DirectedHamiltonianCircuit
import ComplexityReduction.Karp21.DirectedHamiltonianCircuit.Part1
import ComplexityReduction.Karp21.DirectedHamiltonianCircuit.Part2
import ComplexityReduction.Karp21.DirectedHamiltonianCircuit.Part3
import ComplexityReduction.Karp21.DirectedHamiltonianCircuit.Part4
import ComplexityReduction.Karp21.DirectedHamiltonianCircuit.Part5
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.ChainAssembly
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.ChainAssemblySemantics
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.ChainProductSemantics
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.CrossAssembly
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.CrossAssemblyOuter
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EdgeAssembly
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitAllSlotsExitTM
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitAllSlotsTM
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitAssembly
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitBoundaryExitSemantics
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitBoundaryExitTM
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitBoundarySemantics
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitBoundaryTM
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitProductSemantics
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitTM
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.FinalAssemblyTM
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.FoldTM
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.GuardedOutputTM
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.OuterRows
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.RowScan
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.SelectorSkipTM
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.Semantics
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.TracksTM
import ComplexityReduction.Karp21.ExactCover
import ComplexityReduction.Karp21.ExactCover.Part1
import ComplexityReduction.Karp21.ExactCover.Part2
import ComplexityReduction.Karp21.ExactCover.Part3
import ComplexityReduction.Karp21.ExactCover.StructuredTM
import ComplexityReduction.Karp21.ExactCover.StructuredTM.Assembly
import ComplexityReduction.Karp21.ExactCover.StructuredTM.BlockFamilies
import ComplexityReduction.Karp21.ExactCover.StructuredTM.BlockInputFamily
import ComplexityReduction.Karp21.ExactCover.StructuredTM.BlockInputs
import ComplexityReduction.Karp21.ExactCover.StructuredTM.ChoiceBlock
import ComplexityReduction.Karp21.ExactCover.StructuredTM.EdgeCode
import ComplexityReduction.Karp21.ExactCover.StructuredTM.FillerBlock
import ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.Assembly
import ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.AtLeast
import ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.AtMostChoice
import ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.AtMostSlot
import ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.Coverage
import ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.CoverageClause
import ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.CoverageSlot
import ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.Literals
import ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.SlotClauses
import ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.SlotFor
import ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.Slots
import ComplexityReduction.Karp21.ExactCover.StructuredTM.ViaCNF
import ComplexityReduction.Karp21.ExactEncodedSuffixDecodersTM
import ComplexityReduction.Karp21.FeedbackArcSet
import ComplexityReduction.Karp21.FeedbackArcSetStructuredTM
import ComplexityReduction.Karp21.FeedbackNodeSet
import ComplexityReduction.Karp21.FeedbackNodeSetStructuredTM
import ComplexityReduction.Karp21.FiniteBoolSuffixDecodersTM
import ComplexityReduction.Karp21.FiniteWitness
import ComplexityReduction.Karp21.GraphStructuredTM
import ComplexityReduction.Karp21.GraphStructuredTM.ComplementEdges
import ComplexityReduction.Karp21.GraphStructuredTM.EdgeScan
import ComplexityReduction.Karp21.GraphStructuredTM.PairCandidates
import ComplexityReduction.Karp21.GraphStructuredTM.Projections
import ComplexityReduction.Karp21.GraphStructuredTM.Range
import ComplexityReduction.Karp21.GraphStructuredTM.StrictPairs
import ComplexityReduction.Karp21.HittingSet
import ComplexityReduction.Karp21.HittingSet.Base
import ComplexityReduction.Karp21.HittingSet.FamilyRunner
import ComplexityReduction.Karp21.HittingSet.IndexRunner
import ComplexityReduction.Karp21.HittingSet.MembershipRunner
import ComplexityReduction.Karp21.HittingSet.StructuredRoute
import ComplexityReduction.Karp21.JobSequencing
import ComplexityReduction.Karp21.JobSequencingBinaryStructuredTM
import ComplexityReduction.Karp21.JobSequencingStructuredTM
import ComplexityReduction.Karp21.Knapsack
import ComplexityReduction.Karp21.Knapsack.Part1
import ComplexityReduction.Karp21.Knapsack.Part2
import ComplexityReduction.Karp21.Knapsack.Part3
import ComplexityReduction.Karp21.Knapsack.Part4
import ComplexityReduction.Karp21.Knapsack.Part5
import ComplexityReduction.Karp21.Knapsack.StructuredTM
import ComplexityReduction.Karp21.Knapsack.StructuredTM.Assembly
import ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryAdd
import ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryAddMachine
import ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryAddTM
import ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryArithmetic
import ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryBitLength
import ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryBitsList
import ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryCompare
import ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryCompareTM
import ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryLogic
import ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryMul
import ComplexityReduction.Karp21.Knapsack.StructuredTM.BinarySub
import ComplexityReduction.Karp21.Knapsack.StructuredTM.BinarySubMachine
import ComplexityReduction.Karp21.Knapsack.StructuredTM.BinarySubTM
import ComplexityReduction.Karp21.Knapsack.StructuredTM.ChoiceDigits
import ComplexityReduction.Karp21.Knapsack.StructuredTM.CodeAssembly
import ComplexityReduction.Karp21.Knapsack.StructuredTM.CodeGeneration
import ComplexityReduction.Karp21.Knapsack.StructuredTM.ConstraintBound
import ComplexityReduction.Karp21.Knapsack.StructuredTM.DigitCode
import ComplexityReduction.Karp21.Knapsack.StructuredTM.DigitCodeList
import ComplexityReduction.Karp21.Knapsack.StructuredTM.Front
import ComplexityReduction.Karp21.Knapsack.StructuredTM.ItemDigits
import ComplexityReduction.Karp21.Knapsack.StructuredTM.ItemVectorAssembly
import ComplexityReduction.Karp21.Knapsack.StructuredTM.ListLength
import ComplexityReduction.Karp21.Knapsack.StructuredTM.ListNat
import ComplexityReduction.Karp21.Knapsack.StructuredTM.RowLookup
import ComplexityReduction.Karp21.Knapsack.StructuredTM.RowNegativeShift
import ComplexityReduction.Karp21.Knapsack.StructuredTM.SignedParts
import ComplexityReduction.Karp21.Knapsack.StructuredTM.SlackDigits
import ComplexityReduction.Karp21.Knapsack.StructuredTM.SlackItemVectors
import ComplexityReduction.Karp21.Knapsack.StructuredTM.SlackPowers
import ComplexityReduction.Karp21.Knapsack.StructuredTM.SlackVectors
import ComplexityReduction.Karp21.Knapsack.StructuredTM.TargetDigits
import ComplexityReduction.Karp21.Knapsack.StructuredTM.UnaryToBinary
import ComplexityReduction.Karp21.ListLookupTM
import ComplexityReduction.Karp21.MaxCut
import ComplexityReduction.Karp21.MaxCut.Part1
import ComplexityReduction.Karp21.MaxCut.Part2
import ComplexityReduction.Karp21.MaxCut.StructuredTM.Assembly
import ComplexityReduction.Karp21.MaxCut.StructuredTM.EdgeBlocks
import ComplexityReduction.Karp21.MaxCut.StructuredTM.Lookup
import ComplexityReduction.Karp21.MaxCut.StructuredTM.PairInstructions
import ComplexityReduction.Karp21.MaxCut.StructuredTM.Pairs
import ComplexityReduction.Karp21.MaxCut.StructuredTM.Replicate
import ComplexityReduction.Karp21.MaxCut.StructuredTM.UnaryToBinary
import ComplexityReduction.Karp21.NatListSplitTM
import ComplexityReduction.Karp21.NatPairTM
import ComplexityReduction.Karp21.PackagedCatalog
import ComplexityReduction.Karp21.PackagedCompleteness
import ComplexityReduction.Karp21.PackagedEdgeTransfers
import ComplexityReduction.Karp21.PackagedMembership
import ComplexityReduction.Karp21.PackagedMembershipChromaticNumber
import ComplexityReduction.Karp21.PackagedMembershipChromaticNumberFlat
import ComplexityReduction.Karp21.PackagedMembershipClique
import ComplexityReduction.Karp21.PackagedMembershipCliqueCover
import ComplexityReduction.Karp21.PackagedMembershipCliqueCoverFlat
import ComplexityReduction.Karp21.PackagedMembershipDirectedHamiltonianCircuit
import ComplexityReduction.Karp21.PackagedMembershipDirectedHamiltonianCircuitCycle
import ComplexityReduction.Karp21.PackagedMembershipDirectedHamiltonianCircuitCycleTM
import ComplexityReduction.Karp21.PackagedMembershipDirectedHamiltonianCircuitEdge
import ComplexityReduction.Karp21.PackagedMembershipExactCover
import ComplexityReduction.Karp21.PackagedMembershipExactCoverAtMostOne
import ComplexityReduction.Karp21.PackagedMembershipFeedbackArcSet
import ComplexityReduction.Karp21.PackagedMembershipFeedbackArcSetFlat
import ComplexityReduction.Karp21.PackagedMembershipFeedbackArcSetRankRunner
import ComplexityReduction.Karp21.PackagedMembershipFeedbackArcSetRemovedRunner
import ComplexityReduction.Karp21.PackagedMembershipFeedbackNodeSet
import ComplexityReduction.Karp21.PackagedMembershipFeedbackNodeSetFlat
import ComplexityReduction.Karp21.PackagedMembershipFeedbackNodeSetRunner
import ComplexityReduction.Karp21.PackagedMembershipJobSequencing
import ComplexityReduction.Karp21.PackagedMembershipJobSequencingBinary
import ComplexityReduction.Karp21.PackagedMembershipJobSequencingVerifier
import ComplexityReduction.Karp21.PackagedMembershipKnapsackBinary
import ComplexityReduction.Karp21.PackagedMembershipMaxCut
import ComplexityReduction.Karp21.PackagedMembershipMaxCutBinary
import ComplexityReduction.Karp21.PackagedMembershipPartition
import ComplexityReduction.Karp21.PackagedMembershipPartitionBinary
import ComplexityReduction.Karp21.PackagedMembershipSetCovering
import ComplexityReduction.Karp21.PackagedMembershipSetPacking
import ComplexityReduction.Karp21.PackagedMembershipSetPackingEq
import ComplexityReduction.Karp21.PackagedMembershipSetPackingScan
import ComplexityReduction.Karp21.PackagedMembershipSetSystem
import ComplexityReduction.Karp21.PackagedMembershipSetSystemBounds
import ComplexityReduction.Karp21.PackagedMembershipSteinerTree
import ComplexityReduction.Karp21.PackagedMembershipSteinerTreeEdgeScan
import ComplexityReduction.Karp21.PackagedMembershipSteinerTreeFlat
import ComplexityReduction.Karp21.PackagedMembershipSteinerTreeGraphScan
import ComplexityReduction.Karp21.PackagedMembershipSteinerTreePath
import ComplexityReduction.Karp21.PackagedMembershipSteinerTreePathEntry
import ComplexityReduction.Karp21.PackagedMembershipSteinerTreeTerminal
import ComplexityReduction.Karp21.PackagedMembershipThreeDimensionalMatching
import ComplexityReduction.Karp21.PackagedMembershipThreeDimensionalMatchingCore
import ComplexityReduction.Karp21.PackagedMembershipThreeDimensionalMatchingIndex
import ComplexityReduction.Karp21.PackagedMembershipThreeDimensionalMatchingScan
import ComplexityReduction.Karp21.PackagedMembershipUndirectedHamiltonianCircuit
import ComplexityReduction.Karp21.PackagedMembershipVertexCover
import ComplexityReduction.Karp21.Partition
import ComplexityReduction.Karp21.Partition.Part1
import ComplexityReduction.Karp21.Partition.Part2
import ComplexityReduction.Karp21.Partition.Part3
import ComplexityReduction.Karp21.Partition.StructuredTM.Arithmetic
import ComplexityReduction.Karp21.Partition.StructuredTM.ExactWrapper
import ComplexityReduction.Karp21.Partition.StructuredTM.KnapsackWeights
import ComplexityReduction.Karp21.Partition.StructuredTM.ProductSumChoice
import ComplexityReduction.Karp21.Partition.StructuredTM.SubsetCore
import ComplexityReduction.Karp21.Partition.StructuredTM.SubsetWeights
import ComplexityReduction.Karp21.Partition.StructuredTM.UnaryToBinary
import ComplexityReduction.Karp21.PullbackFiniteBoolSuffixDecodersTM
import ComplexityReduction.Karp21.Satisfiability
import ComplexityReduction.Karp21.Satisfiability.CNFSplit
import ComplexityReduction.Karp21.Satisfiability.CNFSplit.Part1
import ComplexityReduction.Karp21.Satisfiability.CNFSplit.Part2
import ComplexityReduction.Karp21.Satisfiability.CNFSplit.Part3
import ComplexityReduction.Karp21.Satisfiability.CNFSplit.Part4
import ComplexityReduction.Karp21.Satisfiability.Encoding
import ComplexityReduction.Karp21.Satisfiability.Reductions
import ComplexityReduction.Karp21.Satisfiability.SplitWith
import ComplexityReduction.Karp21.Satisfiability.SplitWith.BranchInputChoice
import ComplexityReduction.Karp21.Satisfiability.SplitWith.BranchTraceStep
import ComplexityReduction.Karp21.Satisfiability.SplitWith.Core
import ComplexityReduction.Karp21.Satisfiability.SplitWith.ListUncons
import ComplexityReduction.Karp21.Satisfiability.SplitWith.LongTrace
import ComplexityReduction.Karp21.Satisfiability.SplitWith.LongTrace.Part1
import ComplexityReduction.Karp21.Satisfiability.SplitWith.LongTrace.Part2
import ComplexityReduction.Karp21.Satisfiability.SplitWith.RunnerFold
import ComplexityReduction.Karp21.Satisfiability.SplitWith.RunnerStepChoice
import ComplexityReduction.Karp21.Satisfiability.SplitWith.RunnerStepChoice.Part1
import ComplexityReduction.Karp21.Satisfiability.SplitWith.RunnerStepChoice.Part2
import ComplexityReduction.Karp21.Satisfiability.SplitWith.SizeAndFinalMaps
import ComplexityReduction.Karp21.Satisfiability.SplitWith.TaggedDispatch
import ComplexityReduction.Karp21.Satisfiability.SplitWith.TaggedDispatch.Part1
import ComplexityReduction.Karp21.Satisfiability.SplitWith.TaggedDispatch.Part2
import ComplexityReduction.Karp21.Satisfiability.SplitWith.TaggedDispatch.Part3
import ComplexityReduction.Karp21.Satisfiability.SplitWith.TaggedDispatch.Part4
import ComplexityReduction.Karp21.Satisfiability.SplitWith.TraceInstructions
import ComplexityReduction.Karp21.Satisfiability.SplitWith.TraceLoop
import ComplexityReduction.Karp21.SatisfiabilitySuffixDecoderTM
import ComplexityReduction.Karp21.SetCovering
import ComplexityReduction.Karp21.SetCovering.Base
import ComplexityReduction.Karp21.SetCovering.FamilyRunner
import ComplexityReduction.Karp21.SetCovering.IncidentRunner
import ComplexityReduction.Karp21.SetCovering.StructuredRoute
import ComplexityReduction.Karp21.SetPacking
import ComplexityReduction.Karp21.SetPacking.Base
import ComplexityReduction.Karp21.SetPacking.FamilyRunner
import ComplexityReduction.Karp21.SetPacking.IncidentRunner
import ComplexityReduction.Karp21.SetPacking.StructuredRoute
import ComplexityReduction.Karp21.SetPacking.StructuredTMRoute
import ComplexityReduction.Karp21.SetPacking.TMRoute
import ComplexityReduction.Karp21.SteinerTree
import ComplexityReduction.Karp21.SteinerTree.Part1
import ComplexityReduction.Karp21.SteinerTree.Part2
import ComplexityReduction.Karp21.SteinerTreeStructuredTM
import ComplexityReduction.Karp21.SteinerTreeStructuredTM.Assembly
import ComplexityReduction.Karp21.SteinerTreeStructuredTM.EdgeBlocks
import ComplexityReduction.Karp21.SteinerTreeStructuredTM.FamilyEdges
import ComplexityReduction.Karp21.SteinerTreeStructuredTM.Lookup
import ComplexityReduction.Karp21.SteinerTreeStructuredTM.Projections
import ComplexityReduction.Karp21.SteinerTreeStructuredTM.Support
import ComplexityReduction.Karp21.SteinerTreeStructuredTM.Terminals
import ComplexityReduction.Karp21.SteinerTreeStructuredTM.WellFormed
import ComplexityReduction.Karp21.StructuredChains
import ComplexityReduction.Karp21.ThreeDimensionalMatching
import ComplexityReduction.Karp21.ThreeDimensionalMatching.Part1
import ComplexityReduction.Karp21.ThreeDimensionalMatching.Part2
import ComplexityReduction.Karp21.ThreeDimensionalMatching.Part3
import ComplexityReduction.Karp21.ThreeDimensionalMatching.Part4
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.Alpha
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.AlphaFamily
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.Assembly
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.CoverBlocks
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.CoverFamily
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.CoverTriples
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.FillerBetaFamily
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.FillerBlocks
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.FillerBlockSemantics
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.FillerFamily
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.FillerTriples
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.Guard
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.NonAlphaFamily
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.PositionBlocks
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.PositionCodes
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.PositionFamily
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.Projections
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.Support
import ComplexityReduction.Karp21.ThreeSATFiniteVerifierTM
import ComplexityReduction.Karp21.ThreeSATFiniteVerifierTMFormula
import ComplexityReduction.Karp21.ThreeSATFiniteVerifierTMStandard
import ComplexityReduction.Karp21.ThreeSATStandardParser
import ComplexityReduction.Karp21.ThreeSATStandardParserTM
import ComplexityReduction.Karp21.ThreeSATStructuredEncoderTM
import ComplexityReduction.Karp21.ThreeSATSuffixDecoderTM
import ComplexityReduction.Karp21.ThreeSATTMRoot
import ComplexityReduction.Karp21.ThreeSATTMRootDecoding
import ComplexityReduction.Karp21.UndirectedHamiltonianCircuit
import ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.Part1
import ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.Part2
import ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.Part3
import ComplexityReduction.Karp21.UndirectedHamiltonianCircuitStructuredTM
import ComplexityReduction.Karp21.VertexCover
import ComplexityReduction.Karp21.ZeroOneIP
import ComplexityReduction.Karp21.ZeroOneIP.Base
import ComplexityReduction.Karp21.ZeroOneIP.StructuredTM
import ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.Assembly
import ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.Bound
import ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.ClauseConstraint
import ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.Coeff
import ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.ConstraintsFold
import ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.LiteralRow
import ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.Prefix
import ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.PrefixRow
import ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.Rows
import ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.UnaryToBinary


/-!
Karp's 21 NP-complete problem inventory.

This module fixes local names, encoded decision-problem symbols, and reference
metadata for the 21 targets from Richard M. Karp's 1972 paper.  It deliberately
does not assert unproved NP-completeness wrappers for the new combinatorial
targets; those wrappers belong in staged reduction files once their maps and
semantic theorems are proved.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-- Canonical enum for Karp's 21 problem names in the order used by this library. -/
inductive Problem where
  | satisfiability
  | zeroOneIntegerProgramming
  | clique
  | setPacking
  | vertexCover
  | setCovering
  | feedbackNodeSet
  | feedbackArcSet
  | directedHamiltonianCircuit
  | undirectedHamiltonianCircuit
  | threeSatisfiability
  | chromaticNumber
  | cliqueCover
  | exactCover
  | hittingSet
  | steinerTree
  | threeDimensionalMatching
  | knapsack
  | jobSequencing
  | partition
  | maxCut
  deriving DecidableEq, Repr

namespace Problem

/-- Inventory list for length checks and catalog generation. -/
def all : List Problem :=
  [ satisfiability
  , zeroOneIntegerProgramming
  , clique
  , setPacking
  , vertexCover
  , setCovering
  , feedbackNodeSet
  , feedbackArcSet
  , directedHamiltonianCircuit
  , undirectedHamiltonianCircuit
  , threeSatisfiability
  , chromaticNumber
  , cliqueCover
  , exactCover
  , hittingSet
  , steinerTree
  , threeDimensionalMatching
  , knapsack
  , jobSequencing
  , partition
  , maxCut
  ]

theorem all_length : all.length = 21 :=
  rfl

/-- Karp paper display name. -/
def paperName : Problem → String
  | satisfiability => "Satisfiability"
  | zeroOneIntegerProgramming => "0-1 Integer Programming"
  | clique => "Clique"
  | setPacking => "Set Packing"
  | vertexCover => "Vertex Cover"
  | setCovering => "Set Covering"
  | feedbackNodeSet => "Feedback Node Set"
  | feedbackArcSet => "Feedback Arc Set"
  | directedHamiltonianCircuit => "Directed Hamiltonian Circuit"
  | undirectedHamiltonianCircuit => "Undirected Hamiltonian Circuit"
  | threeSatisfiability => "3-Satisfiability"
  | chromaticNumber => "Chromatic Number"
  | cliqueCover => "Clique Cover"
  | exactCover => "Exact Cover"
  | hittingSet => "Hitting Set"
  | steinerTree => "Steiner Tree"
  | threeDimensionalMatching => "3-Dimensional Matching"
  | knapsack => "Knapsack"
  | jobSequencing => "Job Sequencing"
  | partition => "Partition"
  | maxCut => "Max Cut"

/-- Stable machine tag used by docs, manifests, and audit tooling. -/
def tag : Problem → String
  | satisfiability => "satisfiability"
  | zeroOneIntegerProgramming => "zero_one_integer_programming"
  | clique => "clique"
  | setPacking => "set_packing"
  | vertexCover => "vertex_cover"
  | setCovering => "set_covering"
  | feedbackNodeSet => "feedback_node_set"
  | feedbackArcSet => "feedback_arc_set"
  | directedHamiltonianCircuit => "directed_hamiltonian_circuit"
  | undirectedHamiltonianCircuit => "undirected_hamiltonian_circuit"
  | threeSatisfiability => "three_satisfiability"
  | chromaticNumber => "chromatic_number"
  | cliqueCover => "clique_cover"
  | exactCover => "exact_cover"
  | hittingSet => "hitting_set"
  | steinerTree => "steiner_tree"
  | threeDimensionalMatching => "three_dimensional_matching"
  | knapsack => "knapsack"
  | jobSequencing => "job_sequencing"
  | partition => "partition"
  | maxCut => "max_cut"

end Problem

/-- Metadata for one Karp 21 problem at the reusable library layer. -/
structure ProblemDescriptor where
  problem : Problem
  paperName : String
  tag : String
  localModule : String
  encodedProblemSymbol : String
  instanceSchema : String
  yesPredicate : String
  karpSource : String
  reference : String
  status : String
  deriving Repr

def satisfiabilityDescriptor : ProblemDescriptor :=
  { problem := Problem.satisfiability
    paperName := Problem.paperName Problem.satisfiability
    tag := Problem.tag Problem.satisfiability
    localModule := "ComplexityReduction.Karp21.Satisfiability"
    encodedProblemSymbol := "ComplexityReduction.Karp21.satisfiabilityDecisionProblem"
    instanceSchema := "SAT.CNF"
    yesPredicate := "SAT.CNF.Satisfiable"
    karpSource := "Cook-Levin / starting problem in Karp 1972"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15g-local-cnf-wrapper" }

def zeroOneIntegerProgrammingDescriptor : ProblemDescriptor :=
  { problem := Problem.zeroOneIntegerProgramming
    paperName := Problem.paperName Problem.zeroOneIntegerProgramming
    tag := Problem.tag Problem.zeroOneIntegerProgramming
    localModule := "ComplexityReduction.Combinatorics.IntegerProgramming"
    encodedProblemSymbol :=
      "ComplexityReduction.Combinatorics.zeroOneIntegerProgrammingDecisionProblem"
    instanceSchema := "IntegerProgrammingInput"
    yesPredicate := "ZeroOneIntegerProgramming"
    karpSource := "Satisfiability"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15x-textbook" }

def cliqueDescriptor : ProblemDescriptor :=
  { problem := Problem.clique
    paperName := Problem.paperName Problem.clique
    tag := Problem.tag Problem.clique
    localModule := "ComplexityReduction.Combinatorics.Graph.Basic"
    encodedProblemSymbol := "ComplexityReduction.Combinatorics.Graph.cliqueDecisionProblem"
    instanceSchema := "Graph.CliqueInput"
    yesPredicate := "Graph.Clique"
    karpSource := "3-Satisfiability"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15b" }

def setPackingDescriptor : ProblemDescriptor :=
  { problem := Problem.setPacking
    paperName := Problem.paperName Problem.setPacking
    tag := Problem.tag Problem.setPacking
    localModule := "ComplexityReduction.Combinatorics.SetSystem"
    encodedProblemSymbol := "ComplexityReduction.Combinatorics.setPackingDecisionProblem"
    instanceSchema := "SetPackingInput"
    yesPredicate := "SetPacking"
    karpSource := "Clique"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15e" }

def vertexCoverDescriptor : ProblemDescriptor :=
  { problem := Problem.vertexCover
    paperName := Problem.paperName Problem.vertexCover
    tag := Problem.tag Problem.vertexCover
    localModule := "ComplexityReduction.Combinatorics.Graph.Basic"
    encodedProblemSymbol := "ComplexityReduction.Combinatorics.Graph.vertexCoverDecisionProblem"
    instanceSchema := "Graph.VertexCoverInput"
    yesPredicate := "Graph.VertexCover"
    karpSource := "Clique"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15b" }

def setCoveringDescriptor : ProblemDescriptor :=
  { problem := Problem.setCovering
    paperName := Problem.paperName Problem.setCovering
    tag := Problem.tag Problem.setCovering
    localModule := "ComplexityReduction.Combinatorics.SetSystem"
    encodedProblemSymbol := "ComplexityReduction.Combinatorics.setCoveringDecisionProblem"
    instanceSchema := "SetCoveringInput"
    yesPredicate := "SetCovering"
    karpSource := "Vertex Cover"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15b" }

def feedbackNodeSetDescriptor : ProblemDescriptor :=
  { problem := Problem.feedbackNodeSet
    paperName := Problem.paperName Problem.feedbackNodeSet
    tag := Problem.tag Problem.feedbackNodeSet
    localModule := "ComplexityReduction.Combinatorics.Graph.Digraph"
    encodedProblemSymbol := "ComplexityReduction.Combinatorics.Graph.feedbackNodeSetDecisionProblem"
    instanceSchema := "Graph.FeedbackNodeSetInput"
    yesPredicate := "Graph.FeedbackNodeSet"
    karpSource := "Vertex Cover"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15d" }

def feedbackArcSetDescriptor : ProblemDescriptor :=
  { problem := Problem.feedbackArcSet
    paperName := Problem.paperName Problem.feedbackArcSet
    tag := Problem.tag Problem.feedbackArcSet
    localModule := "ComplexityReduction.Combinatorics.Graph.Digraph"
    encodedProblemSymbol := "ComplexityReduction.Combinatorics.Graph.feedbackArcSetDecisionProblem"
    instanceSchema := "Graph.FeedbackArcSetInput"
    yesPredicate := "Graph.FeedbackArcSet"
    karpSource := "Feedback Node Set"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15d" }

def directedHamiltonianCircuitDescriptor : ProblemDescriptor :=
  { problem := Problem.directedHamiltonianCircuit
    paperName := Problem.paperName Problem.directedHamiltonianCircuit
    tag := Problem.tag Problem.directedHamiltonianCircuit
    localModule := "ComplexityReduction.Combinatorics.Graph.Digraph"
    encodedProblemSymbol :=
      "ComplexityReduction.Combinatorics.Graph.directedHamiltonianCircuitDecisionProblem"
    instanceSchema := "Graph.DirectedHamiltonianCircuitInput"
    yesPredicate := "Graph.DirectedHamiltonianCircuit"
    karpSource := "Vertex Cover"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15v-textbook" }

def undirectedHamiltonianCircuitDescriptor : ProblemDescriptor :=
  { problem := Problem.undirectedHamiltonianCircuit
    paperName := Problem.paperName Problem.undirectedHamiltonianCircuit
    tag := Problem.tag Problem.undirectedHamiltonianCircuit
    localModule := "ComplexityReduction.Combinatorics.Graph.Digraph"
    encodedProblemSymbol :=
      "ComplexityReduction.Combinatorics.Graph.undirectedHamiltonianCircuitDecisionProblem"
    instanceSchema := "Graph.UndirectedHamiltonianCircuitInput"
    yesPredicate := "Graph.UndirectedHamiltonianCircuit"
    karpSource := "Directed Hamiltonian Circuit"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15w-textbook" }

def threeSatisfiabilityDescriptor : ProblemDescriptor :=
  { problem := Problem.threeSatisfiability
    paperName := Problem.paperName Problem.threeSatisfiability
    tag := Problem.tag Problem.threeSatisfiability
    localModule := "ComplexityReduction.SAT.ThreeSAT"
    encodedProblemSymbol := "ComplexityReduction.SAT.threeSATDecisionProblem"
    instanceSchema := "SAT.ThreeCNF"
    yesPredicate := "SAT.ThreeCNF.Satisfiable"
    karpSource := "Satisfiability"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "already-proved-local-complete" }

def chromaticNumberDescriptor : ProblemDescriptor :=
  { problem := Problem.chromaticNumber
    paperName := Problem.paperName Problem.chromaticNumber
    tag := Problem.tag Problem.chromaticNumber
    localModule := "ComplexityReduction.Combinatorics.Graph.Basic"
    encodedProblemSymbol :=
      "ComplexityReduction.Combinatorics.Graph.chromaticNumberDecisionProblem"
    instanceSchema := "Graph.ChromaticNumberInput"
    yesPredicate := "Graph.ChromaticNumber"
    karpSource := "3-Satisfiability"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15e" }

def cliqueCoverDescriptor : ProblemDescriptor :=
  { problem := Problem.cliqueCover
    paperName := Problem.paperName Problem.cliqueCover
    tag := Problem.tag Problem.cliqueCover
    localModule := "ComplexityReduction.Combinatorics.Graph.Basic"
    encodedProblemSymbol := "ComplexityReduction.Combinatorics.Graph.cliqueCoverDecisionProblem"
    instanceSchema := "Graph.CliqueCoverInput"
    yesPredicate := "Graph.CliqueCover"
    karpSource := "Chromatic Number"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15r-textbook" }

def exactCoverDescriptor : ProblemDescriptor :=
  { problem := Problem.exactCover
    paperName := Problem.paperName Problem.exactCover
    tag := Problem.tag Problem.exactCover
    localModule := "ComplexityReduction.Combinatorics.SetSystem"
    encodedProblemSymbol := "ComplexityReduction.Combinatorics.exactCoverDecisionProblem"
    instanceSchema := "ExactCoverInput"
    yesPredicate := "ExactCover"
    karpSource := "Set Covering"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15e" }

def hittingSetDescriptor : ProblemDescriptor :=
  { problem := Problem.hittingSet
    paperName := Problem.paperName Problem.hittingSet
    tag := Problem.tag Problem.hittingSet
    localModule := "ComplexityReduction.Combinatorics.SetSystem"
    encodedProblemSymbol := "ComplexityReduction.Combinatorics.hittingSetDecisionProblem"
    instanceSchema := "HittingSetInput"
    yesPredicate := "HittingSet"
    karpSource := "Set Covering"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15b" }

def steinerTreeDescriptor : ProblemDescriptor :=
  { problem := Problem.steinerTree
    paperName := Problem.paperName Problem.steinerTree
    tag := Problem.tag Problem.steinerTree
    localModule := "ComplexityReduction.Combinatorics.Graph.WeightedGraph"
    encodedProblemSymbol := "ComplexityReduction.Combinatorics.Graph.steinerTreeDecisionProblem"
    instanceSchema := "Graph.SteinerTreeInput"
    yesPredicate := "Graph.SteinerTree"
    karpSource := "Exact Cover"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15e" }

def threeDimensionalMatchingDescriptor : ProblemDescriptor :=
  { problem := Problem.threeDimensionalMatching
    paperName := Problem.paperName Problem.threeDimensionalMatching
    tag := Problem.tag Problem.threeDimensionalMatching
    localModule := "ComplexityReduction.Combinatorics.SetSystem"
    encodedProblemSymbol :=
      "ComplexityReduction.Combinatorics.threeDimensionalMatchingDecisionProblem"
    instanceSchema := "ThreeDimensionalMatchingInput"
    yesPredicate := "ThreeDimensionalMatching"
    karpSource := "Exact Cover"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15e" }

def knapsackDescriptor : ProblemDescriptor :=
  { problem := Problem.knapsack
    paperName := Problem.paperName Problem.knapsack
    tag := Problem.tag Problem.knapsack
    localModule := "ComplexityReduction.Combinatorics.Knapsack"
    encodedProblemSymbol := "ComplexityReduction.Combinatorics.knapsackKarpDecisionProblem"
    instanceSchema := "KnapsackInput"
    yesPredicate := "Knapsack"
    karpSource := "0-1 Integer Programming"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15c" }

def jobSequencingDescriptor : ProblemDescriptor :=
  { problem := Problem.jobSequencing
    paperName := Problem.paperName Problem.jobSequencing
    tag := Problem.tag Problem.jobSequencing
    localModule := "ComplexityReduction.Combinatorics.Scheduling"
    encodedProblemSymbol := "ComplexityReduction.Combinatorics.jobSequencingDecisionProblem"
    instanceSchema := "JobSequencingInput"
    yesPredicate := "JobSequencing"
    karpSource := "Knapsack"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15p-textbook" }

def partitionDescriptor : ProblemDescriptor :=
  { problem := Problem.partition
    paperName := Problem.paperName Problem.partition
    tag := Problem.tag Problem.partition
    localModule := "ComplexityReduction.Combinatorics.Knapsack"
    encodedProblemSymbol := "ComplexityReduction.Combinatorics.partitionDecisionProblem"
    instanceSchema := "PartitionInput"
    yesPredicate := "Partition"
    karpSource := "Knapsack"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15c" }

def maxCutDescriptor : ProblemDescriptor :=
  { problem := Problem.maxCut
    paperName := Problem.paperName Problem.maxCut
    tag := Problem.tag Problem.maxCut
    localModule := "ComplexityReduction.Combinatorics.Graph.Basic"
    encodedProblemSymbol := "ComplexityReduction.Combinatorics.Graph.maxCutDecisionProblem"
    instanceSchema := "Graph.MaxCutInput"
    yesPredicate := "Graph.MaxCut"
    karpSource := "Partition"
    reference := "reference/karp-1972-reducibility-among-combinatorial-problems.pdf"
    status := "proved-p15c" }

/-- Descriptor inventory matching `Problem.all`. -/
def problemDescriptors : List ProblemDescriptor :=
  [ satisfiabilityDescriptor
  , zeroOneIntegerProgrammingDescriptor
  , cliqueDescriptor
  , setPackingDescriptor
  , vertexCoverDescriptor
  , setCoveringDescriptor
  , feedbackNodeSetDescriptor
  , feedbackArcSetDescriptor
  , directedHamiltonianCircuitDescriptor
  , undirectedHamiltonianCircuitDescriptor
  , threeSatisfiabilityDescriptor
  , chromaticNumberDescriptor
  , cliqueCoverDescriptor
  , exactCoverDescriptor
  , hittingSetDescriptor
  , steinerTreeDescriptor
  , threeDimensionalMatchingDescriptor
  , knapsackDescriptor
  , jobSequencingDescriptor
  , partitionDescriptor
  , maxCutDescriptor
  ]

theorem problemDescriptors_length :
    problemDescriptors.length = 21 :=
  rfl

end Karp21
end ComplexityReduction
