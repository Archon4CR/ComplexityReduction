/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.SAT.ThreeSAT
import ComplexityReduction.Combinatorics.Graph.Basic
import ComplexityReduction.Combinatorics.Graph.Digraph
import ComplexityReduction.Combinatorics.Graph.WeightedGraph
import ComplexityReduction.Combinatorics.SetSystem
import ComplexityReduction.Combinatorics.IntegerProgramming
import ComplexityReduction.Combinatorics.Scheduling
import ComplexityReduction.Combinatorics.Knapsack
import ComplexityReduction.Karp21.GraphStructuredTM
import ComplexityReduction.Karp21.Satisfiability
import ComplexityReduction.Karp21.ThreeSATFiniteVerifierTMFormula
import ComplexityReduction.Karp21.ThreeSATFiniteVerifierTMStandard
import ComplexityReduction.Karp21.ThreeSATTMRoot
import ComplexityReduction.Karp21.HittingSet
import ComplexityReduction.Karp21.MaxCut
import ComplexityReduction.Karp21.FeedbackNodeSet
import ComplexityReduction.Karp21.FeedbackNodeSetStructuredTM
import ComplexityReduction.Karp21.FeedbackArcSet
import ComplexityReduction.Karp21.FeedbackArcSetStructuredTM
import ComplexityReduction.Karp21.DirectedHamiltonianCircuit
import ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM
import ComplexityReduction.Karp21.UndirectedHamiltonianCircuit
import ComplexityReduction.Karp21.UndirectedHamiltonianCircuitStructuredTM
import ComplexityReduction.Karp21.SetPacking
import ComplexityReduction.Karp21.ExactCover
import ComplexityReduction.Karp21.ExactCover.StructuredTM.Assembly
import ComplexityReduction.Karp21.ExactCover.StructuredTM.ViaCNF
import ComplexityReduction.Karp21.ThreeDimensionalMatching
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM
import ComplexityReduction.Karp21.JobSequencing
import ComplexityReduction.Karp21.JobSequencingStructuredTM
import ComplexityReduction.Karp21.JobSequencingBinaryStructuredTM
import ComplexityReduction.Karp21.Knapsack.StructuredTM
import ComplexityReduction.Karp21.SteinerTree
import ComplexityReduction.Karp21.SteinerTreeStructuredTM
import ComplexityReduction.Karp21.ChromaticNumber
import ComplexityReduction.Karp21.CliqueCover
import ComplexityReduction.Karp21.StructuredChains

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
