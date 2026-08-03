/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21

/-!
Tool-visible reference catalog scaffold for Karp's 21 NP-complete targets.

Entries whose reductions are not yet proved intentionally expose no theorem
symbol.  This prevents generated artifacts from treating the reference
inventory as a verified NP-completeness theorem surface.
-/

namespace ComplexityReduction
namespace Targets

/-- Target-catalog metadata for one Karp 21 problem. -/
structure Karp21TargetDescriptor where
  problem : Karp21.Problem
  name : String
  tag : String
  problemSymbol : String
  membershipSymbol : Option String
  incomingReductionSymbol : Option String
  completenessSymbol : Option String
  routeStyle : String := "current_schema"
  textbookGadgetTheorem : Option String := none
  fallbackCompletenessSymbol : Option String := none
  structuredProblemSymbol : Option String := none
  encodingConformanceTheorem : Option String := none
  acceptsEncodingTheorem : Option String := none
  sourceBoundary : String
  reference : String
  referenceAnchor : String := "Karp 1972, pp. 85-103"
  artifactEligibleByDefault : Bool
  notes : String
  deriving Repr

namespace Karp21TargetDescriptor

/-- Faithful finite-alphabet structured target used for natural-language conformance. -/
def problemStructuredProblemSymbol : Karp21.Problem → String
  | Karp21.Problem.satisfiability =>
      "ComplexityReduction.Karp21.satisfiabilityStructuredDecisionProblem"
  | Karp21.Problem.zeroOneIntegerProgramming =>
      "ComplexityReduction.Combinatorics.zeroOneIntegerProgrammingStructuredDecisionProblem"
  | Karp21.Problem.clique =>
      "ComplexityReduction.Combinatorics.Graph.cliqueStructuredDecisionProblem"
  | Karp21.Problem.setPacking =>
      "ComplexityReduction.Combinatorics.setPackingStructuredDecisionProblem"
  | Karp21.Problem.vertexCover =>
      "ComplexityReduction.Combinatorics.Graph.vertexCoverStructuredDecisionProblem"
  | Karp21.Problem.setCovering =>
      "ComplexityReduction.Combinatorics.setCoveringStructuredDecisionProblem"
  | Karp21.Problem.feedbackNodeSet =>
      "ComplexityReduction.Combinatorics.Graph.feedbackNodeSetStructuredDecisionProblem"
  | Karp21.Problem.feedbackArcSet =>
      "ComplexityReduction.Combinatorics.Graph.feedbackArcSetStructuredDecisionProblem"
  | Karp21.Problem.directedHamiltonianCircuit =>
      "ComplexityReduction.Combinatorics.Graph.directedHamiltonianCircuitStructuredDecisionProblem"
  | Karp21.Problem.undirectedHamiltonianCircuit =>
      "ComplexityReduction.Combinatorics.Graph.undirectedHamiltonianCircuitStructuredDecisionProblem"
  | Karp21.Problem.threeSatisfiability =>
      "ComplexityReduction.Karp21.threeSATStructuredDecisionProblem"
  | Karp21.Problem.chromaticNumber =>
      "ComplexityReduction.Combinatorics.Graph.chromaticNumberStructuredDecisionProblem"
  | Karp21.Problem.cliqueCover =>
      "ComplexityReduction.Combinatorics.Graph.cliqueCoverStructuredDecisionProblem"
  | Karp21.Problem.exactCover =>
      "ComplexityReduction.Combinatorics.exactCoverStructuredDecisionProblem"
  | Karp21.Problem.hittingSet =>
      "ComplexityReduction.Combinatorics.hittingSetStructuredDecisionProblem"
  | Karp21.Problem.steinerTree =>
      "ComplexityReduction.Combinatorics.Graph.steinerTreeStructuredDecisionProblem"
  | Karp21.Problem.threeDimensionalMatching =>
      "ComplexityReduction.Combinatorics.threeDimensionalMatchingStructuredDecisionProblem"
  | Karp21.Problem.knapsack =>
      "ComplexityReduction.Combinatorics.knapsackStructuredDecisionProblem"
  | Karp21.Problem.jobSequencing =>
      "ComplexityReduction.Combinatorics.jobSequencingStructuredDecisionProblem"
  | Karp21.Problem.partition =>
      "ComplexityReduction.Combinatorics.partitionStructuredDecisionProblem"
  | Karp21.Problem.maxCut =>
      "ComplexityReduction.Combinatorics.Graph.maxCutStructuredDecisionProblem"

/-- Checked faithful-encoding theorem for the structured Karp21 target. -/
def problemEncodingConformanceTheorem : Karp21.Problem → String
  | Karp21.Problem.satisfiability =>
      "ComplexityReduction.Karp21.satisfiabilityStructuredEncoding_faithful"
  | Karp21.Problem.zeroOneIntegerProgramming =>
      "ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPStructuredEncoding_faithful"
  | Karp21.Problem.clique =>
      "ComplexityReduction.Karp21.Clique.cliqueStructuredEncoding_faithful"
  | Karp21.Problem.setPacking =>
      "ComplexityReduction.Karp21.SetPacking.setPackingStructuredEncoding_faithful"
  | Karp21.Problem.vertexCover =>
      "ComplexityReduction.Karp21.VertexCover.vertexCoverStructuredEncoding_faithful"
  | Karp21.Problem.setCovering =>
      "ComplexityReduction.Karp21.SetCovering.setCoveringStructuredEncoding_faithful"
  | Karp21.Problem.feedbackNodeSet =>
      "ComplexityReduction.Karp21.FeedbackNodeSet.feedbackNodeSetStructuredEncoding_faithful"
  | Karp21.Problem.feedbackArcSet =>
      "ComplexityReduction.Karp21.FeedbackArcSet.feedbackArcSetStructuredEncoding_faithful"
  | Karp21.Problem.directedHamiltonianCircuit =>
      "ComplexityReduction.Karp21.DirectedHamiltonianCircuit.directedHamiltonianCircuitStructuredEncoding_faithful"
  | Karp21.Problem.undirectedHamiltonianCircuit =>
      "ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.undirectedHamiltonianCircuitStructuredEncoding_faithful"
  | Karp21.Problem.threeSatisfiability =>
      "ComplexityReduction.Karp21.threeSATStructuredEncoding_faithful"
  | Karp21.Problem.chromaticNumber =>
      "ComplexityReduction.Karp21.ChromaticNumber.chromaticNumberStructuredEncoding_faithful"
  | Karp21.Problem.cliqueCover =>
      "ComplexityReduction.Karp21.CliqueCover.cliqueCoverStructuredEncoding_faithful"
  | Karp21.Problem.exactCover =>
      "ComplexityReduction.Karp21.ExactCover.exactCoverStructuredEncoding_faithful"
  | Karp21.Problem.hittingSet =>
      "ComplexityReduction.Karp21.HittingSet.hittingSetStructuredEncoding_faithful"
  | Karp21.Problem.steinerTree =>
      "ComplexityReduction.Karp21.SteinerTree.steinerTreeStructuredEncoding_faithful"
  | Karp21.Problem.threeDimensionalMatching =>
      "ComplexityReduction.Karp21.ThreeDimensionalMatching.threeDimensionalMatchingStructuredEncoding_faithful"
  | Karp21.Problem.knapsack =>
      "ComplexityReduction.Karp21.Knapsack.knapsackStructuredEncoding_faithful"
  | Karp21.Problem.jobSequencing =>
      "ComplexityReduction.Karp21.JobSequencing.jobSequencingStructuredEncoding_faithful"
  | Karp21.Problem.partition =>
      "ComplexityReduction.Karp21.Partition.partitionStructuredEncoding_faithful"
  | Karp21.Problem.maxCut =>
      "ComplexityReduction.Karp21.MaxCut.maxCutStructuredEncoding_faithful"

/-- Encoded-image yes-status reflection theorem for the structured Karp21 target. -/
def problemAcceptsEncodingTheorem : Karp21.Problem → String
  | Karp21.Problem.satisfiability =>
      "ComplexityReduction.Karp21.satisfiabilityStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.zeroOneIntegerProgramming =>
      "ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.clique =>
      "ComplexityReduction.Karp21.Clique.cliqueStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.setPacking =>
      "ComplexityReduction.Karp21.SetPacking.setPackingStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.vertexCover =>
      "ComplexityReduction.Karp21.VertexCover.vertexCoverStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.setCovering =>
      "ComplexityReduction.Karp21.SetCovering.setCoveringStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.feedbackNodeSet =>
      "ComplexityReduction.Karp21.FeedbackNodeSet.feedbackNodeSetStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.feedbackArcSet =>
      "ComplexityReduction.Karp21.FeedbackArcSet.feedbackArcSetStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.directedHamiltonianCircuit =>
      "ComplexityReduction.Karp21.DirectedHamiltonianCircuit.directedHamiltonianCircuitStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.undirectedHamiltonianCircuit =>
      "ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.undirectedHamiltonianCircuitStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.threeSatisfiability =>
      "ComplexityReduction.Karp21.threeSATStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.chromaticNumber =>
      "ComplexityReduction.Karp21.ChromaticNumber.chromaticNumberStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.cliqueCover =>
      "ComplexityReduction.Karp21.CliqueCover.cliqueCoverStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.exactCover =>
      "ComplexityReduction.Karp21.ExactCover.exactCoverStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.hittingSet =>
      "ComplexityReduction.Karp21.HittingSet.hittingSetStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.steinerTree =>
      "ComplexityReduction.Karp21.SteinerTree.steinerTreeStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.threeDimensionalMatching =>
      "ComplexityReduction.Karp21.ThreeDimensionalMatching.threeDimensionalMatchingStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.knapsack =>
      "ComplexityReduction.Karp21.Knapsack.knapsackStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.jobSequencing =>
      "ComplexityReduction.Karp21.JobSequencing.jobSequencingStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.partition =>
      "ComplexityReduction.Karp21.Partition.partitionStructuredEncoding_accepts_encode_iff"
  | Karp21.Problem.maxCut =>
      "ComplexityReduction.Karp21.MaxCut.maxCutStructuredEncoding_accepts_encode_iff"

/-- Convert the reusable Karp21 descriptor to the target-catalog shape. -/
def ofProblemDescriptor (d : Karp21.ProblemDescriptor) : Karp21TargetDescriptor :=
  let base : Karp21TargetDescriptor := match d.problem with
  | Karp21.Problem.satisfiability =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol := some "ComplexityReduction.Karp21.satisfiabilityInNP"
        incomingReductionSymbol :=
          some "ComplexityReduction.Karp21.threeSATToCNFSATKarpReduction"
        completenessSymbol := some "ComplexityReduction.Karp21.satisfiabilityNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some "ComplexityReduction.Karp21.satisfiability_threeSatisfiability_problemEquiv"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P15g proved target: project-local CNF SAT equivalent to bundled local 3SAT." }
  | Karp21.Problem.zeroOneIntegerProgramming =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol := some "ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.ZeroOneIP.threeSATToZeroOneIP_textbookKarpReduction"
        completenessSymbol :=
          some "ComplexityReduction.Karp21.ZeroOneIP.zeroOneIP_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.ZeroOneIP.threeSATToZeroOneIP_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some "ComplexityReduction.Karp21.ZeroOneIP.zeroOneIPNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P15x textbook target: 3SAT clauses linearized as 0-1 IP inequalities." }
  | Karp21.Problem.clique =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol := some "ComplexityReduction.Karp21.Clique.cliqueInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.Clique.threeSATToClique_textbookKarpReduction"
        completenessSymbol := some "ComplexityReduction.Karp21.Clique.clique_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.Clique.threeSATToClique_textbookKarpReduction"
        fallbackCompletenessSymbol := some "ComplexityReduction.Karp21.Clique.cliqueNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P15s textbook target: 3SAT to Clique by clause-literal compatibility graph." }
  | Karp21.Problem.setPacking =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol :=
          some "ComplexityReduction.Karp21.SetPacking.setPackingInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.SetPacking.cliqueToSetPacking_textbookKarpReduction"
        completenessSymbol :=
          some "ComplexityReduction.Karp21.SetPacking.setPacking_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.SetPacking.cliqueToSetPacking_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some "ComplexityReduction.Karp21.SetPacking.setPackingNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P15i proved target: Clique to Set Packing by complement-edge incidence sets." }
  | Karp21.Problem.vertexCover =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol :=
          some "ComplexityReduction.Karp21.VertexCover.vertexCoverInNP"
        incomingReductionSymbol :=
          some "ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverKarpReduction"
        completenessSymbol :=
          some "ComplexityReduction.Karp21.VertexCover.vertexCoverNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some "ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverKarpReduction"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes := "P15b proved target: Clique to Vertex Cover by complement graph." }
  | Karp21.Problem.setCovering =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol :=
          some "ComplexityReduction.Karp21.SetCovering.setCoveringInNP"
        incomingReductionSymbol :=
          some "ComplexityReduction.Karp21.SetCovering.vertexCoverToSetCoveringKarpReduction"
        completenessSymbol :=
          some "ComplexityReduction.Karp21.SetCovering.setCoveringNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some "ComplexityReduction.Karp21.SetCovering.vertexCoverToSetCoveringKarpReduction"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes := "P15b proved target: Vertex Cover to Set Covering by edge incidence." }
  | Karp21.Problem.feedbackNodeSet =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol :=
          some "ComplexityReduction.Karp21.FeedbackNodeSet.feedbackNodeSetInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.FeedbackNodeSet.vertexCoverToFeedbackNodeSet_textbookKarpReduction"
        completenessSymbol :=
          some "ComplexityReduction.Karp21.FeedbackNodeSet.feedbackNodeSet_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.FeedbackNodeSet.vertexCoverToFeedbackNodeSet_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some "ComplexityReduction.Karp21.FeedbackNodeSet.feedbackNodeSetNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes := "P15t textbook target: Vertex Cover to Feedback Node Set by bidirected-edge cycles." }
  | Karp21.Problem.feedbackArcSet =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol :=
          some "ComplexityReduction.Karp21.FeedbackArcSet.feedbackArcSetInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.FeedbackArcSet.feedbackNodeSetToFeedbackArcSet_textbookKarpReduction"
        completenessSymbol :=
          some "ComplexityReduction.Karp21.FeedbackArcSet.feedbackArcSet_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.FeedbackArcSet.feedbackNodeSetToFeedbackArcSet_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some "ComplexityReduction.Karp21.FeedbackArcSet.feedbackArcSetNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes := "P15u textbook target: Feedback Node Set to Feedback Arc Set by node splitting." }
  | Karp21.Problem.directedHamiltonianCircuit =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol :=
          some
            "ComplexityReduction.Karp21.DirectedHamiltonianCircuit.directedHamiltonianCircuitInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.DirectedHamiltonianCircuit.vertexCoverToDirectedHamiltonianCircuit_textbookKarpReduction"
        completenessSymbol :=
          some
            "ComplexityReduction.Karp21.DirectedHamiltonianCircuit.directedHamiltonianCircuit_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.DirectedHamiltonianCircuit.vertexCoverToDirectedHamiltonianCircuit_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some
            "ComplexityReduction.Karp21.DirectedHamiltonianCircuit.directedHamiltonianCircuitNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P15v textbook target: Vertex Cover to Directed Hamiltonian Circuit by selector/path gadget." }
  | Karp21.Problem.undirectedHamiltonianCircuit =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol :=
          some
            "ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.undirectedHamiltonianCircuitInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.directedToUndirectedHamiltonianCircuit_textbookKarpReduction"
        completenessSymbol :=
          some
            "ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.undirectedHamiltonianCircuit_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.directedToUndirectedHamiltonianCircuit_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some
            "ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.undirectedHamiltonianCircuitNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P15w textbook target: Directed Hamiltonian Circuit to Undirected Hamiltonian Circuit by in/mid/out replacement." }
  | Karp21.Problem.threeSatisfiability =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol := some "ComplexityReduction.SAT.threeSAT_inNP"
        incomingReductionSymbol := none
        completenessSymbol := some "ComplexityReduction.SAT.localCookLevinTheorem"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P14e proved source target: local 3-Satisfiability complete via Cook-Levin." }
  | Karp21.Problem.chromaticNumber =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol :=
          some "ComplexityReduction.Karp21.ChromaticNumber.chromaticNumberInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.ChromaticNumber.threeSATToChromaticNumber_textbookKarpReduction"
        completenessSymbol :=
          some "ComplexityReduction.Karp21.ChromaticNumber.chromaticNumber_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.ChromaticNumber.threeSATToChromaticNumber_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some "ComplexityReduction.Karp21.ChromaticNumber.chromaticNumberNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes := "P15q textbook target: 3SAT to Chromatic Number via coloring gadgets." }
  | Karp21.Problem.cliqueCover =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol :=
          some "ComplexityReduction.Karp21.CliqueCover.cliqueCoverInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.CliqueCover.chromaticNumberToCliqueCover_textbookKarpReduction"
        completenessSymbol :=
          some "ComplexityReduction.Karp21.CliqueCover.cliqueCover_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.CliqueCover.chromaticNumberToCliqueCover_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some "ComplexityReduction.Karp21.CliqueCover.cliqueCoverNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P15r proved target: Chromatic Number to Clique Cover by complement graph." }
  | Karp21.Problem.exactCover =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol :=
          some "ComplexityReduction.Karp21.ExactCover.exactCoverInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.ExactCover.setCoveringToExactCover_textbookKarpReduction"
        completenessSymbol :=
          some "ComplexityReduction.Karp21.ExactCover.exactCover_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.ExactCover.setCoveringToExactCover_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some "ComplexityReduction.Karp21.ExactCover.exactCoverNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P15j proved target: Set Covering to Exact Cover by slack/dummy slot blocks." }
  | Karp21.Problem.hittingSet =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol :=
          some "ComplexityReduction.Karp21.HittingSet.hittingSetInNP"
        incomingReductionSymbol :=
          some "ComplexityReduction.Karp21.HittingSet.setCoveringToHittingSetKarpReduction"
        completenessSymbol :=
          some "ComplexityReduction.Karp21.HittingSet.hittingSetNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some "ComplexityReduction.Karp21.HittingSet.setCoveringToHittingSetKarpReduction"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes := "P15b proved target: Set Covering to Hitting Set by dual set system." }
  | Karp21.Problem.steinerTree =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol :=
          some "ComplexityReduction.Karp21.SteinerTree.steinerTreeInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTree_textbookKarpReduction"
        completenessSymbol :=
          some "ComplexityReduction.Karp21.SteinerTree.steinerTree_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTree_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some "ComplexityReduction.Karp21.SteinerTree.steinerTreeNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P15l proved target: Exact Cover to Steiner Tree by weighted connectivity." }
  | Karp21.Problem.threeDimensionalMatching =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol :=
          some "ComplexityReduction.Karp21.ThreeDimensionalMatching.threeDimensionalMatchingInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.ThreeDimensionalMatching.exactCoverToThreeDimensionalMatching_textbookKarpReduction"
        completenessSymbol :=
          some
            "ComplexityReduction.Karp21.ThreeDimensionalMatching.threeDimensionalMatching_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.ThreeDimensionalMatching.exactCoverToThreeDimensionalMatching_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some
            "ComplexityReduction.Karp21.ThreeDimensionalMatching.threeDimensionalMatchingNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P15k proved target: Exact Cover to 3DM by explicit X/Y/Z witness triples." }
  | Karp21.Problem.knapsack =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol := some "ComplexityReduction.Karp21.Knapsack.knapsackInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.Knapsack.zeroOneIPToKnapsack_textbookKarpReduction"
        completenessSymbol :=
          some "ComplexityReduction.Karp21.Knapsack.knapsack_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.Knapsack.zeroOneIPToKnapsack_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some "ComplexityReduction.Karp21.Knapsack.knapsackNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P15m proved target: 0-1 IP to Knapsack by candidate violation digits." }
  | Karp21.Problem.jobSequencing =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol :=
          some "ComplexityReduction.Karp21.JobSequencing.jobSequencingInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencing_textbookKarpReduction"
        completenessSymbol :=
          some "ComplexityReduction.Karp21.JobSequencing.jobSequencing_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencing_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some "ComplexityReduction.Karp21.JobSequencing.jobSequencingNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P15p proved target: Knapsack to Job Sequencing by one job per item." }
  | Karp21.Problem.partition =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol := some "ComplexityReduction.Karp21.Partition.partitionInNP"
        incomingReductionSymbol :=
          some
            "ComplexityReduction.Karp21.Partition.knapsackToPartition_textbookKarpReduction"
        completenessSymbol :=
          some "ComplexityReduction.Karp21.Partition.partition_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some
            "ComplexityReduction.Karp21.Partition.knapsackToPartition_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some "ComplexityReduction.Karp21.Partition.partitionNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P15n proved target: Knapsack to Partition by exact-sum balancing." }
  | Karp21.Problem.maxCut =>
      { problem := d.problem
        name := d.paperName
        tag := d.tag
        problemSymbol := d.encodedProblemSymbol
        membershipSymbol := some "ComplexityReduction.Karp21.MaxCut.maxCutInNP"
        incomingReductionSymbol :=
          some "ComplexityReduction.Karp21.MaxCut.partitionToMaxCut_textbookKarpReduction"
        completenessSymbol := some "ComplexityReduction.Karp21.MaxCut.maxCut_textbookNPComplete"
        routeStyle := "textbook_gadget"
        textbookGadgetTheorem :=
          some "ComplexityReduction.Karp21.MaxCut.partitionToMaxCut_textbookKarpReduction"
        fallbackCompletenessSymbol :=
          some "ComplexityReduction.Karp21.MaxCut.maxCutNPComplete"
        sourceBoundary := "local_discharged: SAT.localCookLevinTheorem"
        reference := d.reference
        artifactEligibleByDefault := true
        notes :=
          "P15o proved target: Partition to Max Cut by scaled complete-graph cuts." }
  { base with
    structuredProblemSymbol := some (problemStructuredProblemSymbol d.problem)
    encodingConformanceTheorem := some (problemEncodingConformanceTheorem d.problem)
    acceptsEncodingTheorem := some (problemAcceptsEncodingTheorem d.problem) }

end Karp21TargetDescriptor

/-- Karp 21 target inventory visible to audit/generation tooling. -/
def karp21Targets : List Karp21TargetDescriptor :=
  Karp21.problemDescriptors.map Karp21TargetDescriptor.ofProblemDescriptor

theorem karp21Targets_length :
    karp21Targets.length = 21 := by
  simp [karp21Targets, Karp21.problemDescriptors_length]

/-- Karp 21 tags in catalog order. -/
def karp21TargetTags : List String :=
  karp21Targets.map Karp21TargetDescriptor.tag

theorem karp21TargetTags_length :
    karp21TargetTags.length = 21 := by
  simp [karp21TargetTags, karp21Targets_length]

/-- P15b targets whose catalog entries expose verified theorem symbols. -/
def karp21P15bTargets : List Karp21TargetDescriptor :=
  [ Karp21TargetDescriptor.ofProblemDescriptor Karp21.cliqueDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.vertexCoverDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.setCoveringDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.hittingSetDescriptor
  ]

theorem karp21P15bTargets_length :
    karp21P15bTargets.length = 4 :=
  rfl

/-- P15c arithmetic targets whose catalog entries expose verified theorem symbols. -/
def karp21P15cTargets : List Karp21TargetDescriptor :=
  [ Karp21TargetDescriptor.ofProblemDescriptor Karp21.zeroOneIntegerProgrammingDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.knapsackDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.partitionDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.maxCutDescriptor
  ]

theorem karp21P15cTargets_length :
    karp21P15cTargets.length = 4 :=
  rfl

/-- P15d graph targets whose catalog entries expose verified theorem symbols. -/
def karp21P15dTargets : List Karp21TargetDescriptor :=
  [ Karp21TargetDescriptor.ofProblemDescriptor Karp21.feedbackNodeSetDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.feedbackArcSetDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.directedHamiltonianCircuitDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.undirectedHamiltonianCircuitDescriptor
  ]

theorem karp21P15dTargets_length :
    karp21P15dTargets.length = 4 :=
  rfl

/-- P15e residual targets whose catalog entries expose verified theorem symbols. -/
def karp21P15eTargets : List Karp21TargetDescriptor :=
  [ Karp21TargetDescriptor.ofProblemDescriptor Karp21.setPackingDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.exactCoverDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.threeDimensionalMatchingDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.jobSequencingDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.steinerTreeDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.chromaticNumberDescriptor
  , Karp21TargetDescriptor.ofProblemDescriptor Karp21.cliqueCoverDescriptor
  ]

theorem karp21P15eTargets_length :
    karp21P15eTargets.length = 7 :=
  rfl

end Targets
end ComplexityReduction
