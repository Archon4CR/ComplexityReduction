/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.PackagedCompleteness
import ComplexityReduction.Karp21.PackagedMembership
import ComplexityReduction.Karp21.ExactEncodedSuffixDecodersTM
import ComplexityReduction.Karp21.PullbackFiniteBoolSuffixDecodersTM
import ComplexityReduction.Karp21.SatisfiabilitySuffixDecoderTM

/-!
Catalog-level packaged standard-TM NP-completeness facts for the currently
verified faithful Karp21 structured edges.

This file deliberately records the remaining source and encoding bridge
obligations as explicit data.  In particular, the current direct edge inventory
still keeps the unary structured Knapsack source separate from the
binary-structured 0-1-IP-to-binary-Knapsack route.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/--
Packaged source facts not yet connected to the main structured-3SAT root by the
current direct-TM edge inventory.
-/
structure Karp21PackagedExternalSources : Prop where
  knapsackStructured : PackagedTMNPComplete knapsackStructuredDecisionProblem

/--
Concrete Karp21 membership facts whose current verifier carries a checked suffix
decoder.  This catalog does not claim a conversion from arbitrary ordinary
`TMInNP` membership.
-/
structure Karp21CheckedSuffixDecoderCatalog : Prop where
  threeSatisfiability :
    SAT.TMInNPWithCheckedSuffixDecoder threeSATStructuredDecisionProblem
  satisfiability :
    SAT.TMInNPWithCheckedSuffixDecoder satisfiabilityStructuredDecisionProblem
  zeroOneIP :
    SAT.TMInNPWithCheckedSuffixDecoder zeroOneIntegerProgrammingStructuredDecisionProblem
  zeroOneIPBinary :
    SAT.TMInNPWithCheckedSuffixDecoder
      zeroOneIntegerProgrammingBinaryStructuredDecisionProblem
  clique : SAT.TMInNPWithCheckedSuffixDecoder cliqueStructuredDecisionProblem
  chromaticNumber :
    SAT.TMInNPWithCheckedSuffixDecoder chromaticNumberStructuredDecisionProblem
  cliqueCover :
    SAT.TMInNPWithCheckedSuffixDecoder cliqueCoverStructuredDecisionProblem
  setPacking :
    SAT.TMInNPWithCheckedSuffixDecoder setPackingStructuredDecisionProblem
  vertexCover :
    SAT.TMInNPWithCheckedSuffixDecoder vertexCoverStructuredDecisionProblem
  setCovering :
    SAT.TMInNPWithCheckedSuffixDecoder setCoveringStructuredDecisionProblem
  feedbackNodeSet :
    SAT.TMInNPWithCheckedSuffixDecoder feedbackNodeSetStructuredDecisionProblem
  feedbackArcSet :
    SAT.TMInNPWithCheckedSuffixDecoder feedbackArcSetStructuredDecisionProblem
  exactCover :
    SAT.TMInNPWithCheckedSuffixDecoder exactCoverStructuredDecisionProblem
  hittingSet :
    SAT.TMInNPWithCheckedSuffixDecoder hittingSetStructuredDecisionProblem
  steinerTree :
    SAT.TMInNPWithCheckedSuffixDecoder steinerTreeStructuredDecisionProblem
  threeDimensionalMatching :
    SAT.TMInNPWithCheckedSuffixDecoder threeDimensionalMatchingStructuredDecisionProblem
  directedHamiltonianCircuit :
    SAT.TMInNPWithCheckedSuffixDecoder directedHamiltonianCircuitStructuredDecisionProblem
  undirectedHamiltonianCircuit :
    SAT.TMInNPWithCheckedSuffixDecoder undirectedHamiltonianCircuitStructuredDecisionProblem
  partition :
    SAT.TMInNPWithCheckedSuffixDecoder partitionStructuredDecisionProblem
  partitionBinary :
    SAT.TMInNPWithCheckedSuffixDecoder partitionBinaryStructuredDecisionProblem
  knapsackStructured :
    SAT.TMInNPWithCheckedSuffixDecoder knapsackStructuredDecisionProblem
  knapsackBinary :
    SAT.TMInNPWithCheckedSuffixDecoder knapsackBinaryStructuredDecisionProblem
  jobSequencing :
    SAT.TMInNPWithCheckedSuffixDecoder jobSequencingStructuredDecisionProblem
  jobSequencingBinary :
    SAT.TMInNPWithCheckedSuffixDecoder jobSequencingBinaryStructuredDecisionProblem
  maxCut : SAT.TMInNPWithCheckedSuffixDecoder maxCutStructuredDecisionProblem
  maxCutBinary :
    SAT.TMInNPWithCheckedSuffixDecoder maxCutBinaryStructuredDecisionProblem

/--
Assemble the checked-suffix-decoder membership catalog from the concrete
verified verifier packages currently available for Karp21 targets.
-/
theorem karp21CheckedSuffixDecoderCatalog :
    Karp21CheckedSuffixDecoderCatalog := by
  exact
    { threeSatisfiability := SAT.threeSATStructured_TMInNPWithCheckedSuffixDecoder
      satisfiability := satisfiabilityStructured_TMInNPWithCheckedSuffixDecoder
      zeroOneIP := zeroOneIPStructured_TMInNPWithCheckedSuffixDecoder
      zeroOneIPBinary := zeroOneIPBinaryStructured_TMInNPWithCheckedSuffixDecoder
      clique := cliqueStructured_TMInNPWithCheckedSuffixDecoder
      chromaticNumber := chromaticNumberStructured_TMInNPWithCheckedSuffixDecoder
      cliqueCover := cliqueCoverStructured_TMInNPWithCheckedSuffixDecoder
      setPacking := setPackingStructured_TMInNPWithCheckedSuffixDecoder
      vertexCover := vertexCoverStructured_TMInNPWithCheckedSuffixDecoder
      setCovering := setCoveringStructured_TMInNPWithCheckedSuffixDecoder
      feedbackNodeSet := feedbackNodeSetStructured_TMInNPWithCheckedSuffixDecoder
      feedbackArcSet := feedbackArcSetStructured_TMInNPWithCheckedSuffixDecoder
      exactCover := exactCoverStructured_TMInNPWithCheckedSuffixDecoder
      hittingSet := hittingSetStructured_TMInNPWithCheckedSuffixDecoder
      steinerTree := steinerTreeStructured_TMInNPWithCheckedSuffixDecoder
      threeDimensionalMatching :=
        threeDimensionalMatchingStructured_TMInNPWithCheckedSuffixDecoder
      directedHamiltonianCircuit :=
        directedHamiltonianCircuitStructured_TMInNPWithCheckedSuffixDecoder
      undirectedHamiltonianCircuit :=
        undirectedHamiltonianCircuitStructured_TMInNPWithCheckedSuffixDecoder
      partition := partitionStructured_TMInNPWithCheckedSuffixDecoder
      partitionBinary := partitionBinaryStructured_TMInNPWithCheckedSuffixDecoder
      knapsackStructured := knapsackStructured_TMInNPWithCheckedSuffixDecoder
      knapsackBinary := knapsackBinaryStructured_TMInNPWithCheckedSuffixDecoder
      jobSequencing := jobSequencingStructured_TMInNPWithCheckedSuffixDecoder
      jobSequencingBinary := jobSequencingBinaryStructured_TMInNPWithCheckedSuffixDecoder
      maxCut := maxCutStructured_TMInNPWithCheckedSuffixDecoder
      maxCutBinary := maxCutBinaryStructured_TMInNPWithCheckedSuffixDecoder }

/-! ### Encoding-discipline membership packages -/

theorem satisfiabilityStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline satisfiabilityStructuredDecisionProblem :=
  satisfiabilityStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem zeroOneIPStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline zeroOneIntegerProgrammingStructuredDecisionProblem :=
  zeroOneIPStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem zeroOneIPBinaryStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline
      zeroOneIntegerProgrammingBinaryStructuredDecisionProblem :=
  zeroOneIPBinaryStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem cliqueStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline cliqueStructuredDecisionProblem :=
  cliqueStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem chromaticNumberStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline chromaticNumberStructuredDecisionProblem :=
  chromaticNumberStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem cliqueCoverStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline cliqueCoverStructuredDecisionProblem :=
  cliqueCoverStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem setPackingStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline setPackingStructuredDecisionProblem :=
  setPackingStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem vertexCoverStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline vertexCoverStructuredDecisionProblem :=
  vertexCoverStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem setCoveringStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline setCoveringStructuredDecisionProblem :=
  setCoveringStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem feedbackNodeSetStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline feedbackNodeSetStructuredDecisionProblem :=
  feedbackNodeSetStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem feedbackArcSetStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline feedbackArcSetStructuredDecisionProblem :=
  feedbackArcSetStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem exactCoverStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline exactCoverStructuredDecisionProblem :=
  exactCoverStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem hittingSetStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline hittingSetStructuredDecisionProblem :=
  hittingSetStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem steinerTreeStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline steinerTreeStructuredDecisionProblem :=
  steinerTreeStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem threeDimensionalMatchingStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline threeDimensionalMatchingStructuredDecisionProblem :=
  threeDimensionalMatchingStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem directedHamiltonianCircuitStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline directedHamiltonianCircuitStructuredDecisionProblem :=
  directedHamiltonianCircuitStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem undirectedHamiltonianCircuitStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline undirectedHamiltonianCircuitStructuredDecisionProblem :=
  undirectedHamiltonianCircuitStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem partitionStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline partitionStructuredDecisionProblem :=
  partitionStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem partitionBinaryStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline partitionBinaryStructuredDecisionProblem :=
  partitionBinaryStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem knapsackStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline knapsackStructuredDecisionProblem :=
  knapsackStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem knapsackBinaryStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline knapsackBinaryStructuredDecisionProblem :=
  knapsackBinaryStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem jobSequencingStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline jobSequencingStructuredDecisionProblem :=
  jobSequencingStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem jobSequencingBinaryStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline jobSequencingBinaryStructuredDecisionProblem :=
  jobSequencingBinaryStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem maxCutStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline maxCutStructuredDecisionProblem :=
  maxCutStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

theorem maxCutBinaryStructured_TMInNPWithEncodingDiscipline :
    SAT.TMInNPWithEncodingDiscipline maxCutBinaryStructuredDecisionProblem :=
  maxCutBinaryStructured_TMInNPWithCheckedSuffixDecoder.toEncodingDiscipline

/-- Concrete Karp21 membership facts carrying standard-TM encoding discipline. -/
structure Karp21EncodingDisciplineCatalog : Prop where
  threeSatisfiability :
    SAT.TMInNPWithEncodingDiscipline threeSATStructuredDecisionProblem
  satisfiability :
    SAT.TMInNPWithEncodingDiscipline satisfiabilityStructuredDecisionProblem
  zeroOneIP :
    SAT.TMInNPWithEncodingDiscipline zeroOneIntegerProgrammingStructuredDecisionProblem
  zeroOneIPBinary :
    SAT.TMInNPWithEncodingDiscipline
      zeroOneIntegerProgrammingBinaryStructuredDecisionProblem
  clique : SAT.TMInNPWithEncodingDiscipline cliqueStructuredDecisionProblem
  chromaticNumber :
    SAT.TMInNPWithEncodingDiscipline chromaticNumberStructuredDecisionProblem
  cliqueCover :
    SAT.TMInNPWithEncodingDiscipline cliqueCoverStructuredDecisionProblem
  setPacking :
    SAT.TMInNPWithEncodingDiscipline setPackingStructuredDecisionProblem
  vertexCover :
    SAT.TMInNPWithEncodingDiscipline vertexCoverStructuredDecisionProblem
  setCovering :
    SAT.TMInNPWithEncodingDiscipline setCoveringStructuredDecisionProblem
  feedbackNodeSet :
    SAT.TMInNPWithEncodingDiscipline feedbackNodeSetStructuredDecisionProblem
  feedbackArcSet :
    SAT.TMInNPWithEncodingDiscipline feedbackArcSetStructuredDecisionProblem
  exactCover :
    SAT.TMInNPWithEncodingDiscipline exactCoverStructuredDecisionProblem
  hittingSet :
    SAT.TMInNPWithEncodingDiscipline hittingSetStructuredDecisionProblem
  steinerTree :
    SAT.TMInNPWithEncodingDiscipline steinerTreeStructuredDecisionProblem
  threeDimensionalMatching :
    SAT.TMInNPWithEncodingDiscipline threeDimensionalMatchingStructuredDecisionProblem
  directedHamiltonianCircuit :
    SAT.TMInNPWithEncodingDiscipline directedHamiltonianCircuitStructuredDecisionProblem
  undirectedHamiltonianCircuit :
    SAT.TMInNPWithEncodingDiscipline undirectedHamiltonianCircuitStructuredDecisionProblem
  partition :
    SAT.TMInNPWithEncodingDiscipline partitionStructuredDecisionProblem
  partitionBinary :
    SAT.TMInNPWithEncodingDiscipline partitionBinaryStructuredDecisionProblem
  knapsackStructured :
    SAT.TMInNPWithEncodingDiscipline knapsackStructuredDecisionProblem
  knapsackBinary :
    SAT.TMInNPWithEncodingDiscipline knapsackBinaryStructuredDecisionProblem
  jobSequencing :
    SAT.TMInNPWithEncodingDiscipline jobSequencingStructuredDecisionProblem
  jobSequencingBinary :
    SAT.TMInNPWithEncodingDiscipline jobSequencingBinaryStructuredDecisionProblem
  maxCut : SAT.TMInNPWithEncodingDiscipline maxCutStructuredDecisionProblem
  maxCutBinary :
    SAT.TMInNPWithEncodingDiscipline maxCutBinaryStructuredDecisionProblem

/-- Assemble the encoding-discipline membership catalog from checked decoders. -/
theorem karp21EncodingDisciplineCatalog :
    Karp21EncodingDisciplineCatalog := by
  exact
    { threeSatisfiability := SAT.threeSATStructured_TMInNPWithEncodingDiscipline
      satisfiability := satisfiabilityStructured_TMInNPWithEncodingDiscipline
      zeroOneIP := zeroOneIPStructured_TMInNPWithEncodingDiscipline
      zeroOneIPBinary := zeroOneIPBinaryStructured_TMInNPWithEncodingDiscipline
      clique := cliqueStructured_TMInNPWithEncodingDiscipline
      chromaticNumber := chromaticNumberStructured_TMInNPWithEncodingDiscipline
      cliqueCover := cliqueCoverStructured_TMInNPWithEncodingDiscipline
      setPacking := setPackingStructured_TMInNPWithEncodingDiscipline
      vertexCover := vertexCoverStructured_TMInNPWithEncodingDiscipline
      setCovering := setCoveringStructured_TMInNPWithEncodingDiscipline
      feedbackNodeSet := feedbackNodeSetStructured_TMInNPWithEncodingDiscipline
      feedbackArcSet := feedbackArcSetStructured_TMInNPWithEncodingDiscipline
      exactCover := exactCoverStructured_TMInNPWithEncodingDiscipline
      hittingSet := hittingSetStructured_TMInNPWithEncodingDiscipline
      steinerTree := steinerTreeStructured_TMInNPWithEncodingDiscipline
      threeDimensionalMatching :=
        threeDimensionalMatchingStructured_TMInNPWithEncodingDiscipline
      directedHamiltonianCircuit :=
        directedHamiltonianCircuitStructured_TMInNPWithEncodingDiscipline
      undirectedHamiltonianCircuit :=
        undirectedHamiltonianCircuitStructured_TMInNPWithEncodingDiscipline
      partition := partitionStructured_TMInNPWithEncodingDiscipline
      partitionBinary := partitionBinaryStructured_TMInNPWithEncodingDiscipline
      knapsackStructured := knapsackStructured_TMInNPWithEncodingDiscipline
      knapsackBinary := knapsackBinaryStructured_TMInNPWithEncodingDiscipline
      jobSequencing := jobSequencingStructured_TMInNPWithEncodingDiscipline
      jobSequencingBinary := jobSequencingBinaryStructured_TMInNPWithEncodingDiscipline
      maxCut := maxCutStructured_TMInNPWithEncodingDiscipline
      maxCutBinary := maxCutBinaryStructured_TMInNPWithEncodingDiscipline }

/--
Checked-suffix-decoder membership obligations still missing from the concrete
catalog.  The current faithful Karp21 target set is closed; the `True` field
keeps the historical audit hook as an explicit empty obligation record.
-/
structure Karp21CheckedSuffixDecoderRemainingObligations : Prop where
  closed : True

/--
Full Karp21 checked-suffix-decoder membership catalog for the currently
formalized faithful structured target set.
-/
structure Karp21FullCheckedSuffixDecoderCatalog : Prop where
  threeSatisfiability :
    SAT.TMInNPWithCheckedSuffixDecoder threeSATStructuredDecisionProblem
  satisfiability :
    SAT.TMInNPWithCheckedSuffixDecoder satisfiabilityStructuredDecisionProblem
  zeroOneIP :
    SAT.TMInNPWithCheckedSuffixDecoder zeroOneIntegerProgrammingStructuredDecisionProblem
  zeroOneIPBinary :
    SAT.TMInNPWithCheckedSuffixDecoder
      zeroOneIntegerProgrammingBinaryStructuredDecisionProblem
  clique : SAT.TMInNPWithCheckedSuffixDecoder cliqueStructuredDecisionProblem
  chromaticNumber :
    SAT.TMInNPWithCheckedSuffixDecoder chromaticNumberStructuredDecisionProblem
  setPacking :
    SAT.TMInNPWithCheckedSuffixDecoder setPackingStructuredDecisionProblem
  vertexCover :
    SAT.TMInNPWithCheckedSuffixDecoder vertexCoverStructuredDecisionProblem
  setCovering :
    SAT.TMInNPWithCheckedSuffixDecoder setCoveringStructuredDecisionProblem
  feedbackNodeSet :
    SAT.TMInNPWithCheckedSuffixDecoder feedbackNodeSetStructuredDecisionProblem
  feedbackArcSet :
    SAT.TMInNPWithCheckedSuffixDecoder feedbackArcSetStructuredDecisionProblem
  directedHamiltonianCircuit :
    SAT.TMInNPWithCheckedSuffixDecoder directedHamiltonianCircuitStructuredDecisionProblem
  undirectedHamiltonianCircuit :
    SAT.TMInNPWithCheckedSuffixDecoder undirectedHamiltonianCircuitStructuredDecisionProblem
  cliqueCover :
    SAT.TMInNPWithCheckedSuffixDecoder cliqueCoverStructuredDecisionProblem
  exactCover :
    SAT.TMInNPWithCheckedSuffixDecoder exactCoverStructuredDecisionProblem
  hittingSet :
    SAT.TMInNPWithCheckedSuffixDecoder hittingSetStructuredDecisionProblem
  steinerTree :
    SAT.TMInNPWithCheckedSuffixDecoder steinerTreeStructuredDecisionProblem
  threeDimensionalMatching :
    SAT.TMInNPWithCheckedSuffixDecoder threeDimensionalMatchingStructuredDecisionProblem
  knapsackStructured :
    SAT.TMInNPWithCheckedSuffixDecoder knapsackStructuredDecisionProblem
  knapsackBinary :
    SAT.TMInNPWithCheckedSuffixDecoder knapsackBinaryStructuredDecisionProblem
  jobSequencing :
    SAT.TMInNPWithCheckedSuffixDecoder jobSequencingStructuredDecisionProblem
  jobSequencingBinary :
    SAT.TMInNPWithCheckedSuffixDecoder jobSequencingBinaryStructuredDecisionProblem
  partition :
    SAT.TMInNPWithCheckedSuffixDecoder partitionStructuredDecisionProblem
  partitionBinary :
    SAT.TMInNPWithCheckedSuffixDecoder partitionBinaryStructuredDecisionProblem
  maxCut : SAT.TMInNPWithCheckedSuffixDecoder maxCutStructuredDecisionProblem
  maxCutBinary :
    SAT.TMInNPWithCheckedSuffixDecoder maxCutBinaryStructuredDecisionProblem

/--
Assemble the full checked-suffix-decoder catalog.  The remaining-obligation
argument is retained as an empty audit hook for generated reference checks.
-/
theorem karp21FullCheckedSuffixDecoderCatalog
    (_remaining : Karp21CheckedSuffixDecoderRemainingObligations) :
    Karp21FullCheckedSuffixDecoderCatalog := by
  let concrete := karp21CheckedSuffixDecoderCatalog
  exact
    { threeSatisfiability := concrete.threeSatisfiability
      satisfiability := concrete.satisfiability
      zeroOneIP := concrete.zeroOneIP
      zeroOneIPBinary := concrete.zeroOneIPBinary
      clique := concrete.clique
      chromaticNumber := concrete.chromaticNumber
      setPacking := concrete.setPacking
      vertexCover := concrete.vertexCover
      setCovering := concrete.setCovering
      feedbackNodeSet := concrete.feedbackNodeSet
      feedbackArcSet := concrete.feedbackArcSet
      directedHamiltonianCircuit := concrete.directedHamiltonianCircuit
      undirectedHamiltonianCircuit := concrete.undirectedHamiltonianCircuit
      cliqueCover := concrete.cliqueCover
      exactCover := concrete.exactCover
      hittingSet := concrete.hittingSet
      steinerTree := concrete.steinerTree
      threeDimensionalMatching := concrete.threeDimensionalMatching
      knapsackStructured := concrete.knapsackStructured
      knapsackBinary := concrete.knapsackBinary
      jobSequencing := concrete.jobSequencing
      jobSequencingBinary := concrete.jobSequencingBinary
      partition := concrete.partition
      partitionBinary := concrete.partitionBinary
      maxCut := concrete.maxCut
      maxCutBinary := concrete.maxCutBinary }

/--
Catalog of packaged standard-TM NP-completeness facts produced by the current
verified Karp21 faithful structured edges.
-/
structure Karp21PackagedTMNPCompleteCatalog : Prop where
  threeSatisfiability : PackagedTMNPComplete threeSATStructuredDecisionProblem
  satisfiability : PackagedTMNPComplete satisfiabilityStructuredDecisionProblem
  zeroOneIP : PackagedTMNPComplete zeroOneIntegerProgrammingStructuredDecisionProblem
  clique : PackagedTMNPComplete cliqueStructuredDecisionProblem
  chromaticNumber : PackagedTMNPComplete chromaticNumberStructuredDecisionProblem
  setPacking : PackagedTMNPComplete setPackingStructuredDecisionProblem
  vertexCover : PackagedTMNPComplete vertexCoverStructuredDecisionProblem
  setCovering : PackagedTMNPComplete setCoveringStructuredDecisionProblem
  feedbackNodeSet : PackagedTMNPComplete feedbackNodeSetStructuredDecisionProblem
  feedbackArcSet : PackagedTMNPComplete feedbackArcSetStructuredDecisionProblem
  directedHamiltonianCircuit :
    PackagedTMNPComplete directedHamiltonianCircuitStructuredDecisionProblem
  undirectedHamiltonianCircuit :
    PackagedTMNPComplete undirectedHamiltonianCircuitStructuredDecisionProblem
  cliqueCover : PackagedTMNPComplete cliqueCoverStructuredDecisionProblem
  exactCover : PackagedTMNPComplete exactCoverStructuredDecisionProblem
  hittingSet : PackagedTMNPComplete hittingSetStructuredDecisionProblem
  steinerTree : PackagedTMNPComplete steinerTreeStructuredDecisionProblem
  threeDimensionalMatching :
    PackagedTMNPComplete threeDimensionalMatchingStructuredDecisionProblem
  zeroOneIPBinary :
    PackagedTMNPComplete zeroOneIntegerProgrammingBinaryStructuredDecisionProblem
  knapsackBinary : PackagedTMNPComplete knapsackBinaryStructuredDecisionProblem
  jobSequencingBinary : PackagedTMNPComplete jobSequencingBinaryStructuredDecisionProblem
  partitionBinary : PackagedTMNPComplete partitionBinaryStructuredDecisionProblem
  knapsackStructured : PackagedTMNPComplete knapsackStructuredDecisionProblem
  jobSequencing : PackagedTMNPComplete jobSequencingStructuredDecisionProblem
  partition : PackagedTMNPComplete partitionStructuredDecisionProblem
  maxCut : PackagedTMNPComplete maxCutStructuredDecisionProblem
  maxCutBinary : PackagedTMNPComplete maxCutBinaryStructuredDecisionProblem

/--
Assemble the currently verified Karp21 packaged catalog from the structured
3SAT packaged root, direct-TM memberships, and the current external packaged
source.
-/
theorem karp21PackagedTMNPCompleteCatalog
    (sources : Karp21PackagedExternalSources) :
    Karp21PackagedTMNPCompleteCatalog := by
  let hThreeSAT := threeSATStructuredPackagedTMNPComplete
  let hSatisfiability :=
    satisfiabilityStructuredPackagedTMNPComplete satisfiabilityStructured_TMInNP
  let hZeroOneIP :=
    zeroOneIPStructuredPackagedTMNPComplete zeroOneIPStructured_TMInNP
  let hClique :=
    cliqueStructuredPackagedTMNPComplete cliqueStructured_TMInNP
  let hChromatic :=
    chromaticNumberStructuredPackagedTMNPComplete chromaticNumberStructured_TMInNP
  let hSetPacking :=
    setPackingStructuredPackagedTMNPCompleteOfClique hClique setPackingStructured_TMInNP
  let hVertexCover :=
    vertexCoverStructuredPackagedTMNPCompleteOfClique hClique vertexCoverStructured_TMInNP
  let hSetCovering :=
    setCoveringStructuredPackagedTMNPCompleteOfVertexCover
      hVertexCover setCoveringStructured_TMInNP
  let hFeedbackNode :=
    feedbackNodeSetStructuredPackagedTMNPCompleteOfVertexCover
      hVertexCover feedbackNodeSetStructured_TMInNP
  let hFeedbackArc :=
    feedbackArcSetStructuredPackagedTMNPCompleteOfFeedbackNodeSet
      hFeedbackNode feedbackArcSetStructured_TMInNP
  let hDirected :=
    directedHamiltonianCircuitStructuredPackagedTMNPCompleteOfVertexCover
      hVertexCover directedHamiltonianCircuitStructured_TMInNP
  let hUndirected :=
    undirectedHamiltonianCircuitStructuredPackagedTMNPCompleteOfDirected
      hDirected undirectedHamiltonianCircuitStructured_TMInNP
  let hCliqueCover :=
    cliqueCoverStructuredPackagedTMNPCompleteOfChromaticNumber
      hChromatic cliqueCoverStructured_TMInNP
  let hExactCover :=
    exactCoverStructuredPackagedTMNPCompleteOfSetCovering
      hSetCovering exactCoverStructured_TMInNP
  let hHittingSet :=
    hittingSetStructuredPackagedTMNPCompleteOfSetCovering
      hSetCovering hittingSetStructured_TMInNP
  let hSteinerTree :=
    steinerTreeStructuredPackagedTMNPCompleteOfExactCover
      hExactCover SteinerTreeMembership.steinerTreeStructured_TMInNP
  let hThreeDM :=
    threeDimensionalMatchingStructuredPackagedTMNPCompleteOfExactCover
      hExactCover threeDimensionalMatchingStructured_TMInNP
  let hZeroOneIPBinary :=
    zeroOneIPBinaryStructuredPackagedTMNPCompleteOfStructured
      hZeroOneIP zeroOneIPBinaryStructured_TMInNP
  let hKnapsackBinary :=
    knapsackBinaryStructuredPackagedTMNPCompleteOfZeroOneIPBinary
      hZeroOneIPBinary knapsackBinaryStructured_TMInNP
  let hJobSequencingBinary :=
    jobSequencingBinaryStructuredPackagedTMNPCompleteOfKnapsackBinary
      hKnapsackBinary jobSequencingBinaryStructured_TMInNP
  let hJobSequencing :=
    jobSequencingStructuredPackagedTMNPCompleteOfKnapsack
      sources.knapsackStructured jobSequencingStructured_TMInNP
  let hPartition :=
    partitionStructuredPackagedTMNPCompleteOfKnapsack
      sources.knapsackStructured partitionStructured_TMInNP
  let hPartitionBinary :=
    partitionBinaryStructuredPackagedTMNPCompleteOfStructured
      hPartition partitionBinaryStructured_TMInNP
  let hMaxCut :=
    maxCutStructuredPackagedTMNPCompleteOfPartition hPartition maxCutStructured_TMInNP
  let hMaxCutBinary :=
    maxCutBinaryStructuredPackagedTMNPCompleteOfStructured
      hMaxCut maxCutBinaryStructured_TMInNP
  exact
    { threeSatisfiability := hThreeSAT
      satisfiability := hSatisfiability
      zeroOneIP := hZeroOneIP
      clique := hClique
      chromaticNumber := hChromatic
      setPacking := hSetPacking
      vertexCover := hVertexCover
      setCovering := hSetCovering
      feedbackNodeSet := hFeedbackNode
      feedbackArcSet := hFeedbackArc
      directedHamiltonianCircuit := hDirected
      undirectedHamiltonianCircuit := hUndirected
      cliqueCover := hCliqueCover
      exactCover := hExactCover
      hittingSet := hHittingSet
      steinerTree := hSteinerTree
      threeDimensionalMatching := hThreeDM
      zeroOneIPBinary := hZeroOneIPBinary
      knapsackBinary := hKnapsackBinary
      jobSequencingBinary := hJobSequencingBinary
      partitionBinary := hPartitionBinary
      knapsackStructured := sources.knapsackStructured
      jobSequencing := hJobSequencing
      partition := hPartition
      maxCut := hMaxCut
      maxCutBinary := hMaxCutBinary }

end Karp21
end ComplexityReduction
