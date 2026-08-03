/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Examples.OneInThree
import ComplexityReduction.CSP.Examples.NAE3SAT
import ComplexityReduction.CSP.Examples.TwoSATLike
import ComplexityReduction.CSP.Examples.ThreeSATLike
import ComplexityReduction.CSP.Examples.Horn3SATLike
import ComplexityReduction.CSP.Examples.DualHorn3SATLike
import ComplexityReduction.CSP.Examples.XOR3SATLike
import ComplexityReduction.CSP.Examples.ValidityExamples
import ComplexityReduction.CSP.Examples.MixedFiniteLanguage
import ComplexityReduction.CSP.Examples.FourSATLike
import ComplexityReduction.CSP.Hardness.OneInThree
import ComplexityReduction.CSP.Hardness.OneInThreeNPC
import ComplexityReduction.CSP.Hardness.ThreeSATLike
import ComplexityReduction.CSP.Hardness.ThreeSATLikeNPC
import ComplexityReduction.CSP.Hardness.MixedFiniteLanguage
import ComplexityReduction.CSP.Hardness.NAE3SAT
import ComplexityReduction.CSP.Hardness.NAE3SATNPC
import ComplexityReduction.CSP.Hardness.NAE3SATPinned

/-!
Tool-visible reference catalog of concrete Boolean CSP decision problems.

The example files provide the verified definitions.  This module organizes
them by Schaefer-style tags and records which theorem level is currently
available.  In particular, all arity-at-most-three entries carry the actual
project-local Karp reduction to 3SAT, and the arity-four entry records the
staged unrestricted-arity costed bridge.
-/

namespace ComplexityReduction
namespace CSP
namespace Examples
namespace Catalog

open SAT

/-- Coarse Schaefer-style tags used by the local CSP problem catalog. -/
inductive SchaeferTag where
  | horn
  | dualHorn
  | bijunctive
  | affine
  | zeroValid
  | oneValid
  | hardCandidate
  | mixedLanguage
  | unrestrictedArity
  deriving DecidableEq, Repr

/-- What kind of complexity statement the catalog is allowed to claim. -/
inductive ClaimStatus where
  | upperBoundOnly
  | tractableWitness
  | hardCandidateNeedsReverseReduction
  | npcTransferNotFormalized
  | conditionalNPCTransferPackaged
  deriving DecidableEq, Repr

/-- Available formal output level for the stored reduction. -/
inductive ReductionLevel where
  | semantic
  | costedKarp
  deriving DecidableEq, Repr

/-- A concrete arity-at-most-three Boolean CSP problem with a verified costed Karp bridge. -/
structure ThreeBoundedProblemDescriptor where
  name : String
  languageSymbol : String
  decisionProblemSymbol : String
  language : BoolLanguage
  isThreeBounded : language.IsThreeBounded
  schaeferTags : List SchaeferTag
  claimStatus : ClaimStatus
  reductionLevel : ReductionLevel
  reductionSymbol : String
  karpReduction :
    KarpReductionM CostedPolyTimeModel (boolCSPDecisionProblem language)
      SAT.threeSATDecisionProblem
  notes : String

/-- A concrete unrestricted-arity Boolean CSP problem with a verified bridge. -/
structure GeneralProblemDescriptor where
  name : String
  languageSymbol : String
  decisionProblemSymbol : String
  language : BoolLanguage
  schaeferTags : List SchaeferTag
  claimStatus : ClaimStatus
  reductionLevel : ReductionLevel
  reductionSymbol : String
  semanticReduction : SemanticReduction (boolCSPDecisionProblem language)
    SAT.threeSATDecisionProblem
  karpReduction? : Option
    (KarpReductionM CostedPolyTimeModel (boolCSPDecisionProblem language)
      SAT.threeSATDecisionProblem)
  notes : String

/-- A hard-case reverse bridge from local 3SAT into a concrete CSP language. -/
structure ThreeSATReverseDescriptor where
  name : String
  languageSymbol : String
  decisionProblemSymbol : String
  language : BoolLanguage
  claimStatus : ClaimStatus
  reductionLevel : ReductionLevel
  reductionSymbol : String
  semanticReduction : SemanticReduction SAT.threeSATDecisionProblem
    (boolCSPDecisionProblem language)
  karpReduction? : Option
    (KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem
      (boolCSPDecisionProblem language))
  remainingWork : String

/-- A hard sublanguage embedding into a concrete CSP language. -/
structure SublanguageEmbeddingDescriptor where
  name : String
  sourceProblemSymbol : String
  targetProblemSymbol : String
  targetLanguageSymbol : String
  claimStatus : ClaimStatus
  reductionLevel : ReductionLevel
  reductionSymbol : String
  remainingWork : String

namespace ThreeBoundedProblemDescriptor

/-- The encoded decision problem associated with a three-bounded catalog entry. -/
def decisionProblem (d : ThreeBoundedProblemDescriptor) : EncodedDecisionProblem :=
  boolCSPDecisionProblem d.language

/-- The generic costed Karp bridge stored in a three-bounded catalog entry. -/
def toThreeSATKarpReduction (d : ThreeBoundedProblemDescriptor) :
    KarpReductionM CostedPolyTimeModel d.decisionProblem SAT.threeSATDecisionProblem :=
  d.karpReduction

end ThreeBoundedProblemDescriptor

namespace GeneralProblemDescriptor

/-- The encoded decision problem associated with a general catalog entry. -/
def decisionProblem (d : GeneralProblemDescriptor) : EncodedDecisionProblem :=
  boolCSPDecisionProblem d.language

/-- The semantic 3SAT bridge stored in a general catalog entry. -/
def toThreeSATSemanticReduction (d : GeneralProblemDescriptor) :
    SemanticReduction d.decisionProblem SAT.threeSATDecisionProblem :=
  d.semanticReduction

/-- The costed Karp 3SAT bridge, when the general-arity entry has one. -/
def toThreeSATKarpReduction? (d : GeneralProblemDescriptor) :
    Option (KarpReductionM CostedPolyTimeModel d.decisionProblem SAT.threeSATDecisionProblem) :=
  d.karpReduction?

end GeneralProblemDescriptor

namespace ThreeSATReverseDescriptor

/-- The encoded decision problem associated with a reverse-reduction entry. -/
def decisionProblem (d : ThreeSATReverseDescriptor) : EncodedDecisionProblem :=
  boolCSPDecisionProblem d.language

/-- The semantic reverse bridge stored in a reverse-reduction entry. -/
def fromThreeSATSemanticReduction (d : ThreeSATReverseDescriptor) :
    SemanticReduction SAT.threeSATDecisionProblem d.decisionProblem :=
  d.semanticReduction

/-- The costed Karp reverse bridge, when the catalog entry has one. -/
def fromThreeSATKarpReduction? (d : ThreeSATReverseDescriptor) :
    Option (KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem d.decisionProblem) :=
  d.karpReduction?

end ThreeSATReverseDescriptor

/-- Catalog entry for one-in-three SAT. -/
noncomputable def oneInThreeEntry : ThreeBoundedProblemDescriptor :=
  { name := "one-in-three SAT"
    languageSymbol := "ComplexityReduction.CSP.Examples.oneInThreeLanguage"
    decisionProblemSymbol := "ComplexityReduction.CSP.Examples.oneInThreeDecisionProblem"
    language := oneInThreeLanguage
    isThreeBounded := oneInThreeLanguage_isThreeBounded
    schaeferTags := [SchaeferTag.hardCandidate]
    claimStatus := ClaimStatus.conditionalNPCTransferPackaged
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol := "ComplexityReduction.CSP.Examples.oneInThreeToThreeSATKarpReduction"
    karpReduction := oneInThreeToThreeSATKarpReduction
    notes := "Upper-bound bridge is formalized; NPC transfer uses the packaged reverse gadget." }

/-- Catalog entry for NAE-3SAT. -/
noncomputable def nae3Entry : ThreeBoundedProblemDescriptor :=
  { name := "NAE-3SAT"
    languageSymbol := "ComplexityReduction.CSP.Examples.notAllEqual3Language"
    decisionProblemSymbol := "ComplexityReduction.CSP.Examples.notAllEqual3DecisionProblem"
    language := notAllEqual3Language
    isThreeBounded := notAllEqual3Language_isThreeBounded
    schaeferTags := [SchaeferTag.hardCandidate]
    claimStatus := ClaimStatus.conditionalNPCTransferPackaged
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol := "ComplexityReduction.CSP.Examples.notAllEqual3ToThreeSATKarpReduction"
    karpReduction := notAllEqual3ToThreeSATKarpReduction
    notes := "Upper-bound bridge is formalized; NPC transfer uses the packaged ordinary gadget." }

/-- Catalog entry for binary-clause 2SAT-like CSP. -/
noncomputable def twoSATEntry : ThreeBoundedProblemDescriptor :=
  { name := "binary-clause 2SAT-like CSP"
    languageSymbol := "ComplexityReduction.CSP.Examples.twoSATLanguage"
    decisionProblemSymbol := "ComplexityReduction.CSP.Examples.twoSATDecisionProblem"
    language := twoSATLanguage
    isThreeBounded := twoSATLanguage_isThreeBounded
    schaeferTags := [SchaeferTag.bijunctive]
    claimStatus := ClaimStatus.upperBoundOnly
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol := "ComplexityReduction.CSP.Examples.twoSATToThreeSATKarpReduction"
    karpReduction := twoSATToThreeSATKarpReduction
    notes := "This entry is an upper-bound regression case, not an NP-hardness claim." }

/-- Catalog entry for ternary-clause 3SAT-like CSP. -/
noncomputable def threeSATLikeEntry : ThreeBoundedProblemDescriptor :=
  { name := "ternary-clause 3SAT-like CSP"
    languageSymbol := "ComplexityReduction.CSP.Examples.threeSATLikeLanguage"
    decisionProblemSymbol := "ComplexityReduction.CSP.Examples.threeSATLikeDecisionProblem"
    language := threeSATLikeLanguage
    isThreeBounded := threeSATLikeLanguage_isThreeBounded
    schaeferTags := [SchaeferTag.hardCandidate]
    claimStatus := ClaimStatus.conditionalNPCTransferPackaged
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol := "ComplexityReduction.CSP.Examples.threeSATLikeToThreeSATKarpReduction"
    karpReduction := threeSATLikeToThreeSATKarpReduction
    notes := "CSP syntax mirror of 3SAT clauses; costed reverse adapter is packaged." }

/-- Catalog entry for ternary Horn CSP. -/
noncomputable def horn3Entry : ThreeBoundedProblemDescriptor :=
  { name := "ternary Horn CSP"
    languageSymbol := "ComplexityReduction.CSP.Examples.horn3Language"
    decisionProblemSymbol := "ComplexityReduction.CSP.Examples.horn3DecisionProblem"
    language := horn3Language
    isThreeBounded := horn3Language_isThreeBounded
    schaeferTags := [SchaeferTag.horn]
    claimStatus := ClaimStatus.upperBoundOnly
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol := "ComplexityReduction.CSP.Examples.horn3ToThreeSATKarpReduction"
    karpReduction := horn3ToThreeSATKarpReduction
    notes := "Tractable-side Schaefer example; no hardness claim is exposed." }

/-- Catalog entry for ternary dual-Horn CSP. -/
noncomputable def dualHorn3Entry : ThreeBoundedProblemDescriptor :=
  { name := "ternary dual-Horn CSP"
    languageSymbol := "ComplexityReduction.CSP.Examples.dualHorn3Language"
    decisionProblemSymbol := "ComplexityReduction.CSP.Examples.dualHorn3DecisionProblem"
    language := dualHorn3Language
    isThreeBounded := dualHorn3Language_isThreeBounded
    schaeferTags := [SchaeferTag.dualHorn]
    claimStatus := ClaimStatus.upperBoundOnly
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol := "ComplexityReduction.CSP.Examples.dualHorn3ToThreeSATKarpReduction"
    karpReduction := dualHorn3ToThreeSATKarpReduction
    notes := "Tractable-side Schaefer example; no hardness claim is exposed." }

/-- Catalog entry for odd ternary XOR CSP. -/
noncomputable def xor3Entry : ThreeBoundedProblemDescriptor :=
  { name := "odd ternary XOR CSP"
    languageSymbol := "ComplexityReduction.CSP.Examples.xor3Language"
    decisionProblemSymbol := "ComplexityReduction.CSP.Examples.xor3DecisionProblem"
    language := xor3Language
    isThreeBounded := xor3Language_isThreeBounded
    schaeferTags := [SchaeferTag.affine]
    claimStatus := ClaimStatus.upperBoundOnly
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol := "ComplexityReduction.CSP.Examples.xor3ToThreeSATKarpReduction"
    karpReduction := xor3ToThreeSATKarpReduction
    notes := "Affine Schaefer example; no hardness claim is exposed." }

/-- Catalog entry for 1-valid positive ternary clauses. -/
noncomputable def positive3ClauseEntry : ThreeBoundedProblemDescriptor :=
  { name := "1-valid positive ternary clauses"
    languageSymbol := "ComplexityReduction.CSP.Examples.positive3ClauseLanguage"
    decisionProblemSymbol := "ComplexityReduction.CSP.Examples.positive3ClauseDecisionProblem"
    language := positive3ClauseLanguage
    isThreeBounded := positive3ClauseLanguage_isThreeBounded
    schaeferTags := [SchaeferTag.oneValid, SchaeferTag.dualHorn]
    claimStatus := ClaimStatus.tractableWitness
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol := "ComplexityReduction.CSP.Examples.positive3ClauseToThreeSATKarpReduction"
    karpReduction := positive3ClauseToThreeSATKarpReduction
    notes := "Every formula is witnessed satisfiable by the all-true assignment." }

/-- Catalog entry for 0-valid negative ternary clauses. -/
noncomputable def negative3ClauseEntry : ThreeBoundedProblemDescriptor :=
  { name := "0-valid negative ternary clauses"
    languageSymbol := "ComplexityReduction.CSP.Examples.negative3ClauseLanguage"
    decisionProblemSymbol := "ComplexityReduction.CSP.Examples.negative3ClauseDecisionProblem"
    language := negative3ClauseLanguage
    isThreeBounded := negative3ClauseLanguage_isThreeBounded
    schaeferTags := [SchaeferTag.zeroValid, SchaeferTag.horn]
    claimStatus := ClaimStatus.tractableWitness
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol := "ComplexityReduction.CSP.Examples.negative3ClauseToThreeSATKarpReduction"
    karpReduction := negative3ClauseToThreeSATKarpReduction
    notes := "Every formula is witnessed satisfiable by the all-false assignment." }

/-- Catalog entry for the mixed finite-language regression case. -/
noncomputable def mixedFiniteEntry : ThreeBoundedProblemDescriptor :=
  { name := "mixed finite Boolean CSP"
    languageSymbol := "ComplexityReduction.CSP.Examples.mixedFiniteLanguage"
    decisionProblemSymbol := "ComplexityReduction.CSP.Examples.mixedFiniteDecisionProblem"
    language := mixedFiniteLanguage
    isThreeBounded := mixedFiniteLanguage_isThreeBounded
    schaeferTags := [SchaeferTag.mixedLanguage, SchaeferTag.hardCandidate]
    claimStatus := ClaimStatus.hardCandidateNeedsReverseReduction
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol := "ComplexityReduction.CSP.Examples.mixedFiniteToThreeSATKarpReduction"
    karpReduction := mixedFiniteToThreeSATKarpReduction
    notes := "Multi-symbol regression case; hardness transfer is not formalized here." }

/-- Catalog of arity-at-most-three problems with costed Karp bridges to local 3SAT. -/
noncomputable def threeBoundedProblems : List ThreeBoundedProblemDescriptor :=
  [ oneInThreeEntry
  , nae3Entry
  , twoSATEntry
  , threeSATLikeEntry
  , horn3Entry
  , dualHorn3Entry
  , xor3Entry
  , positive3ClauseEntry
  , negative3ClauseEntry
  , mixedFiniteEntry
  ]

@[simp]
theorem threeBoundedProblems_length :
    threeBoundedProblems.length = 10 :=
  rfl

/-- Catalog entry for the arity-four positive-clause example. -/
noncomputable def fourClauseEntry : GeneralProblemDescriptor :=
  { name := "positive arity-four clause CSP"
    languageSymbol := "ComplexityReduction.CSP.Examples.fourClauseLanguage"
    decisionProblemSymbol := "ComplexityReduction.CSP.Examples.fourClauseDecisionProblem"
    language := fourClauseLanguage
    schaeferTags := [SchaeferTag.unrestrictedArity, SchaeferTag.oneValid]
    claimStatus := ClaimStatus.upperBoundOnly
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol :=
      "ComplexityReduction.CSP.boolCSPToThreeSATGeneralKarpReduction"
    semanticReduction := fourClauseToThreeSATGeneralReduction
    karpReduction? := some (boolCSPToThreeSATGeneralKarpReduction fourClauseLanguage)
    notes := "Uses the generic fixed finite-language unrestricted-arity costed certificate." }

/-- Catalog of unrestricted-arity examples. -/
noncomputable def generalProblems : List GeneralProblemDescriptor :=
  [fourClauseEntry]

@[simp]
theorem generalProblems_length :
    generalProblems.length = 1 :=
  rfl

/-- Semantic reverse adapter from local 3SAT into the 3SAT-like CSP language. -/
noncomputable def threeSATLikeReverseEntry : ThreeSATReverseDescriptor :=
  { name := "local 3SAT to ternary-clause 3SAT-like CSP"
    languageSymbol := "ComplexityReduction.CSP.Examples.threeSATLikeLanguage"
    decisionProblemSymbol := "ComplexityReduction.CSP.Examples.threeSATLikeDecisionProblem"
    language := threeSATLikeLanguage
    claimStatus := ClaimStatus.conditionalNPCTransferPackaged
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol :=
      "ComplexityReduction.CSP.Hardness.ThreeSATLike.threeSATToThreeSATLikeKarpReduction"
    semanticReduction := Hardness.ThreeSATLike.threeSATToThreeSATLikeReduction
    karpReduction? := some Hardness.ThreeSATLike.threeSATToThreeSATLikeKarpReduction
    remainingWork :=
      "Local NPC transfer is packaged as \
       ComplexityReduction.CSP.Hardness.ThreeSATLike.threeSATLikeNPComplete; \
       3SAT completeness is discharged by ComplexityReduction.SAT.localCookLevinTheorem." }

/-- Costed reverse adapter from local 3SAT into ordinary one-in-three SAT. -/
noncomputable def oneInThreeReverseEntry : ThreeSATReverseDescriptor :=
  { name := "local 3SAT to ordinary one-in-three SAT"
    languageSymbol := "ComplexityReduction.CSP.Examples.oneInThreeLanguage"
    decisionProblemSymbol := "ComplexityReduction.CSP.Examples.oneInThreeDecisionProblem"
    language := oneInThreeLanguage
    claimStatus := ClaimStatus.conditionalNPCTransferPackaged
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol :=
      "ComplexityReduction.CSP.Hardness.OneInThree.threeSATToOneInThreeKarpReduction"
    semanticReduction := Hardness.OneInThree.threeSATToOneInThreeReduction
    karpReduction? := some Hardness.OneInThree.threeSATToOneInThreeKarpReduction
    remainingWork :=
      "Local NPC transfer is packaged as \
       ComplexityReduction.CSP.Hardness.OneInThree.oneInThreeNPComplete; \
       3SAT completeness is discharged by ComplexityReduction.SAT.localCookLevinTheorem." }

/-- Costed reverse adapter from local 3SAT into the pinned polarized NAE-3SAT language. -/
noncomputable def nae3PinnedReverseEntry : ThreeSATReverseDescriptor :=
  { name := "local 3SAT to pinned polarized NAE-3SAT"
    languageSymbol := "ComplexityReduction.CSP.Hardness.NAE3SATPinned.nae3PinnedLanguage"
    decisionProblemSymbol :=
      "ComplexityReduction.CSP.Hardness.NAE3SATPinned.nae3PinnedDecisionProblem"
    language := Hardness.NAE3SATPinned.nae3PinnedLanguage
    claimStatus := ClaimStatus.npcTransferNotFormalized
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol :=
      "ComplexityReduction.CSP.Hardness.NAE3SATPinned.threeSATToNAE3PinnedKarpReduction"
    semanticReduction := Hardness.NAE3SATPinned.threeSATToNAE3PinnedReduction
    karpReduction? := some Hardness.NAE3SATPinned.threeSATToNAE3PinnedKarpReduction
    remainingWork :=
      "Pinned, polarized intermediate hardness is packaged; ordinary NAE-3SAT still needs \
       pinning/polarity elimination before any ordinary NAE NPC claim." }

/-- Costed reverse adapter from local 3SAT into ordinary NAE-3SAT. -/
noncomputable def nae3ReverseEntry : ThreeSATReverseDescriptor :=
  { name := "local 3SAT to ordinary NAE-3SAT"
    languageSymbol := "ComplexityReduction.CSP.Examples.notAllEqual3Language"
    decisionProblemSymbol := "ComplexityReduction.CSP.Examples.notAllEqual3DecisionProblem"
    language := notAllEqual3Language
    claimStatus := ClaimStatus.conditionalNPCTransferPackaged
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol :=
      "ComplexityReduction.CSP.Hardness.NAE3SAT.threeSATToNAE3KarpReduction"
    semanticReduction := Hardness.NAE3SAT.threeSATToNAE3Reduction
    karpReduction? := some Hardness.NAE3SAT.threeSATToNAE3KarpReduction
    remainingWork :=
      "Local NPC transfer is packaged as \
       ComplexityReduction.CSP.Hardness.NAE3SAT.nae3NPComplete; \
       3SAT completeness is discharged by ComplexityReduction.SAT.localCookLevinTheorem." }

/-- Sublanguage embedding from one-in-three SAT into the mixed finite language. -/
def oneInThreeToMixedFiniteEmbeddingEntry : SublanguageEmbeddingDescriptor :=
  { name := "one-in-three SAT to mixed finite Boolean CSP"
    sourceProblemSymbol := "ComplexityReduction.CSP.Examples.oneInThreeDecisionProblem"
    targetProblemSymbol := "ComplexityReduction.CSP.Examples.mixedFiniteDecisionProblem"
    targetLanguageSymbol := "ComplexityReduction.CSP.Examples.mixedFiniteLanguage"
    claimStatus := ClaimStatus.hardCandidateNeedsReverseReduction
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol :=
      "ComplexityReduction.CSP.Hardness.MixedFiniteLanguage.oneInThreeToMixedFiniteKarpReduction"
    remainingWork :=
      "This entry records the mixed-language sublanguage embedding; NPC transfer still needs \
       a verified mixed-language hard theorem; local 3SAT completeness is already available." }

/-- Sublanguage embedding from NAE-3SAT into the mixed finite language. -/
def nae3ToMixedFiniteEmbeddingEntry : SublanguageEmbeddingDescriptor :=
  { name := "NAE-3SAT to mixed finite Boolean CSP"
    sourceProblemSymbol := "ComplexityReduction.CSP.Examples.notAllEqual3DecisionProblem"
    targetProblemSymbol := "ComplexityReduction.CSP.Examples.mixedFiniteDecisionProblem"
    targetLanguageSymbol := "ComplexityReduction.CSP.Examples.mixedFiniteLanguage"
    claimStatus := ClaimStatus.hardCandidateNeedsReverseReduction
    reductionLevel := ReductionLevel.costedKarp
    reductionSymbol :=
      "ComplexityReduction.CSP.Hardness.MixedFiniteLanguage.nae3ToMixedFiniteKarpReduction"
    remainingWork :=
      "This entry records the mixed-language sublanguage embedding; NPC transfer still needs \
       a verified mixed-language hard theorem; local 3SAT completeness is already available." }

/-- Hard-case reverse bridges currently available. -/
noncomputable def threeSATReverseReductions : List ThreeSATReverseDescriptor :=
  [threeSATLikeReverseEntry, oneInThreeReverseEntry, nae3PinnedReverseEntry, nae3ReverseEntry]

@[simp]
theorem threeSATReverseReductions_length :
    threeSATReverseReductions.length = 4 :=
  rfl

/-- Hard sublanguage embeddings currently available. -/
def hardSublanguageEmbeddings : List SublanguageEmbeddingDescriptor :=
  [oneInThreeToMixedFiniteEmbeddingEntry, nae3ToMixedFiniteEmbeddingEntry]

@[simp]
theorem hardSublanguageEmbeddings_length :
    hardSublanguageEmbeddings.length = 2 :=
  rfl

/-- Missing proof obligations before a hard-candidate entry can be claimed NP-complete. -/
structure HardCaseChecklist where
  sourceName : String
  candidateProblemSymbol : String
  availableUpperBoundSymbol : String
  availableReverseReductionSymbol : Option String
  remainingReverseReductionWork : String
  missingCompletenessTransfer : String
  forbiddenShortcut : String
  deriving Repr

/-- Guardrail checklist for entries that look like Schaefer hard cases. -/
def hardCaseChecklists : List HardCaseChecklist :=
  [ { sourceName := "one-in-three SAT"
      candidateProblemSymbol := "ComplexityReduction.CSP.Examples.oneInThreeDecisionProblem"
      availableUpperBoundSymbol :=
        "ComplexityReduction.CSP.Examples.oneInThreeToThreeSATKarpReduction"
      availableReverseReductionSymbol := some
        "ComplexityReduction.CSP.Hardness.OneInThree.threeSATToOneInThreeKarpReduction"
      remainingReverseReductionWork :=
        "Local NPC transfer via ComplexityReduction.CSP.Hardness.OneInThree.oneInThreeNPComplete"
      missingCompletenessTransfer :=
        "No missing transfer: local 3SAT completeness is discharged by SAT.localCookLevinTheorem"
      forbiddenShortcut := "Do not claim NP-hardness from the upper-bound reduction." }
  , { sourceName := "NAE-3SAT"
      candidateProblemSymbol := "ComplexityReduction.CSP.Examples.notAllEqual3DecisionProblem"
      availableUpperBoundSymbol :=
        "ComplexityReduction.CSP.Examples.notAllEqual3ToThreeSATKarpReduction"
      availableReverseReductionSymbol := some
        "ComplexityReduction.CSP.Hardness.NAE3SAT.threeSATToNAE3KarpReduction"
      remainingReverseReductionWork :=
        "Local NPC transfer via ComplexityReduction.CSP.Hardness.NAE3SAT.nae3NPComplete"
      missingCompletenessTransfer :=
        "No missing transfer: local 3SAT completeness is discharged by SAT.localCookLevinTheorem"
      forbiddenShortcut := "Do not claim NP-hardness from the upper-bound reduction." }
  , { sourceName := "ternary-clause 3SAT-like CSP"
      candidateProblemSymbol := "ComplexityReduction.CSP.Examples.threeSATLikeDecisionProblem"
      availableUpperBoundSymbol :=
        "ComplexityReduction.CSP.Examples.threeSATLikeToThreeSATKarpReduction"
      availableReverseReductionSymbol := some
        "ComplexityReduction.CSP.Hardness.ThreeSATLike.threeSATToThreeSATLikeKarpReduction"
      remainingReverseReductionWork :=
        "Local NPC transfer via ComplexityReduction.CSP.Hardness.ThreeSATLike.threeSATLikeNPComplete"
      missingCompletenessTransfer :=
        "No missing transfer: local 3SAT completeness is discharged by SAT.localCookLevinTheorem"
      forbiddenShortcut := "Do not use name similarity as a theorem." }
  , { sourceName := "mixed finite Boolean CSP"
      candidateProblemSymbol := "ComplexityReduction.CSP.Examples.mixedFiniteDecisionProblem"
      availableUpperBoundSymbol :=
        "ComplexityReduction.CSP.Examples.mixedFiniteToThreeSATKarpReduction"
      availableReverseReductionSymbol := some
        "ComplexityReduction.CSP.Hardness.MixedFiniteLanguage.oneInThreeToMixedFiniteKarpReduction"
      remainingReverseReductionWork :=
        "NPC transfer still needs a final mixed-language hard theorem; local 3SAT completeness is available"
      missingCompletenessTransfer :=
        "Need a verified mixed-language NP-completeness theorem, not just a sublanguage embedding"
      forbiddenShortcut := "Do not infer hardness from containing a symbol name." }
  ]

@[simp]
theorem hardCaseChecklists_length :
    hardCaseChecklists.length = 4 :=
  rfl

/-- Missing proof obligations before tractable-side entries can claim polynomial algorithms. -/
structure TractableChecklist where
  sourceName : String
  problemSymbol : String
  schaeferReason : String
  availableUpperBoundSymbol : String
  missingAlgorithmProof : String
  forbiddenClaim : String
  deriving Repr

/-- Guardrail checklist for tractable-side examples. -/
def tractableChecklists : List TractableChecklist :=
  [ { sourceName := "binary-clause 2SAT-like CSP"
      problemSymbol := "ComplexityReduction.CSP.Examples.twoSATDecisionProblem"
      schaeferReason := "bijunctive"
      availableUpperBoundSymbol :=
        "ComplexityReduction.CSP.Examples.twoSATToThreeSATKarpReduction"
      missingAlgorithmProof := "formal 2SAT-style decision procedure is not packaged"
      forbiddenClaim := "Do not claim NP-hardness without a separate reverse reduction." }
  , { sourceName := "ternary Horn CSP"
      problemSymbol := "ComplexityReduction.CSP.Examples.horn3DecisionProblem"
      schaeferReason := "Horn"
      availableUpperBoundSymbol :=
        "ComplexityReduction.CSP.Examples.horn3ToThreeSATKarpReduction"
      missingAlgorithmProof := "formal Horn-SAT propagation algorithm is not packaged"
      forbiddenClaim := "Do not claim NP-hardness from upper-bound reducibility." }
  , { sourceName := "ternary dual-Horn CSP"
      problemSymbol := "ComplexityReduction.CSP.Examples.dualHorn3DecisionProblem"
      schaeferReason := "dual-Horn"
      availableUpperBoundSymbol :=
        "ComplexityReduction.CSP.Examples.dualHorn3ToThreeSATKarpReduction"
      missingAlgorithmProof := "formal dual-Horn propagation algorithm is not packaged"
      forbiddenClaim := "Do not claim NP-hardness from upper-bound reducibility." }
  , { sourceName := "odd ternary XOR CSP"
      problemSymbol := "ComplexityReduction.CSP.Examples.xor3DecisionProblem"
      schaeferReason := "affine"
      availableUpperBoundSymbol :=
        "ComplexityReduction.CSP.Examples.xor3ToThreeSATKarpReduction"
      missingAlgorithmProof := "formal Gaussian-elimination-style algorithm is not packaged"
      forbiddenClaim := "Do not claim NP-hardness from upper-bound reducibility." }
  , { sourceName := "1-valid positive ternary clauses"
      problemSymbol := "ComplexityReduction.CSP.Examples.positive3ClauseDecisionProblem"
      schaeferReason := "1-valid"
      availableUpperBoundSymbol :=
        "ComplexityReduction.CSP.Examples.positive3ClauseToThreeSATKarpReduction"
      missingAlgorithmProof := "constant all-true witness theorem is available, not yet a solver"
      forbiddenClaim := "Do not claim NP-hardness for this always-satisfiable language." }
  , { sourceName := "0-valid negative ternary clauses"
      problemSymbol := "ComplexityReduction.CSP.Examples.negative3ClauseDecisionProblem"
      schaeferReason := "0-valid"
      availableUpperBoundSymbol :=
        "ComplexityReduction.CSP.Examples.negative3ClauseToThreeSATKarpReduction"
      missingAlgorithmProof := "constant all-false witness theorem is available, not yet a solver"
      forbiddenClaim := "Do not claim NP-hardness for this always-satisfiable language." }
  ]

@[simp]
theorem tractableChecklists_length :
    tractableChecklists.length = 6 :=
  rfl

end Catalog
end Examples
end CSP
end ComplexityReduction
