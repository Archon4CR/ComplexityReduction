/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.SAT.CookLevin.XOnlyCheckedSuffixDecoderTM

/-!
Checked suffix-generator staging for the x-only Cook-Levin route.

This module does not assert a uniform standard-TM Cook-Levin generator.  It
records the proof-carrying shape that such a local suffix generator must have:
representative atom, clause, and CNF generators with direct `TMPolyTimeMap`
certificates, plus the semantic suffix bridges consumed by
`TMVerifierXOnlyCheckedSuffixValidity`.
-/

namespace ComplexityReduction
namespace SAT

/--
Proof-carrying descriptor for a checked suffix generator for one verifier.

The atom and clause layers are staging hooks for concrete generator
formalizations.  The CNF layer and the two semantic bridge fields are the part
used to build the existing checked suffix-validity package.
-/
structure TMVerifierXOnlyCheckedSuffixGeneratorDescriptor
    {L : EncodedDecisionProblem} (V : TMVerifier L) where
  descriptorName : String := "x_only_checked_suffix_generator"
  moduleName : String := "ComplexityReduction.SAT.CookLevin.XOnlyCheckedSuffixGeneratorTM"
  suffixAtom : L.Instance.Carrier -> Literal
  suffixClause : L.Instance.Carrier -> Clause
  suffixCNF : L.Instance.Carrier -> CNF
  suffixAtom_tm_polytime :
    TMPolyTimeMap L.Instance literalStructuredEncodedType suffixAtom
  suffixClause_tm_polytime :
    TMPolyTimeMap L.Instance clauseStructuredEncodedType suffixClause
  suffixCNF_tm_polytime :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType suffixCNF
  validSuffixSeed_satisfies :
    {B : TMVerifierPushPayloadBoundary V} ->
      {x : L.Instance.Carrier} ->
        {a : Assignment} ->
          TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a ->
            CNF.Satisfies (suffixCNF x) a
  decodedSuffix_valid_of_satisfies :
    {B : TMVerifierPushPayloadBoundary V} ->
      {x : L.Instance.Carrier} ->
        {a : Assignment} ->
          (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) ->
            CNF.Satisfies (suffixCNF x) a ->
              TMVerifierCertificateWordSuffix V x E.decodedInitialCertificateSuffixWord

namespace TMVerifierXOnlyCheckedSuffixGeneratorDescriptor

/--
Checked suffix-generator descriptors are not root Cook-Levin theorem
certificates by themselves.
-/
def generatorMayUseAsRootTheorem
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (_G : TMVerifierXOnlyCheckedSuffixGeneratorDescriptor V) : Bool :=
  false

end TMVerifierXOnlyCheckedSuffixGeneratorDescriptor

/-- A checked suffix-generator descriptor is explicitly not a root theorem. -/
theorem checkedSuffixGeneratorDescriptor_not_root_theorem
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixGeneratorDescriptor V) :
    G.generatorMayUseAsRootTheorem = false :=
  rfl

/-- Extract the direct-TM witness for the staged suffix atom generator. -/
theorem tmVerifierCheckedSuffixAtom_tm_polytime
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixGeneratorDescriptor V) :
    TMPolyTimeMap L.Instance literalStructuredEncodedType G.suffixAtom :=
  G.suffixAtom_tm_polytime

/-- Extract the direct-TM witness for the staged suffix clause generator. -/
theorem tmVerifierCheckedSuffixClause_tm_polytime
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixGeneratorDescriptor V) :
    TMPolyTimeMap L.Instance clauseStructuredEncodedType G.suffixClause :=
  G.suffixClause_tm_polytime

/-- Extract the direct-TM witness for the checked suffix CNF generator. -/
theorem tmVerifierCheckedSuffixCNF_tm_polytime
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixGeneratorDescriptor V) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType G.suffixCNF :=
  G.suffixCNF_tm_polytime

/--
Turn a proof-carrying suffix-generator descriptor into the checked validity
package used by the x-only Cook-Levin route.
-/
noncomputable def tmVerifierXOnlyCheckedSuffixValidityOfGenerator
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixGeneratorDescriptor V) :
    TMVerifierXOnlyCheckedSuffixValidity V where
  suffixValidityCNF := G.suffixCNF
  suffixValidityCNF_tm_polytime := tmVerifierCheckedSuffixCNF_tm_polytime G
  validSuffixSeed_satisfies := by
    intro B x a w
    exact G.validSuffixSeed_satisfies w
  decodedSuffix_valid_of_satisfies := by
    intro B x a E hSuffix
    exact G.decodedSuffix_valid_of_satisfies E hSuffix

@[simp]
theorem tmVerifierXOnlyCheckedSuffixValidityOfGenerator_suffixValidityCNF
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixGeneratorDescriptor V) :
    (tmVerifierXOnlyCheckedSuffixValidityOfGenerator G).suffixValidityCNF = G.suffixCNF :=
  rfl

#check TMVerifierXOnlyCheckedSuffixGeneratorDescriptor
#check TMVerifierXOnlyCheckedSuffixGeneratorDescriptor.generatorMayUseAsRootTheorem
#check checkedSuffixGeneratorDescriptor_not_root_theorem
#check tmVerifierCheckedSuffixAtom_tm_polytime
#check tmVerifierCheckedSuffixClause_tm_polytime
#check tmVerifierCheckedSuffixCNF_tm_polytime
#check tmVerifierXOnlyCheckedSuffixValidityOfGenerator
#check tmVerifierXOnlyCheckedSuffixValidityOfGenerator_suffixValidityCNF

end SAT
end ComplexityReduction
