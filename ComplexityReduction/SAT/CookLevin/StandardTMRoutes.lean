/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.SAT.CookLevin.WindowGrid
import ComplexityReduction.SAT.CookLevin.TMActiveSymbols
import ComplexityReduction.SAT.CookLevin.TMControlBlocks
import ComplexityReduction.SAT.CookLevin.TMStackActionBlocks
import ComplexityReduction.SAT.CookLevin.TMRootXOnly
import ComplexityReduction.SAT.CookLevin.TMRootStandard
import ComplexityReduction.SAT.CookLevin.XOnlyBoundsTM
import ComplexityReduction.SAT.CookLevin.XOnlyCheckedSuffixGeneratorTM
import ComplexityReduction.Bridges.TMEncodingDisciplineTemplates

/-!
Descriptor layer for standard-TM Cook-Levin components.

The descriptors in this file make existing local block-generation and boundary
symbols visible to route planners.  They do not assert a full standard-TM
Cook-Levin soundness theorem; entries explicitly separate checked local blocks
from metadata boundaries that still require additional witnesses.
-/

namespace ComplexityReduction
namespace SAT
namespace CookLevin
namespace TableauCSP

/-- Trust status for a standard-TM Cook-Levin route descriptor. -/
inductive StandardTMRouteStatus where
  | theoremUsable
  | checkedLocalBlock
  | metadataBoundary
  deriving DecidableEq, Repr

namespace StandardTMRouteStatus

/-- Stable string label for standard-TM route status metadata. -/
def label : StandardTMRouteStatus -> String
  | theoremUsable => "theorem_usable"
  | checkedLocalBlock => "checked_local_block"
  | metadataBoundary => "metadata_boundary"

end StandardTMRouteStatus

/-- Planner metadata for a standard-TM Cook-Levin component route. -/
structure StandardTMRouteDescriptor where
  name : String
  status : StandardTMRouteStatus
  moduleName : String
  localTargetSymbol : String
  theoremSymbols : List String := []
  supportSymbols : List String := []
  generatorMayUseAsTheorem : Bool
  requiredPremises : List String := []
  roles : List String := []
  notes : List String := []
  deriving Repr

/-- Active stack-symbol collection and membership surface. -/
def standardTMActiveSymbolRoute : StandardTMRouteDescriptor :=
  { name := "standard_tm_active_symbol_route"
    status := StandardTMRouteStatus.checkedLocalBlock
    moduleName := "ComplexityReduction.SAT.CookLevin.TMActiveSymbols"
    localTargetSymbol := "ComplexityReduction.SAT.tmVerifierActiveStackSymbols"
    theoremSymbols :=
      [ "ComplexityReduction.SAT.tmVerifierStackSymbolActive_input"
      , "ComplexityReduction.SAT.tmVerifierStackSymbolActive_output"
      , "ComplexityReduction.SAT.tmVerifierPushSymbolsFor_mem"
      , "ComplexityReduction.SAT.tmVerifierStmtPushSymbols_push_mem"
      , "ComplexityReduction.SAT.tmVerifierControlPushSymbols_label_mem" ]
    supportSymbols :=
      [ "ComplexityReduction.SAT.TMVerifierStackSymbol"
      , "ComplexityReduction.SAT.TMVerifierNamedStackSymbol"
      , "ComplexityReduction.SAT.tmVerifierNamedStackSymbolAtom"
      , "ComplexityReduction.SAT.tmVerifierActiveStackSymbolPayload" ]
    generatorMayUseAsTheorem := true
    requiredPremises := ["A concrete `TMVerifier L`."]
    roles := ["cook_levin", "standard_tm", "active_symbols", "checked_local_block"]
    notes :=
      [ "Indexes finite active-symbol collection lemmas."
      , "This is not a full transition-window correctness theorem." ] }

/-- Finite-control label/state CNF block surface. -/
def standardTMControlBlockRoute : StandardTMRouteDescriptor :=
  { name := "standard_tm_control_block_route"
    status := StandardTMRouteStatus.checkedLocalBlock
    moduleName := "ComplexityReduction.SAT.CookLevin.TMControlBlocks"
    localTargetSymbol := "ComplexityReduction.SAT.tmVerifierExactlyOneLabelCNFAt"
    theoremSymbols := ["ComplexityReduction.SAT.tmVerifierUnitCNF_satisfies"]
    supportSymbols :=
      [ "ComplexityReduction.SAT.tmVerifierLabelCode"
      , "ComplexityReduction.SAT.tmVerifierStateCode"
      , "ComplexityReduction.SAT.tmVerifierLabelAtom"
      , "ComplexityReduction.SAT.tmVerifierStateAtom"
      , "ComplexityReduction.SAT.tmVerifierInitialControlCNF"
      , "ComplexityReduction.SAT.tmVerifierHaltingControlCNFAt" ]
    generatorMayUseAsTheorem := true
    requiredPremises := ["A concrete `TMVerifier L` and an assignment to CNF atoms."]
    roles := ["cook_levin", "standard_tm", "control_block", "checked_local_block"]
    notes := ["Indexes local finite-control block definitions and the unit-CNF satisfaction lemma."] }

/-- Stack action/frame CNF block surface. -/
def standardTMStackBlockRoute : StandardTMRouteDescriptor :=
  { name := "standard_tm_stack_block_route"
    status := StandardTMRouteStatus.checkedLocalBlock
    moduleName := "ComplexityReduction.SAT.CookLevin.TMStackActionBlocks"
    localTargetSymbol := "ComplexityReduction.SAT.tmVerifierStackActionCNFBetween"
    theoremSymbols :=
      [ "ComplexityReduction.SAT.tmVerifierFrameForwardClause_satisfies"
      , "ComplexityReduction.SAT.tmVerifierStackActionCNFBetween_satisfies_effect_cnf"
      , "ComplexityReduction.SAT.tmVerifierStackActionReadCNFAt_satisfies"
      , "ComplexityReduction.SAT.tmVerifierStackActionCNFBetween_satisfies_read" ]
    supportSymbols :=
      [ "ComplexityReduction.SAT.TMVerifierPushPayloadBoundary"
      , "ComplexityReduction.SAT.tmVerifierFrameAllStacksCNFBetween"
      , "ComplexityReduction.SAT.tmVerifierPushActionCNFBetween"
      , "ComplexityReduction.SAT.tmVerifierPopActionCNFBetween"
      , "ComplexityReduction.SAT.tmVerifierPreserveAllStacksActionCNFBetween" ]
    generatorMayUseAsTheorem := true
    requiredPremises :=
      [ "A concrete `TMVerifier L`."
      , "A `TMVerifierPushPayloadBoundary` when push payload equality is needed." ]
    roles := ["cook_levin", "standard_tm", "stack_block", "checked_local_block"]
    notes :=
      [ "Indexes checked frame/read/effect block lemmas."
      , "Dependent push payload naming remains an explicit premise." ] }

/-- Transition-window control and statement-window surface. -/
def standardTMTransitionWindowRoute : StandardTMRouteDescriptor :=
  { name := "standard_tm_transition_window_route"
    status := StandardTMRouteStatus.checkedLocalBlock
    moduleName := "ComplexityReduction.SAT.CookLevin.TMTransitionWindows"
    localTargetSymbol := "ComplexityReduction.SAT.tmVerifierTransitionControlCNFAt"
    theoremSymbols :=
      [ "ComplexityReduction.SAT.tmVerifierImplicationClause_satisfies_of_antecedents"
      , "ComplexityReduction.SAT.tmVerifierWindowControlCNFAt_satisfies_next_control"
      , "ComplexityReduction.SAT.tmVerifierStmtWindowsAt_actions_readChoiceMem"
      , "ComplexityReduction.SAT.tmVerifierStmtWindowsAt_actions_pushSymbolMem_of_stmt"
      , "ComplexityReduction.SAT.tmVerifierStmtWindowsAt_goto_mem"
      , "ComplexityReduction.SAT.tmVerifierStmtWindowsAt_halt_mem"
      , "ComplexityReduction.SAT.tmVerifierStmtWindowsAt_push_action_mem" ]
    supportSymbols :=
      [ "ComplexityReduction.SAT.TMVerifierStmtTag"
      , "ComplexityReduction.SAT.TMVerifierStackReadChoice"
      , "ComplexityReduction.SAT.TMVerifierStackAction"
      , "ComplexityReduction.SAT.TMVerifierStmtWindow"
      , "ComplexityReduction.SAT.tmVerifierStmtWindowsAt"
      , "ComplexityReduction.SAT.tmVerifierWindowAntecedents" ]
    generatorMayUseAsTheorem := true
    requiredPremises := ["A concrete `TMVerifier L` and a selected statement window."]
    roles := ["cook_levin", "standard_tm", "transition_window", "checked_local_block"]
    notes := ["Indexes local transition-window membership and implication-CNF lemmas."] }

/-- Checked suffix-generator staging surface for the x-only root route. -/
def standardTMCheckedSuffixGeneratorRoute : StandardTMRouteDescriptor :=
  { name := "standard_tm_checked_suffix_generator_route"
    status := StandardTMRouteStatus.metadataBoundary
    moduleName := "ComplexityReduction.SAT.CookLevin.XOnlyCheckedSuffixGeneratorTM"
    localTargetSymbol := "ComplexityReduction.SAT.TMVerifierXOnlyCheckedSuffixGeneratorDescriptor"
    theoremSymbols :=
      [ "ComplexityReduction.SAT.checkedSuffixGeneratorDescriptor_not_root_theorem"
      , "ComplexityReduction.SAT.tmVerifierCheckedSuffixAtom_tm_polytime"
      , "ComplexityReduction.SAT.tmVerifierCheckedSuffixClause_tm_polytime"
      , "ComplexityReduction.SAT.tmVerifierCheckedSuffixCNF_tm_polytime"
      , "ComplexityReduction.SAT.tmVerifierXOnlyCheckedSuffixValidityOfGenerator" ]
    supportSymbols :=
      [ "ComplexityReduction.SAT.TMVerifierXOnlyCheckedSuffixGeneratorDescriptor"
      , "ComplexityReduction.SAT.TMVerifierXOnlyCheckedSuffixGeneratorDescriptor.generatorMayUseAsRootTheorem"
      , "ComplexityReduction.SAT.TMVerifierXOnlyCheckedSuffixValidity"
      , "ComplexityReduction.SAT.TMVerifierXOnlyCheckedSuffixDecoder"
      , "ComplexityReduction.SAT.TMVerifierXOnlyCheckedSuffixDecoder.toCheckedSuffixValidity"
      , "ComplexityReduction.SAT.tmVerifierFiniteBoolCheckedSuffixDecoder"
      , "ComplexityReduction.SAT.tmVerifierNatListCheckedSuffixDecoder" ]
    generatorMayUseAsTheorem := false
    requiredPremises :=
      [ "A concrete `TMVerifier L`."
      , "A proof-carrying `TMVerifierXOnlyCheckedSuffixGeneratorDescriptor V`."
      , "A separate direct `CNF.splitToThreeCNF` TM witness is still required for the root route." ]
    roles := ["cook_levin", "standard_tm", "checked_suffix_generator", "metadata_boundary"]
    notes :=
      [ "Packages direct atom/clause/CNF generator witnesses without asserting a root theorem."
      , "Use `tmVerifierXOnlyCheckedSuffixValidityOfGenerator` before entering the x-only checked-validity route." ] }

/-- X-only root boundary and polynomial-bound surface. -/
def standardTMXOnlyBoundaryRoute : StandardTMRouteDescriptor :=
  { name := "standard_tm_x_only_boundary_route"
    status := StandardTMRouteStatus.theoremUsable
    moduleName := "ComplexityReduction.SAT.CookLevin.TMRootStandard"
    localTargetSymbol := "ComplexityReduction.SAT.standardTMCookLevinTheorem"
    theoremSymbols :=
      [ "ComplexityReduction.SAT.standardTMCookLevinTheorem"
      , "ComplexityReduction.SAT.standardTM_reduction_of_TMVerifier"
      , "ComplexityReduction.SAT.threeSAT_TMNPComplete_with_encodingDiscipline"
      , "ComplexityReduction.SAT.tmVerifierXOnlyEmittedThreeCNFReduction"
      , "ComplexityReduction.SAT.tmCookLevinTheoremOfXOnlyGeneratorPolytime"
      , "ComplexityReduction.SAT.tmVerifierEncodingDisciplineReduction"
      , "ComplexityReduction.SAT.disciplinedStandardTMCookLevinTheorem"
      , "ComplexityReduction.SAT.standardTMCookLevinTheoremOfUniformEncodingDiscipline"
      , "ComplexityReduction.SAT.tmVerifierCertificateSizeBound_tm_polytime"
      , "ComplexityReduction.SAT.tmVerifierXOnlyInputLengthBound_tm_polytime"
      , "ComplexityReduction.SAT.tmVerifierXOnlyTimeBound_tm_polytime"
      , "ComplexityReduction.SAT.tmVerifierXOnlyCellBound_tm_polytime" ]
    supportSymbols :=
      [ "ComplexityReduction.SAT.tmVerifierXOnlyEmittedThreeCNF"
      , "ComplexityReduction.SAT.tmVerifierXOnlyTableauTimeRange_tm_polytime"
      , "ComplexityReduction.SAT.tmVerifierXOnlyTransitionTimeRange_tm_polytime"
      , "ComplexityReduction.SAT.tmVerifierXOnlyCellRange_tm_polytime"
      , "ComplexityReduction.SAT.TMVerifierEncodingDiscipline"
      , "ComplexityReduction.SAT.TMVerifierEncodingDiscipline.ofCheckedSuffixDecoder"
      , "ComplexityReduction.SAT.TMVerifierEncodingDiscipline.ofFiniteBoolCertificate"
      , "ComplexityReduction.SAT.TMVerifierEncodingDiscipline.ofBoolListCertificate"
      , "ComplexityReduction.SAT.TMVerifierEncodingDiscipline.ofNatListCertificate"
      , "ComplexityReduction.SAT.TMVerifierEncodingDiscipline.ofFinListCertificate"
      , "ComplexityReduction.SAT.TMVerifierEncodingDiscipline.ofAssignmentCertificate"
      , "ComplexityReduction.SAT.TMVerifierEncodingDiscipline.ofSubsetCertificate"
      , "ComplexityReduction.SAT.TMVerifierEncodingDiscipline.ofOrderingCertificate"
      , "ComplexityReduction.SAT.TMVerifierEncodingDiscipline.toCheckedSuffixValidity"
      , "ComplexityReduction.SAT.UniformTMVerifierEncodingDiscipline"
      , "ComplexityReduction.SAT.uniformCheckedSuffixValidityOfEncodingDiscipline"
      , "ComplexityReduction.SAT.DisciplinedTMCookLevinTheorem"
      , "ComplexityReduction.SAT.DisciplinedTMCookLevinTheorem.reduction_of_TMVerifier"
      , "ComplexityReduction.SAT.TMInNPWithEncodingDiscipline"
      , "ComplexityReduction.SAT.TMInNPWithEncodingDiscipline.toTMInNP"
      , "ComplexityReduction.SAT.TMNPCompleteEncWithEncodingDiscipline"
      , "ComplexityReduction.SAT.TMNPCompleteEncWithEncodingDiscipline.mem_np"
      , "ComplexityReduction.SAT.TMNPCompleteEncWithEncodingDiscipline.hard"
      , "ComplexityReduction.SAT.TMNPCompleteEncWithEncodingDiscipline.transfer"
      , "ComplexityReduction.SAT.liftNPCompleteAlongReductionWithEncodingDiscipline"
      , "ComplexityReduction.SAT.transferTMNPCompleteWithEncodingDiscipline" ]
    generatorMayUseAsTheorem := true
    requiredPremises :=
      [ "A `TMVerifierEncodingDiscipline V` for the concrete verifier being reduced."
      , "Or `UniformTMVerifierEncodingDiscipline` for the current arbitrary-verifier root surface."
      , "The ordinary arbitrary-`TMVerifier` surface still requires the uniform discipline premise." ]
    roles := ["cook_levin", "standard_tm", "x_only", "theorem_usable", "encoding_discipline"]
    notes :=
      [ "The disciplined root is theorem-bearing for verifiers carrying checked suffix discipline."
      , "Generated proofs may cite the disciplined theorem only with its explicit encoding-discipline premise."
      , "Do not cite the uniform arbitrary-verifier adapter without `UniformTMVerifierEncodingDiscipline`." ] }

/-- Standard-TM Cook-Levin route descriptors exposed to planners. -/
def standardTMRoutes : List StandardTMRouteDescriptor :=
  [ standardTMActiveSymbolRoute
  , standardTMControlBlockRoute
  , standardTMStackBlockRoute
  , standardTMTransitionWindowRoute
  , standardTMCheckedSuffixGeneratorRoute
  , standardTMXOnlyBoundaryRoute
  ]

theorem standardTMRoutes_length :
    standardTMRoutes.length = 6 :=
  rfl

theorem standardTMActiveSymbolRoute_usable :
    standardTMActiveSymbolRoute.generatorMayUseAsTheorem = true :=
  rfl

theorem standardTMControlBlockRoute_usable :
    standardTMControlBlockRoute.generatorMayUseAsTheorem = true :=
  rfl

theorem standardTMStackBlockRoute_usable :
    standardTMStackBlockRoute.generatorMayUseAsTheorem = true :=
  rfl

theorem standardTMTransitionWindowRoute_usable :
    standardTMTransitionWindowRoute.generatorMayUseAsTheorem = true :=
  rfl

theorem standardTMCheckedSuffixGeneratorRoute_not_root_direct :
    standardTMCheckedSuffixGeneratorRoute.generatorMayUseAsTheorem = false :=
  rfl

theorem standardTMXOnlyBoundaryRoute_usable :
    standardTMXOnlyBoundaryRoute.generatorMayUseAsTheorem = true :=
  rfl

#check StandardTMRouteStatus
#check StandardTMRouteStatus.label
#check StandardTMRouteDescriptor
#check standardTMRoutes
#check standardTMRoutes_length
#check standardTMActiveSymbolRoute_usable
#check standardTMControlBlockRoute_usable
#check standardTMStackBlockRoute_usable
#check standardTMTransitionWindowRoute_usable
#check standardTMCheckedSuffixGeneratorRoute_not_root_direct
#check standardTMXOnlyBoundaryRoute_usable
#check SAT.TMVerifierXOnlyCheckedSuffixGeneratorDescriptor
#check SAT.TMVerifierXOnlyCheckedSuffixGeneratorDescriptor.generatorMayUseAsRootTheorem
#check SAT.checkedSuffixGeneratorDescriptor_not_root_theorem
#check SAT.tmVerifierCheckedSuffixAtom_tm_polytime
#check SAT.tmVerifierCheckedSuffixClause_tm_polytime
#check SAT.tmVerifierCheckedSuffixCNF_tm_polytime
#check SAT.tmVerifierXOnlyCheckedSuffixValidityOfGenerator
#check SAT.TMVerifierStackSymbol
#check SAT.TMVerifierNamedStackSymbol
#check SAT.tmVerifierStackSymbolActive_input
#check SAT.tmVerifierStackSymbolActive_output
#check SAT.tmVerifierPushSymbolsFor_mem
#check SAT.tmVerifierStmtPushSymbols_push_mem
#check SAT.tmVerifierControlPushSymbols_label_mem
#check SAT.tmVerifierUnitCNF_satisfies
#check SAT.tmVerifierFrameForwardClause_satisfies
#check SAT.tmVerifierStackActionCNFBetween_satisfies_effect_cnf
#check SAT.tmVerifierStackActionReadCNFAt_satisfies
#check SAT.tmVerifierStackActionCNFBetween_satisfies_read
#check SAT.tmVerifierImplicationClause_satisfies_of_antecedents
#check SAT.tmVerifierWindowControlCNFAt_satisfies_next_control
#check SAT.tmVerifierStmtWindowsAt_actions_readChoiceMem
#check SAT.tmVerifierStmtWindowsAt_actions_pushSymbolMem_of_stmt
#check SAT.tmVerifierStmtWindowsAt_goto_mem
#check SAT.tmVerifierStmtWindowsAt_halt_mem
#check SAT.tmVerifierStmtWindowsAt_push_action_mem
#check SAT.tmVerifierXOnlyEmittedThreeCNFReduction
#check SAT.tmCookLevinTheoremOfXOnlyGeneratorPolytime
#check SAT.tmVerifierEncodingDisciplineReduction
#check SAT.standardTMCookLevinTheorem
#check SAT.standardTM_reduction_of_TMVerifier
#check SAT.threeSAT_TMNPComplete_with_encodingDiscipline
#check SAT.TMVerifierEncodingDiscipline
#check SAT.TMVerifierEncodingDiscipline.ofCheckedSuffixDecoder
#check SAT.TMVerifierEncodingDiscipline.ofFiniteBoolCertificate
#check SAT.TMVerifierEncodingDiscipline.ofBoolListCertificate
#check SAT.TMVerifierEncodingDiscipline.ofNatListCertificate
#check SAT.TMVerifierEncodingDiscipline.ofFinListCertificate
#check SAT.TMVerifierEncodingDiscipline.ofAssignmentCertificate
#check SAT.TMVerifierEncodingDiscipline.ofSubsetCertificate
#check SAT.TMVerifierEncodingDiscipline.ofOrderingCertificate
#check SAT.TMVerifierEncodingDiscipline.toCheckedSuffixValidity
#check SAT.UniformTMVerifierEncodingDiscipline
#check SAT.uniformCheckedSuffixValidityOfEncodingDiscipline
#check SAT.DisciplinedTMCookLevinTheorem
#check SAT.DisciplinedTMCookLevinTheorem.reduction_of_TMVerifier
#check SAT.disciplinedStandardTMCookLevinTheorem
#check SAT.standardTMCookLevinTheoremOfUniformEncodingDiscipline
#check SAT.TMInNPWithEncodingDiscipline
#check SAT.TMInNPWithEncodingDiscipline.toTMInNP
#check SAT.TMNPCompleteEncWithEncodingDiscipline
#check SAT.TMNPCompleteEncWithEncodingDiscipline.mem_np
#check SAT.TMNPCompleteEncWithEncodingDiscipline.hard
#check SAT.TMNPCompleteEncWithEncodingDiscipline.transfer
#check SAT.liftNPCompleteAlongReductionWithEncodingDiscipline
#check SAT.transferTMNPCompleteWithEncodingDiscipline
#check SAT.tmVerifierCertificateSizeBound_tm_polytime
#check SAT.tmVerifierXOnlyInputLengthBound_tm_polytime
#check SAT.tmVerifierXOnlyTimeBound_tm_polytime
#check SAT.tmVerifierXOnlyCellBound_tm_polytime

end TableauCSP
end CookLevin
end SAT
end ComplexityReduction
