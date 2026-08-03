/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic

/-!
Descriptor-only RAM-to-SAT route metadata.

This module records the finite fields and route status vocabulary needed by the
planner to talk about RAM-to-SAT constructions.  It intentionally does not
assert a RAM computation iff SAT satisfiability theorem or any asymptotic
Robson/Viola bound.
-/

namespace ComplexityReduction
namespace SAT
namespace RAMToSAT

/-- Trust status for RAM-to-SAT route metadata. -/
inductive RouteStatus where
  | metadataOnly
  | sourceGated
  | blocked
  deriving DecidableEq, Repr

namespace RouteStatus

/-- Stable route-status label for generated artifacts and source maps. -/
def label : RouteStatus → String
  | metadataOnly => "metadata_only"
  | sourceGated => "source_gated"
  | blocked => "blocked"

/-- RAM-to-SAT descriptors in this module are not theorem-eligible. -/
def generatorMayUseAsTheorem : RouteStatus → Bool
  | metadataOnly => false
  | sourceGated => false
  | blocked => false

/-- Metadata-only RAM-to-SAT routes are not local correctness theorems. -/
@[simp]
theorem metadataOnly_not_theorem :
    generatorMayUseAsTheorem RouteStatus.metadataOnly = false :=
  rfl

@[simp]
theorem sourceGated_not_theorem :
    generatorMayUseAsTheorem RouteStatus.sourceGated = false :=
  rfl

@[simp]
theorem blocked_not_theorem :
    generatorMayUseAsTheorem RouteStatus.blocked = false :=
  rfl

end RouteStatus

/-- Finite RAM model assumptions recorded by a metadata-only route. -/
structure RAMModelDescriptor where
  name : String
  wordBits : Nat
  addressBits : Nat
  registerCount : Nat
  instructionCount : Nat
  memoryCellCount : Nat
  assumptions : List String := []
  roles : List String := []
  notes : List String := []
  deriving Repr

/-- Bit-field layout for one RAM configuration record. -/
structure ConfigurationDescriptor where
  programCounterBits : Nat
  registerBits : Nat
  memoryAddressBits : Nat
  memoryValueBits : Nat
  flagBits : Nat := 0
  deriving Repr

namespace ConfigurationDescriptor

/-- Total bit width of the recorded configuration fields. -/
def bitWidth (C : ConfigurationDescriptor) : Nat :=
  C.programCounterBits + C.registerBits + C.memoryAddressBits + C.memoryValueBits +
    C.flagBits

theorem programCounterBits_le_bitWidth (C : ConfigurationDescriptor) :
    C.programCounterBits ≤ C.bitWidth := by
  dsimp [bitWidth]
  omega

theorem registerBits_le_bitWidth (C : ConfigurationDescriptor) :
    C.registerBits ≤ C.bitWidth := by
  dsimp [bitWidth]
  omega

theorem memoryAddressBits_le_bitWidth (C : ConfigurationDescriptor) :
    C.memoryAddressBits ≤ C.bitWidth := by
  dsimp [bitWidth]
  omega

theorem memoryValueBits_le_bitWidth (C : ConfigurationDescriptor) :
    C.memoryValueBits ≤ C.bitWidth := by
  dsimp [bitWidth]
  omega

end ConfigurationDescriptor

/-- Bit-field layout for one RAM memory-access record. -/
structure MemoryAccessDescriptor where
  timeBits : Nat
  addressBits : Nat
  valueBits : Nat
  writeFlagBits : Nat := 1
  deriving Repr

namespace MemoryAccessDescriptor

/-- Total bit width of the recorded memory-access fields. -/
def recordBits (M : MemoryAccessDescriptor) : Nat :=
  M.timeBits + M.addressBits + M.valueBits + M.writeFlagBits

theorem addressBits_le_recordBits (M : MemoryAccessDescriptor) :
    M.addressBits ≤ M.recordBits := by
  dsimp [recordBits]
  omega

theorem valueBits_le_recordBits (M : MemoryAccessDescriptor) :
    M.valueBits ≤ M.recordBits := by
  dsimp [recordBits]
  omega

end MemoryAccessDescriptor

/-- Descriptor for an adjacent-configuration check block. -/
structure AdjacentConfigCheckDescriptor where
  name : String
  configBits : Nat
  predicateSymbol : String
  theoremSymbol : Option String := none
  status : RouteStatus := RouteStatus.metadataOnly
  notes : List String := []
  deriving Repr

/-- Descriptor for the sorted-memory-access consistency block. -/
structure SortingConsistencyDescriptor where
  name : String
  accessRecordBits : Nat
  sortKeySymbol : String
  theoremSymbol : Option String := none
  status : RouteStatus := RouteStatus.metadataOnly
  notes : List String := []
  deriving Repr

/-- Planner metadata for a RAM-to-SAT route. -/
structure RouteDescriptor where
  name : String
  status : RouteStatus
  model : RAMModelDescriptor
  configuration : ConfigurationDescriptor
  memoryAccess : MemoryAccessDescriptor
  adjacentConfigCheck : AdjacentConfigCheckDescriptor
  sortingConsistency : SortingConsistencyDescriptor
  localPredicateFamilySymbol : Option String := none
  correctnessTheorem : Option String := none
  sourceReferences : List String := []
  roles : List String := []
  notes : List String := []
  deriving Repr

namespace RouteDescriptor

/--
Whether generated proofs may cite this route as a local correctness theorem.
For this descriptor-only layer all statuses currently evaluate to `false`.
-/
def generatorMayUseAsTheorem (R : RouteDescriptor) : Bool :=
  R.status.generatorMayUseAsTheorem

/-- A metadata-only route cannot be used as a theorem by generated proofs. -/
theorem not_theorem_eligible_of_metadataOnly {R : RouteDescriptor}
    (h : R.status = RouteStatus.metadataOnly) :
    R.generatorMayUseAsTheorem = false := by
  cases R
  cases h
  rfl

end RouteDescriptor

/-- Conservative model metadata corresponding to the currently mounted descriptor layer. -/
def metadataOnlyModel : RAMModelDescriptor :=
  { name := "source_gated_uniform_ram_model"
    wordBits := 0
    addressBits := 0
    registerCount := 0
    instructionCount := 0
    memoryCellCount := 0
    assumptions :=
      [ "A concrete RAM syntax, time bound, and encoding are not formalized in this module." ]
    roles := ["ram_to_sat", "metadata_only"]
    notes :=
      [ "Fields are placeholders for future source-backed RAM encodings."
      , "No RAM acceptance or SAT satisfiability theorem is asserted." ] }

/-- Configuration bit layout placeholder for the metadata-only route. -/
def metadataOnlyConfiguration : ConfigurationDescriptor :=
  { programCounterBits := 0
    registerBits := 0
    memoryAddressBits := 0
    memoryValueBits := 0
    flagBits := 0 }

/-- Memory-access record layout placeholder for the metadata-only route. -/
def metadataOnlyMemoryAccess : MemoryAccessDescriptor :=
  { timeBits := 0
    addressBits := 0
    valueBits := 0
    writeFlagBits := 1 }

/-- Adjacent-configuration check placeholder. -/
def metadataOnlyAdjacentConfigCheck : AdjacentConfigCheckDescriptor :=
  { name := "metadata_only_adjacent_configuration_check"
    configBits := metadataOnlyConfiguration.bitWidth
    predicateSymbol := "future RAM adjacent-configuration predicate"
    theoremSymbol := none
    status := RouteStatus.metadataOnly
    notes :=
      [ "Use as route metadata only until a local adjacent-configuration proof is added." ] }

/-- Sorting-consistency check placeholder for memory-access records. -/
def metadataOnlySortingConsistency : SortingConsistencyDescriptor :=
  { name := "metadata_only_memory_access_sorting_consistency"
    accessRecordBits := metadataOnlyMemoryAccess.recordBits
    sortKeySymbol := "future RAM memory-access sort key"
    theoremSymbol := none
    status := RouteStatus.metadataOnly
    notes :=
      [ "Use as route metadata only until a local sorted-memory consistency proof is added." ] }

/-- Metadata-only RAM-to-SAT route descriptor. -/
def metadataOnlyRoute : RouteDescriptor :=
  { name := "ram_to_sat_descriptor_metadata_only"
    status := RouteStatus.metadataOnly
    model := metadataOnlyModel
    configuration := metadataOnlyConfiguration
    memoryAccess := metadataOnlyMemoryAccess
    adjacentConfigCheck := metadataOnlyAdjacentConfigCheck
    sortingConsistency := metadataOnlySortingConsistency
    localPredicateFamilySymbol :=
      some "future ComplexityReduction.SAT.CookLevin.TableauCSP.WindowGridDescriptor"
    correctnessTheorem := none
    sourceReferences :=
      [ "Viola, From RAM to SAT"
      , "Robson 1991 is source-gated and not used as a local theorem here." ]
    roles := ["ram_to_sat", "descriptor", "metadata_only", "source_gated"]
    notes :=
      [ "Descriptor records intended route shape only."
      , "Generated proofs must not cite this as RAM-to-SAT correctness." ] }

/-- The mounted RAM-to-SAT descriptor is not theorem-eligible. -/
@[simp]
theorem metadataOnlyRoute_not_theorem :
    metadataOnlyRoute.generatorMayUseAsTheorem = false :=
  rfl

/-- Public RAM-to-SAT route metadata catalog. -/
def routes : List RouteDescriptor :=
  [metadataOnlyRoute]

/-- There is currently one RAM-to-SAT metadata route. -/
@[simp]
theorem routes_length :
    routes.length = 1 :=
  rfl

/-- Every currently mounted RAM-to-SAT route is metadata-only for proof generation. -/
theorem routes_not_theorem {R : RouteDescriptor} (hR : R ∈ routes) :
    R.generatorMayUseAsTheorem = false := by
  simp [routes] at hR
  rcases hR with rfl
  rfl

end RAMToSAT
end SAT
end ComplexityReduction
