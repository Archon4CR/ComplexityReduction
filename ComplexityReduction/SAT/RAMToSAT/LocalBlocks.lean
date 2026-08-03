/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.SAT.RAMToSAT.Descriptor
import ComplexityReduction.SAT.CookLevin.WindowGrid

/-!
Local RAM-to-SAT block metadata with checkable record bounds.

This module follows the descriptor-only boundary of `RAMToSAT.Descriptor`.
It records finite bit-field layouts and local block names that can later be
connected to Cook-Levin `WindowGridDescriptor`s.  It intentionally does not
assert RAM transition correctness, memory sorting correctness, a SAT
satisfiability equivalence, or any asymptotic RAM-to-SAT size theorem.
-/

namespace ComplexityReduction
namespace SAT
namespace RAMToSAT

/-- One named bit field inside a finite record. -/
structure BitField where
  name : String
  offset : Nat
  width : Nat
  notes : List String := []
  deriving Repr

namespace BitField

/-- One-past-the-end offset of a bit field. -/
def endOffset (F : BitField) : Nat :=
  F.offset + F.width

theorem offset_le_endOffset (F : BitField) :
    F.offset ≤ F.endOffset := by
  simp [endOffset]

theorem width_le_endOffset (F : BitField) :
    F.width ≤ F.endOffset := by
  simp [endOffset]

end BitField

/-- A finite bit-record layout with a proof that each stored field fits. -/
structure RecordLayout where
  name : String
  fields : List BitField
  recordBits : Nat
  fieldsWithinRecord : ∀ F, F ∈ fields → F.endOffset ≤ recordBits
  notes : List String := []

namespace RecordLayout

/-- Stable planner-facing field names. -/
def fieldNames (R : RecordLayout) : List String :=
  R.fields.map BitField.name

/-- The end offset of every listed field is bounded by the record width. -/
theorem fieldEndOffset_le_recordBits (R : RecordLayout) {F : BitField}
    (hF : F ∈ R.fields) :
    F.endOffset ≤ R.recordBits :=
  R.fieldsWithinRecord F hF

/-- Every listed field offset is bounded by the record width. -/
theorem fieldOffset_le_recordBits (R : RecordLayout) {F : BitField}
    (hF : F ∈ R.fields) :
    F.offset ≤ R.recordBits := by
  have hEnd := R.fieldEndOffset_le_recordBits hF
  have hOffset : F.offset ≤ F.endOffset := F.offset_le_endOffset
  omega

/-- Every positive-width listed field begins strictly before the record end. -/
theorem fieldOffset_lt_recordBits (R : RecordLayout) {F : BitField}
    (hF : F ∈ R.fields) (hWidth : 0 < F.width) :
    F.offset < R.recordBits := by
  have hEnd := R.fieldEndOffset_le_recordBits hF
  simp [BitField.endOffset] at hEnd
  omega

/-- Every listed field has width at most the enclosing record width. -/
theorem fieldWidth_le_recordBits (R : RecordLayout) {F : BitField}
    (hF : F ∈ R.fields) :
    F.width ≤ R.recordBits := by
  have hEnd := R.fieldEndOffset_le_recordBits hF
  simp [BitField.endOffset] at hEnd
  omega

end RecordLayout

/-- Top-level wrapper for generated proofs that use record-layout fields. -/
theorem fieldOffset_lt_recordBits (R : RecordLayout) {F : BitField}
    (hF : F ∈ R.fields) (hWidth : 0 < F.width) :
    F.offset < R.recordBits :=
  R.fieldOffset_lt_recordBits hF hWidth

/-- Top-level wrapper for generated proofs that use record-layout fields. -/
theorem fieldWidth_le_recordBits (R : RecordLayout) {F : BitField}
    (hF : F ∈ R.fields) :
    F.width ≤ R.recordBits :=
  R.fieldWidth_le_recordBits hF

/-- Program-counter field induced by a `ConfigurationDescriptor`. -/
def configurationProgramCounterField (C : ConfigurationDescriptor) : BitField :=
  { name := "program_counter"
    offset := 0
    width := C.programCounterBits }

/-- Register block field induced by a `ConfigurationDescriptor`. -/
def configurationRegistersField (C : ConfigurationDescriptor) : BitField :=
  { name := "registers"
    offset := C.programCounterBits
    width := C.registerBits }

/-- Memory-address field induced by a `ConfigurationDescriptor`. -/
def configurationMemoryAddressField (C : ConfigurationDescriptor) : BitField :=
  { name := "memory_address"
    offset := C.programCounterBits + C.registerBits
    width := C.memoryAddressBits }

/-- Memory-value field induced by a `ConfigurationDescriptor`. -/
def configurationMemoryValueField (C : ConfigurationDescriptor) : BitField :=
  { name := "memory_value"
    offset := C.programCounterBits + C.registerBits + C.memoryAddressBits
    width := C.memoryValueBits }

/-- Flag field induced by a `ConfigurationDescriptor`. -/
def configurationFlagsField (C : ConfigurationDescriptor) : BitField :=
  { name := "flags"
    offset :=
      C.programCounterBits + C.registerBits + C.memoryAddressBits + C.memoryValueBits
    width := C.flagBits }

/-- Canonical ordered fields of a configuration record descriptor. -/
def configurationFields (C : ConfigurationDescriptor) : List BitField :=
  [ configurationProgramCounterField C
  , configurationRegistersField C
  , configurationMemoryAddressField C
  , configurationMemoryValueField C
  , configurationFlagsField C ]

/-- Canonical record layout induced by a `ConfigurationDescriptor`. -/
def configurationRecordLayout (C : ConfigurationDescriptor) : RecordLayout where
  name := "configuration_record"
  fields := configurationFields C
  recordBits := C.bitWidth
  fieldsWithinRecord := by
    intro F hF
    simp [configurationFields] at hF
    rcases hF with rfl | rfl | rfl | rfl | rfl <;>
      simp [BitField.endOffset, configurationProgramCounterField,
        configurationRegistersField, configurationMemoryAddressField,
        configurationMemoryValueField, configurationFlagsField,
        ConfigurationDescriptor.bitWidth] <;>
      omega
  notes := ["Canonical cumulative layout induced by a configuration descriptor."]

/-- Checkable bit-field layout for a RAM configuration record. -/
structure ConfigurationLayout where
  record : RecordLayout
  programCounter : BitField
  registers : BitField
  memoryAddress : BitField
  memoryValue : BitField
  flags : BitField
  fields_eq :
    record.fields = [programCounter, registers, memoryAddress, memoryValue, flags]
  recordBits_eq :
    record.recordBits =
      programCounter.width + registers.width + memoryAddress.width + memoryValue.width +
        flags.width

namespace ConfigurationLayout

/-- Total width of the configuration record. -/
def bitWidth (C : ConfigurationLayout) : Nat :=
  C.record.recordBits

/-- Canonical layout induced by a descriptor-only configuration record. -/
def ofDescriptor (C : ConfigurationDescriptor) : ConfigurationLayout where
  record := configurationRecordLayout C
  programCounter := configurationProgramCounterField C
  registers := configurationRegistersField C
  memoryAddress := configurationMemoryAddressField C
  memoryValue := configurationMemoryValueField C
  flags := configurationFlagsField C
  fields_eq := rfl
  recordBits_eq := by
    simp [configurationRecordLayout, configurationProgramCounterField,
      configurationRegistersField, configurationMemoryAddressField,
      configurationMemoryValueField, configurationFlagsField,
      ConfigurationDescriptor.bitWidth]

/-- The configuration bit width is exactly the sum of its named field widths. -/
theorem bitWidth_eq (C : ConfigurationLayout) :
    C.bitWidth =
      C.programCounter.width + C.registers.width + C.memoryAddress.width +
        C.memoryValue.width + C.flags.width := by
  rw [bitWidth, C.recordBits_eq]

theorem programCounter_mem (C : ConfigurationLayout) :
    C.programCounter ∈ C.record.fields := by
  rw [C.fields_eq]
  simp

theorem registers_mem (C : ConfigurationLayout) :
    C.registers ∈ C.record.fields := by
  rw [C.fields_eq]
  simp

theorem memoryAddress_mem (C : ConfigurationLayout) :
    C.memoryAddress ∈ C.record.fields := by
  rw [C.fields_eq]
  simp

theorem memoryValue_mem (C : ConfigurationLayout) :
    C.memoryValue ∈ C.record.fields := by
  rw [C.fields_eq]
  simp

theorem flags_mem (C : ConfigurationLayout) :
    C.flags ∈ C.record.fields := by
  rw [C.fields_eq]
  simp

end ConfigurationLayout

/-- Top-level wrapper for the configuration bit-width identity. -/
theorem configurationLayout_bitWidth_eq (C : ConfigurationLayout) :
    C.bitWidth =
      C.programCounter.width + C.registers.width + C.memoryAddress.width +
        C.memoryValue.width + C.flags.width :=
  C.bitWidth_eq

/-- Time field induced by a `MemoryAccessDescriptor`. -/
def memoryAccessTimeField (M : MemoryAccessDescriptor) : BitField :=
  { name := "time"
    offset := 0
    width := M.timeBits }

/-- Address field induced by a `MemoryAccessDescriptor`. -/
def memoryAccessAddressField (M : MemoryAccessDescriptor) : BitField :=
  { name := "address"
    offset := M.timeBits
    width := M.addressBits }

/-- Value field induced by a `MemoryAccessDescriptor`. -/
def memoryAccessValueField (M : MemoryAccessDescriptor) : BitField :=
  { name := "value"
    offset := M.timeBits + M.addressBits
    width := M.valueBits }

/-- Write-flag field induced by a `MemoryAccessDescriptor`. -/
def memoryAccessWriteFlagField (M : MemoryAccessDescriptor) : BitField :=
  { name := "write_flag"
    offset := M.timeBits + M.addressBits + M.valueBits
    width := M.writeFlagBits }

/-- Canonical ordered fields of a memory-access record descriptor. -/
def memoryAccessFields (M : MemoryAccessDescriptor) : List BitField :=
  [ memoryAccessTimeField M
  , memoryAccessAddressField M
  , memoryAccessValueField M
  , memoryAccessWriteFlagField M ]

/-- Canonical record layout induced by a `MemoryAccessDescriptor`. -/
def memoryAccessRecordLayout (M : MemoryAccessDescriptor) : RecordLayout where
  name := "memory_access_record"
  fields := memoryAccessFields M
  recordBits := M.recordBits
  fieldsWithinRecord := by
    intro F hF
    simp [memoryAccessFields] at hF
    rcases hF with rfl | rfl | rfl | rfl <;>
      simp [BitField.endOffset, memoryAccessTimeField, memoryAccessAddressField,
        memoryAccessValueField, memoryAccessWriteFlagField,
        MemoryAccessDescriptor.recordBits] <;>
      omega
  notes := ["Canonical cumulative layout induced by a memory-access descriptor."]

/-- Checkable bit-field layout for one RAM memory-access record. -/
structure MemoryAccessLayout where
  record : RecordLayout
  time : BitField
  address : BitField
  value : BitField
  writeFlag : BitField
  fields_eq : record.fields = [time, address, value, writeFlag]
  recordBits_eq : record.recordBits = time.width + address.width + value.width + writeFlag.width

namespace MemoryAccessLayout

/-- Total width of the memory-access record. -/
def recordBits (M : MemoryAccessLayout) : Nat :=
  M.record.recordBits

/-- Canonical layout induced by a descriptor-only memory-access record. -/
def ofDescriptor (M : MemoryAccessDescriptor) : MemoryAccessLayout where
  record := memoryAccessRecordLayout M
  time := memoryAccessTimeField M
  address := memoryAccessAddressField M
  value := memoryAccessValueField M
  writeFlag := memoryAccessWriteFlagField M
  fields_eq := rfl
  recordBits_eq := by
    simp [memoryAccessRecordLayout, memoryAccessTimeField, memoryAccessAddressField,
      memoryAccessValueField, memoryAccessWriteFlagField,
      MemoryAccessDescriptor.recordBits]

/-- The memory-access record width is exactly the sum of its named field widths. -/
theorem recordBits_eq_sum (M : MemoryAccessLayout) :
    M.recordBits = M.time.width + M.address.width + M.value.width + M.writeFlag.width := by
  rw [recordBits, M.recordBits_eq]

theorem time_mem (M : MemoryAccessLayout) :
    M.time ∈ M.record.fields := by
  rw [M.fields_eq]
  simp

theorem address_mem (M : MemoryAccessLayout) :
    M.address ∈ M.record.fields := by
  rw [M.fields_eq]
  simp

theorem value_mem (M : MemoryAccessLayout) :
    M.value ∈ M.record.fields := by
  rw [M.fields_eq]
  simp

theorem writeFlag_mem (M : MemoryAccessLayout) :
    M.writeFlag ∈ M.record.fields := by
  rw [M.fields_eq]
  simp

end MemoryAccessLayout

/-- Top-level wrapper for the memory-access record-width identity. -/
theorem memoryAccessLayout_recordBits_eq (M : MemoryAccessLayout) :
    M.recordBits = M.time.width + M.address.width + M.value.width + M.writeFlag.width :=
  M.recordBits_eq_sum

/-- Metadata for a local adjacent-configuration RAM block. -/
structure AdjacentConfigurationBlock where
  name : String
  before : ConfigurationLayout
  after : ConfigurationLayout
  timeCount : Nat
  cellCount : Nat
  payloadCount : Nat
  predicateSymbol : String
  theoremSymbol : Option String := none
  status : RouteStatus := RouteStatus.metadataOnly
  notes : List String := []

namespace AdjacentConfigurationBlock

/-- Total record input width read by an adjacent-configuration predicate. -/
def inputBits (B : AdjacentConfigurationBlock) : Nat :=
  B.before.bitWidth + B.after.bitWidth

/-- Local RAM blocks remain metadata and are not theorem-eligible. -/
def generatorMayUseAsTheorem (B : AdjacentConfigurationBlock) : Bool :=
  B.status.generatorMayUseAsTheorem

@[simp]
theorem generatorMayUseAsTheorem_eq_false (B : AdjacentConfigurationBlock) :
    B.generatorMayUseAsTheorem = false := by
  cases h : B.status <;>
    simp [generatorMayUseAsTheorem, RouteStatus.generatorMayUseAsTheorem, h]

theorem before_bitWidth_le_inputBits (B : AdjacentConfigurationBlock) :
    B.before.bitWidth ≤ B.inputBits := by
  simp [inputBits]

theorem after_bitWidth_le_inputBits (B : AdjacentConfigurationBlock) :
    B.after.bitWidth ≤ B.inputBits := by
  simp [inputBits]

end AdjacentConfigurationBlock

/-- Metadata for the memory-access sort-key block used by RAM-to-SAT encodings. -/
structure MemorySortKeyBlock where
  name : String
  access : MemoryAccessLayout
  timeCount : Nat
  cellCount : Nat
  payloadCount : Nat
  keySymbol : String
  theoremSymbol : Option String := none
  status : RouteStatus := RouteStatus.metadataOnly
  notes : List String := []

namespace MemorySortKeyBlock

/-- Width of the syntactic time/address sort key. -/
def sortKeyBits (B : MemorySortKeyBlock) : Nat :=
  B.access.time.width + B.access.address.width

/-- Memory sort-key blocks remain metadata and are not theorem-eligible. -/
def generatorMayUseAsTheorem (B : MemorySortKeyBlock) : Bool :=
  B.status.generatorMayUseAsTheorem

@[simp]
theorem generatorMayUseAsTheorem_eq_false (B : MemorySortKeyBlock) :
    B.generatorMayUseAsTheorem = false := by
  cases h : B.status <;>
    simp [generatorMayUseAsTheorem, RouteStatus.generatorMayUseAsTheorem, h]

/-- The time/address sort key is no wider than the whole memory-access record. -/
theorem sortKeyBits_le_recordBits (B : MemorySortKeyBlock) :
    B.sortKeyBits ≤ B.access.recordBits := by
  rw [sortKeyBits, memoryAccessLayout_recordBits_eq]
  omega

end MemorySortKeyBlock

/-- Planner metadata anchoring RAM local blocks to the Cook-Levin window-grid surface. -/
structure WindowGridMetadata where
  timeCount : Nat
  cellCount : Nat
  payloadCount : Nat
  windowCount : Nat
  windowGridDescriptorSymbol : String
  sourceBlocks : List String := []
  status : RouteStatus := RouteStatus.metadataOnly
  notes : List String := []
  deriving Repr

namespace WindowGridMetadata

/-- Window-grid metadata remains non-theorem-eligible. -/
def generatorMayUseAsTheorem (G : WindowGridMetadata) : Bool :=
  G.status.generatorMayUseAsTheorem

@[simp]
theorem generatorMayUseAsTheorem_eq_false (G : WindowGridMetadata) :
    G.generatorMayUseAsTheorem = false := by
  cases h : G.status <;>
    simp [generatorMayUseAsTheorem, RouteStatus.generatorMayUseAsTheorem, h]

end WindowGridMetadata

/--
Turn RAM local block metadata into conservative Cook-Levin window-grid bounds.
This is only a metadata bridge; it does not build local predicates and does not
state a RAM-to-SAT correctness theorem.
-/
def toWindowGridMetadata (A : AdjacentConfigurationBlock) (M : MemorySortKeyBlock) :
    WindowGridMetadata :=
  { timeCount := max A.timeCount M.timeCount
    cellCount := max A.cellCount M.cellCount
    payloadCount := max A.payloadCount M.payloadCount
    windowCount := 2
    windowGridDescriptorSymbol :=
      "ComplexityReduction.SAT.CookLevin.TableauCSP.WindowGridDescriptor"
    sourceBlocks := [A.name, M.name]
    status := RouteStatus.metadataOnly
    notes :=
      [ "Conservative metadata bridge from RAM local blocks to Cook-Levin window grids."
      , "No local predicate list or RAM correctness theorem is asserted." ] }

theorem adjacent_timeCount_le_toWindowGridMetadata
    (A : AdjacentConfigurationBlock) (M : MemorySortKeyBlock) :
    A.timeCount ≤ (toWindowGridMetadata A M).timeCount := by
  simp [toWindowGridMetadata]

theorem sortKey_timeCount_le_toWindowGridMetadata
    (A : AdjacentConfigurationBlock) (M : MemorySortKeyBlock) :
    M.timeCount ≤ (toWindowGridMetadata A M).timeCount := by
  simp [toWindowGridMetadata]

theorem toWindowGridMetadata_not_theorem
    (A : AdjacentConfigurationBlock) (M : MemorySortKeyBlock) :
    (toWindowGridMetadata A M).generatorMayUseAsTheorem = false :=
  rfl

/-- Canonical metadata-only configuration layout used by the mounted route. -/
def metadataOnlyConfigurationLayout : ConfigurationLayout :=
  ConfigurationLayout.ofDescriptor metadataOnlyConfiguration

/-- Canonical metadata-only memory-access layout used by the mounted route. -/
def metadataOnlyMemoryAccessLayout : MemoryAccessLayout :=
  MemoryAccessLayout.ofDescriptor metadataOnlyMemoryAccess

/-- Metadata-only adjacent-configuration block corresponding to the descriptor route. -/
def metadataOnlyAdjacentConfigurationBlock : AdjacentConfigurationBlock :=
  { name := "metadata_only_adjacent_configuration_block"
    before := metadataOnlyConfigurationLayout
    after := metadataOnlyConfigurationLayout
    timeCount := 0
    cellCount := 0
    payloadCount := 0
    predicateSymbol := "future RAM adjacent-configuration predicate"
    theoremSymbol := none
    status := RouteStatus.metadataOnly
    notes :=
      [ "Use as metadata only until a local adjacent-configuration proof is added." ] }

/-- Metadata-only memory sort-key block corresponding to the descriptor route. -/
def metadataOnlyMemorySortKeyBlock : MemorySortKeyBlock :=
  { name := "metadata_only_memory_sort_key_block"
    access := metadataOnlyMemoryAccessLayout
    timeCount := 0
    cellCount := 0
    payloadCount := 0
    keySymbol := "future RAM memory-access sort key"
    theoremSymbol := none
    status := RouteStatus.metadataOnly
    notes := ["Use as metadata only until sorted-memory consistency is formalized."] }

/-- Metadata-only window-grid anchor produced from the two local RAM blocks. -/
def metadataOnlyWindowGridMetadata : WindowGridMetadata :=
  toWindowGridMetadata metadataOnlyAdjacentConfigurationBlock metadataOnlyMemorySortKeyBlock

/-- Descriptor view of the adjacent-configuration local-block metadata. -/
def localBlockAdjacentConfigCheckDescriptor : AdjacentConfigCheckDescriptor :=
  { name := metadataOnlyAdjacentConfigurationBlock.name
    configBits := metadataOnlyAdjacentConfigurationBlock.inputBits
    predicateSymbol := metadataOnlyAdjacentConfigurationBlock.predicateSymbol
    theoremSymbol := none
    status := RouteStatus.metadataOnly
    notes := metadataOnlyAdjacentConfigurationBlock.notes }

/-- Descriptor view of the memory sort-key local-block metadata. -/
def localBlockSortingConsistencyDescriptor : SortingConsistencyDescriptor :=
  { name := metadataOnlyMemorySortKeyBlock.name
    accessRecordBits := metadataOnlyMemoryAccessLayout.recordBits
    sortKeySymbol := metadataOnlyMemorySortKeyBlock.keySymbol
    theoremSymbol := none
    status := RouteStatus.metadataOnly
    notes := metadataOnlyMemorySortKeyBlock.notes }

/-- Metadata-only RAM-to-SAT route that advertises the local block surfaces. -/
def localBlockMetadataRoute : RouteDescriptor :=
  { metadataOnlyRoute with
    name := "ram_to_sat_local_blocks_metadata_only"
    adjacentConfigCheck := localBlockAdjacentConfigCheckDescriptor
    sortingConsistency := localBlockSortingConsistencyDescriptor
    localPredicateFamilySymbol :=
      some "ComplexityReduction.SAT.CookLevin.TableauCSP.WindowGridDescriptor"
    correctnessTheorem := none
    roles := ["ram_to_sat", "local_blocks", "window_grid_anchor", "metadata_only"]
    notes :=
      [ "Records finite local RAM block layouts and checkable record bounds."
      , "Generated proofs must not cite this as RAM-to-SAT correctness." ] }

@[simp]
theorem localBlockMetadataRoute_not_theorem :
    localBlockMetadataRoute.generatorMayUseAsTheorem = false :=
  rfl

/-- Local-block route metadata catalog. -/
def localBlockRoutes : List RouteDescriptor :=
  [localBlockMetadataRoute]

@[simp]
theorem localBlockRoutes_length :
    localBlockRoutes.length = 1 :=
  rfl

/-- Every currently mounted local-block RAM-to-SAT route is metadata-only. -/
theorem localBlockRoutes_not_theorem {R : RouteDescriptor} (hR : R ∈ localBlockRoutes) :
    R.generatorMayUseAsTheorem = false := by
  simp [localBlockRoutes] at hR
  rcases hR with rfl
  rfl

end RAMToSAT
end SAT
end ComplexityReduction
