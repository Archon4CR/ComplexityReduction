/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.Tiling.Wang

/-!
Descriptor catalog for Moore-Robson style tiling gadgets.

Moore and Robson's tiling reductions organize local constructions as wires,
gates, splitters, variable starts, true terminals, bends, and phase changes.
This file records that vocabulary as finite Lean metadata with arity and
truth-table shape lemmas.  It deliberately does not assert a concrete tile
palette, per-gadget local tiling correctness, or any global hardness theorem.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace Tiling
namespace MooreRobson

/-- Boolean signal carried by the Moore-Robson descriptor layer. -/
inductive Signal where
  | low
  | high
  deriving DecidableEq, Fintype, Repr

namespace Signal

/-- Interpret a descriptor-level signal as a Boolean value. -/
def toBool : Signal → Bool
  | low => false
  | high => true

/-- Convert a Boolean value to a descriptor-level signal. -/
def ofBool (b : Bool) : Signal :=
  if b then high else low

@[simp]
theorem ofBool_toBool (s : Signal) :
    ofBool s.toBool = s := by
  cases s <;> rfl

@[simp]
theorem toBool_ofBool (b : Bool) :
    (ofBool b).toBool = b := by
  cases b <;> rfl

/-- Signal-level conjunction used by the AND-gate truth-table metadata. -/
def and (a b : Signal) : Signal :=
  ofBool (a.toBool && b.toBool)

/-- Signal-level negation used by the NOT-gate truth-table metadata. -/
def negate (a : Signal) : Signal :=
  ofBool (!a.toBool)

@[simp]
theorem and_low_left (s : Signal) :
    and low s = low := by
  cases s <;> rfl

@[simp]
theorem and_high_left (s : Signal) :
    and high s = s := by
  cases s <;> rfl

@[simp]
theorem negate_low :
    negate low = high :=
  rfl

@[simp]
theorem negate_high :
    negate high = low :=
  rfl

end Signal

/-- Terminal-port role in a local gadget descriptor. -/
inductive PortRole where
  | input
  | output
  deriving DecidableEq, Fintype, Repr

/-- Boundary port of a descriptor-level tiling gadget. -/
structure Port where
  role : PortRole
  index : Nat
  side : Wang.Side
  deriving DecidableEq, Repr

/-- Canonical list of input ports for a descriptor of the given arity. -/
def inputPorts (n : Nat) : List Port :=
  List.ofFn fun i : Fin n =>
    { role := PortRole.input
      index := i.val
      side := Wang.Side.west }

/-- Canonical list of output ports for a descriptor of the given arity. -/
def outputPorts (n : Nat) : List Port :=
  List.ofFn fun i : Fin n =>
    { role := PortRole.output
      index := i.val
      side := Wang.Side.east }

@[simp]
theorem inputPorts_length (n : Nat) :
    (inputPorts n).length = n := by
  simp [inputPorts]

@[simp]
theorem outputPorts_length (n : Nat) :
    (outputPorts n).length = n := by
  simp [outputPorts]

/-- Wire-like Moore-Robson descriptor kinds. -/
inductive WireKind where
  | straight
  | bend
  | phaseChange
  deriving DecidableEq, Fintype, Repr

namespace WireKind

/-- Wire-like descriptors have one input and one output. -/
def terminalCount (_ : WireKind) : Nat :=
  2

/-- Descriptor-level signal relation for a wire-like gadget. -/
def accepts (_ : WireKind) (input output : Signal) : Prop :=
  output = input

@[simp]
theorem terminalCount_eq_two (k : WireKind) :
    k.terminalCount = 2 :=
  rfl

@[simp]
theorem accepts_iff (k : WireKind) (input output : Signal) :
    k.accepts input output ↔ output = input :=
  Iff.rfl

end WireKind

/-- Metadata for one wire-like tiling gadget. -/
structure WireDescriptor where
  kind : WireKind
  name : String
  inputPort : Port
  outputPort : Port
  truthTable : Signal → Signal → Prop
  notes : List String

namespace WireDescriptor

/-- Wire-like descriptors expose two terminal ports. -/
def terminalCount (_ : WireDescriptor) : Nat :=
  2

@[simp]
theorem terminalCount_eq_two (W : WireDescriptor) :
    W.terminalCount = 2 :=
  rfl

end WireDescriptor

/-- Build a wire-like descriptor from a Moore-Robson wire kind. -/
def wireDescriptor (kind : WireKind) (name : String) (notes : List String) :
    WireDescriptor where
  kind := kind
  name := name
  inputPort := { role := PortRole.input, index := 0, side := Wang.Side.west }
  outputPort := { role := PortRole.output, index := 0, side := Wang.Side.east }
  truthTable := kind.accepts
  notes := notes

/-- Straight signal-carrying wire descriptor. -/
def wire : WireDescriptor :=
  wireDescriptor WireKind.straight "wire"
    [ "Straight wire metadata; concrete tile coordinates and palette are supplied by a later layer." ]

/-- Bend descriptor for changing geometric direction while preserving the signal. -/
def bend : WireDescriptor :=
  wireDescriptor WireKind.bend "bend"
    [ "Wire-like bend metadata; this records signal preservation only." ]

/-- Phase-change descriptor for changing tiling phase while preserving the signal. -/
def phaseChange : WireDescriptor :=
  wireDescriptor WireKind.phaseChange "phase_change"
    [ "Wire-like phase-change metadata; this records signal preservation only." ]

@[simp]
theorem wire_truthTable_iff (input output : Signal) :
    wire.truthTable input output ↔ output = input :=
  Iff.rfl

@[simp]
theorem bend_truthTable_iff (input output : Signal) :
    bend.truthTable input output ↔ output = input :=
  Iff.rfl

@[simp]
theorem phaseChange_truthTable_iff (input output : Signal) :
    phaseChange.truthTable input output ↔ output = input :=
  Iff.rfl

/-- Gate-like Moore-Robson descriptor kinds. -/
inductive GateKind where
  | andGate
  | notGate
  | splitter
  | variableStart
  | trueTerminal
  deriving DecidableEq, Fintype, Repr

namespace GateKind

/-- Number of input signal terminals for a gate kind. -/
def inputArity : GateKind → Nat
  | andGate => 2
  | notGate => 1
  | splitter => 1
  | variableStart => 0
  | trueTerminal => 1

/-- Number of output signal terminals for a gate kind. -/
def outputArity : GateKind → Nat
  | andGate => 1
  | notGate => 1
  | splitter => 2
  | variableStart => 1
  | trueTerminal => 0

/-- Total number of boundary signal terminals for a gate kind. -/
def terminalCount (kind : GateKind) : Nat :=
  kind.inputArity + kind.outputArity

/-- Descriptor-level truth table for a gate kind. -/
def accepts : (kind : GateKind) →
    (Fin kind.inputArity → Signal) → (Fin kind.outputArity → Signal) → Prop
  | andGate, inputs, outputs =>
      outputs (0 : Fin 1) = Signal.and (inputs (0 : Fin 2)) (inputs (1 : Fin 2))
  | notGate, inputs, outputs =>
      outputs (0 : Fin 1) = Signal.negate (inputs (0 : Fin 1))
  | splitter, inputs, outputs =>
      outputs (0 : Fin 2) = inputs (0 : Fin 1) ∧
        outputs (1 : Fin 2) = inputs (0 : Fin 1)
  | variableStart, _, _ =>
      True
  | trueTerminal, inputs, _ =>
      inputs (0 : Fin 1) = Signal.high

@[simp]
theorem andGate_inputArity :
    GateKind.andGate.inputArity = 2 :=
  rfl

@[simp]
theorem andGate_outputArity :
    GateKind.andGate.outputArity = 1 :=
  rfl

@[simp]
theorem notGate_inputArity :
    GateKind.notGate.inputArity = 1 :=
  rfl

@[simp]
theorem notGate_outputArity :
    GateKind.notGate.outputArity = 1 :=
  rfl

@[simp]
theorem splitter_inputArity :
    GateKind.splitter.inputArity = 1 :=
  rfl

@[simp]
theorem splitter_outputArity :
    GateKind.splitter.outputArity = 2 :=
  rfl

@[simp]
theorem variableStart_inputArity :
    GateKind.variableStart.inputArity = 0 :=
  rfl

@[simp]
theorem variableStart_outputArity :
    GateKind.variableStart.outputArity = 1 :=
  rfl

@[simp]
theorem trueTerminal_inputArity :
    GateKind.trueTerminal.inputArity = 1 :=
  rfl

@[simp]
theorem trueTerminal_outputArity :
    GateKind.trueTerminal.outputArity = 0 :=
  rfl

end GateKind

/-- Metadata for one gate-like Moore-Robson tiling gadget. -/
structure GateDescriptor where
  kind : GateKind
  name : String
  inputPorts : List Port
  outputPorts : List Port
  inputPorts_length : inputPorts.length = kind.inputArity
  outputPorts_length : outputPorts.length = kind.outputArity
  truthTable : (Fin kind.inputArity → Signal) → (Fin kind.outputArity → Signal) → Prop
  notes : List String

namespace GateDescriptor

/-- Declared input arity of a gate descriptor. -/
def inputArity (G : GateDescriptor) : Nat :=
  G.kind.inputArity

/-- Declared output arity of a gate descriptor. -/
def outputArity (G : GateDescriptor) : Nat :=
  G.kind.outputArity

/-- Declared boundary terminal count of a gate descriptor. -/
def terminalCount (G : GateDescriptor) : Nat :=
  G.inputPorts.length + G.outputPorts.length

/-- Port lists have the declared gate arities. -/
theorem terminalCount_eq_kind (G : GateDescriptor) :
    G.terminalCount = G.kind.terminalCount := by
  unfold terminalCount GateKind.terminalCount
  rw [G.inputPorts_length, G.outputPorts_length]

end GateDescriptor

/-- Build a gate descriptor whose truth table is the standard one for its kind. -/
def gateDescriptor (kind : GateKind) (name : String) (notes : List String) :
    GateDescriptor where
  kind := kind
  name := name
  inputPorts := inputPorts kind.inputArity
  outputPorts := outputPorts kind.outputArity
  inputPorts_length := by simp
  outputPorts_length := by simp
  truthTable := kind.accepts
  notes := notes

/-- AND-gate descriptor with two inputs and one output. -/
def andGate : GateDescriptor :=
  gateDescriptor GateKind.andGate "and_gate"
    [ "Descriptor-level AND truth table; no concrete tile coordinates are asserted here." ]

/-- NOT-gate descriptor with one input and one output. -/
def notGate : GateDescriptor :=
  gateDescriptor GateKind.notGate "not_gate"
    [ "Descriptor-level NOT truth table; no concrete tile coordinates are asserted here." ]

/-- Splitter descriptor with one input and two equal outputs. -/
def splitter : GateDescriptor :=
  gateDescriptor GateKind.splitter "splitter"
    [ "Descriptor-level splitter truth table; both outputs carry the input signal." ]

/-- Variable-start descriptor with one unconstrained outgoing signal. -/
def variableStart : GateDescriptor :=
  gateDescriptor GateKind.variableStart "variable_start"
    [ "Variable starts choose the outgoing signal; no source assignment semantics is asserted here." ]

/-- True-terminal descriptor requiring its incoming signal to be high. -/
def trueTerminal : GateDescriptor :=
  gateDescriptor GateKind.trueTerminal "true_terminal"
    [ "Descriptor-level terminal that accepts exactly a high incoming signal." ]

@[simp]
theorem andGate_terminalCount :
    andGate.terminalCount = 3 := by
  rfl

@[simp]
theorem notGate_terminalCount :
    notGate.terminalCount = 2 := by
  rfl

@[simp]
theorem splitter_terminalCount :
    splitter.terminalCount = 3 := by
  rfl

@[simp]
theorem variableStart_terminalCount :
    variableStart.terminalCount = 1 := by
  rfl

@[simp]
theorem trueTerminal_terminalCount :
    trueTerminal.terminalCount = 1 := by
  rfl

@[simp]
theorem andGate_truthTable_iff
    (inputs : Fin 2 → Signal) (outputs : Fin 1 → Signal) :
    andGate.truthTable inputs outputs ↔
      outputs (0 : Fin 1) = Signal.and (inputs (0 : Fin 2)) (inputs (1 : Fin 2)) :=
  Iff.rfl

@[simp]
theorem notGate_truthTable_iff
    (inputs : Fin 1 → Signal) (outputs : Fin 1 → Signal) :
    notGate.truthTable inputs outputs ↔
      outputs (0 : Fin 1) = Signal.negate (inputs (0 : Fin 1)) :=
  Iff.rfl

@[simp]
theorem splitter_truthTable_iff
    (inputs : Fin 1 → Signal) (outputs : Fin 2 → Signal) :
    splitter.truthTable inputs outputs ↔
      outputs (0 : Fin 2) = inputs (0 : Fin 1) ∧
        outputs (1 : Fin 2) = inputs (0 : Fin 1) :=
  Iff.rfl

@[simp]
theorem variableStart_truthTable_iff
    (inputs : Fin 0 → Signal) (outputs : Fin 1 → Signal) :
    variableStart.truthTable inputs outputs ↔ True :=
  Iff.rfl

@[simp]
theorem trueTerminal_truthTable_iff
    (inputs : Fin 1 → Signal) (outputs : Fin 0 → Signal) :
    trueTerminal.truthTable inputs outputs ↔ inputs (0 : Fin 1) = Signal.high :=
  Iff.rfl

/-- Wire-like descriptor catalog selected from Moore-Robson's gadget vocabulary. -/
def wireCatalog : List WireDescriptor :=
  [wire, bend, phaseChange]

/-- Gate-like descriptor catalog selected from Moore-Robson's gadget vocabulary. -/
def gateCatalog : List GateDescriptor :=
  [andGate, notGate, splitter, variableStart, trueTerminal]

@[simp]
theorem wireCatalog_length :
    wireCatalog.length = 3 :=
  rfl

@[simp]
theorem gateCatalog_length :
    gateCatalog.length = 5 :=
  rfl

/-- Every listed gate descriptor has port lengths matching its declared arity. -/
theorem gateCatalog_port_lengths {G : GateDescriptor}
    (_hG : G ∈ gateCatalog) :
    G.inputPorts.length = G.kind.inputArity ∧
      G.outputPorts.length = G.kind.outputArity := by
  exact ⟨G.inputPorts_length, G.outputPorts_length⟩

/-- Every listed wire-like descriptor has two boundary terminals. -/
theorem wireCatalog_terminalCount {W : WireDescriptor}
    (_hW : W ∈ wireCatalog) :
    W.terminalCount = 2 :=
  WireDescriptor.terminalCount_eq_two W

end MooreRobson
end Tiling
end FiniteDomain
end CSP
end ComplexityReduction
