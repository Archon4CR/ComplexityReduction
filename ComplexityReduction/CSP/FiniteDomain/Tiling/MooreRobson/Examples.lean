/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.Tiling.MooreRobson.Realization

/-!
Small proof-carrying Moore-Robson realization examples.

These examples are API smoke tests for the realization wrapper.  They do not
claim to be the concrete Moore-Robson tile palette from the literature.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace Tiling
namespace MooreRobson

/-- A one-state, unit-colored palette used by the trivial realization example. -/
def trivialWirePalette : Wang.EdgeColoredPalette Unit where
  palette := { tileCount := 1, orientationCount := 1 }
  color := fun _ _ => ()

/-- Empty rectangular region used by the trivial realization example. -/
def trivialWireRegion : WangGadgetRegion Unit where
  region := { width := 0, height := 0 }
  palette := trivialWirePalette
  notes := ["Empty smoke-test region; boundary condition carries the signal relation."]

/-- The unique placement used for the trivial unit palette. -/
def trivialWirePlacement : Placement trivialWirePalette.palette :=
  fun _ => (⟨0, by decide⟩, ⟨0, by decide⟩)

/-- The empty unit-colored region satisfies all rectangular Wang local rules. -/
theorem trivialWirePlacement_satisfies :
    Formula.Satisfies
      (Wang.rectangularWangTilingFormula trivialWireRegion.region trivialWireRegion.palette)
      trivialWirePlacement := by
  rw [Wang.rectangularWangTilingFormula_satisfies_iff]
  simp [trivialWireRegion, trivialWirePalette, trivialWirePlacement, Wang.Satisfies,
    Rectangular.Satisfies, Rectangular.cells, Rectangular.horizontalPairs,
    Rectangular.verticalPairs]

/-- Truth-table predicate for the trivial wire realization. -/
def trivialWireTruthTable (v : PortValuation 1 1) : Prop :=
  wire.truthTable (v.inputs (0 : Fin 1)) (v.outputs (0 : Fin 1))

/--
Boundary condition for the trivial wire realization.  Since the region is
empty, the boundary predicate is deliberately the whole signal relation.
-/
def trivialWireBoundary : BoundaryCondition trivialWirePalette 1 1 :=
  fun v _ => trivialWireTruthTable v

/-- A tiny proof-carrying realization of the descriptor-level wire truth table. -/
def TrivialWireRealization : WangGadgetRealization Unit 1 1 where
  gadget := trivialWireRegion
  boundaryCondition := trivialWireBoundary
  truthTable := trivialWireTruthTable
  complete := by
    intro v hv
    exact ⟨trivialWirePlacement, trivialWirePlacement_satisfies, hv⟩
  sound := by
    intro v h
    rcases h with ⟨_a, _hSat, hBoundary⟩
    exact hBoundary
  notes := ["Proof-carrying smoke test for the local realization API."]

/-- The trivial realization realizes the descriptor-level wire truth table. -/
theorem trivialWire_realizesWireTruthTable :
    realizesWireTruthTable wire TrivialWireRealization := by
  intro v
  rfl

/-- Recover the descriptor truth table from any wire realization certificate. -/
theorem realizationTruthTableOfWire {Color : Type} {W : WireDescriptor}
    {G : WangGadgetRealization Color 1 1}
    (h : realizesWireTruthTable W G) (v : PortValuation 1 1) :
    G.truthTable v ↔ W.truthTable (v.inputs (0 : Fin 1)) (v.outputs (0 : Fin 1)) :=
  h v

/-- Recover the descriptor truth table from any gate realization certificate. -/
theorem realizationTruthTableOfGate {Color : Type} {D : GateDescriptor}
    {G : WangGadgetRealization Color D.kind.inputArity D.kind.outputArity}
    (h : realizesGateTruthTable D G)
    (v : PortValuation D.kind.inputArity D.kind.outputArity) :
    G.truthTable v ↔ D.truthTable v.inputs v.outputs :=
  h v

#check TrivialWireRealization
#check trivialWire_realizesWireTruthTable
#check realizationTruthTableOfWire
#check realizationTruthTableOfGate

end MooreRobson
end Tiling
end FiniteDomain
end CSP
end ComplexityReduction
