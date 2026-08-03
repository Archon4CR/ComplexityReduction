/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import ComplexityReduction.CSP.FiniteDomain.Basic

/-!
Finite-domain CSP encoding for local tiling constraints.

Moore-Robson style tiling reductions are built from finite palettes and local
coverage/adjacency checks on grid cells.  This module provides the reusable
finite-domain CSP layer for such reductions: a finite list of local checks is
compiled to one finite-domain CSP language whose relation symbols are check
indices, and the generated formula is proved semantically equivalent to the
local tiling predicate.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace Tiling

/-- A grid cell addressed by natural-number coordinates. -/
structure GridCell where
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

/-- A rectangular finite grid region. -/
structure RectangularRegion where
  width : Nat
  height : Nat
  deriving Repr

namespace RectangularRegion

/-- Number of cells in a rectangular region. -/
def cellCount (R : RectangularRegion) : Nat :=
  R.width * R.height

/-- A coordinate lies inside a rectangular region. -/
def Contains (R : RectangularRegion) (c : GridCell) : Prop :=
  c.x < R.width ∧ c.y < R.height

/-- Row-major variable number for a cell in a rectangular region. -/
def cellVar (R : RectangularRegion) (c : GridCell) : Nat :=
  c.y * R.width + c.x

/-- In-bounds rectangular cells map below the row-major cell count. -/
theorem cellVar_lt_cellCount_of_contains (R : RectangularRegion) (c : GridCell)
    (h : R.Contains c) :
    R.cellVar c < R.cellCount := by
  rcases h with ⟨hx, hy⟩
  have hRow : c.y * R.width + c.x < c.y * R.width + R.width :=
    Nat.add_lt_add_left hx (c.y * R.width)
  have hSucc : c.y + 1 ≤ R.height :=
    Nat.succ_le_of_lt hy
  have hMul : (c.y + 1) * R.width ≤ R.height * R.width :=
    Nat.mul_le_mul_right R.width hSucc
  calc
    R.cellVar c = c.y * R.width + c.x := rfl
    _ < c.y * R.width + R.width := hRow
    _ = (c.y + 1) * R.width := by
      rw [Nat.add_mul, Nat.one_mul]
    _ ≤ R.height * R.width := hMul
    _ = R.cellCount := by
      simp [cellCount, Nat.mul_comm]

end RectangularRegion

/-- An explicit finite region as a list of cells. -/
structure ExplicitRegion where
  cells : List GridCell
  deriving Repr

namespace ExplicitRegion

/-- Number of listed cells in an explicit finite region. -/
def cellCount (R : ExplicitRegion) : Nat :=
  R.cells.length

/-- Variable number for the `i`th listed cell. -/
def cellVar (R : ExplicitRegion) (i : Fin R.cellCount) : Nat :=
  i.val

@[simp]
theorem cellVar_lt_cellCount (R : ExplicitRegion) (i : Fin R.cellCount) :
    R.cellVar i < R.cellCount :=
  i.isLt

/-- Membership of a concrete grid cell in the explicit region list. -/
def Contains (R : ExplicitRegion) (c : GridCell) : Prop :=
  c ∈ R.cells

end ExplicitRegion

/-- A finite tile palette represented by tile and orientation counts. -/
structure TilePalette where
  tileCount : Nat
  orientationCount : Nat
  deriving Repr

namespace TilePalette

/-- The finite CSP domain for oriented tile placements. -/
abbrev State (P : TilePalette) : Type :=
  Fin P.tileCount × Fin P.orientationCount

/-- Extract the unoriented tile component of a palette state. -/
def tile {P : TilePalette} (s : P.State) : Fin P.tileCount :=
  s.1

/-- Extract the orientation component of a palette state. -/
def orientation {P : TilePalette} (s : P.State) : Fin P.orientationCount :=
  s.2

end TilePalette

/-- A total placement of oriented tiles on natural-number variables. -/
abbrev Placement (P : TilePalette) : Type :=
  Assignment P.State

/-- Scope helper for one-cell local checks. -/
def unaryScope (x : Nat) : Fin 1 → Nat :=
  fun _ => x

@[simp]
theorem unaryScope_zero (x : Nat) :
    unaryScope x (0 : Fin 1) = x :=
  rfl

/-- Scope helper for two-cell local checks. -/
def binaryScope (x y : Nat) : Fin 2 → Nat :=
  fun i => if i.val = 0 then x else y

@[simp]
theorem binaryScope_zero (x y : Nat) :
    binaryScope x y (0 : Fin 2) = x := by
  simp [binaryScope]

@[simp]
theorem binaryScope_one (x y : Nat) :
    binaryScope x y (1 : Fin 2) = y := by
  simp [binaryScope]

/-- One local finite-domain tiling check with its concrete CSP variable scope. -/
structure LocalCheck (D : Type) where
  arity : Nat
  scope : Fin arity → Nat
  accepts : Tuple D arity → Prop

namespace LocalCheck

/-- Interpret a local check as a finite-domain CSP relation. -/
def rel {D : Type} (C : LocalCheck D) : Rel D where
  arity := C.arity
  holds := C.accepts

/-- Assignment-level satisfaction of one local tiling check. -/
def Satisfies {D : Type} (C : LocalCheck D) (a : Assignment D) : Prop :=
  C.accepts (fun i => a (C.scope i))

@[simp]
theorem rel_holds_iff {D : Type} (C : LocalCheck D) (t : Tuple D C.arity) :
    C.rel.Holds t ↔ C.accepts t :=
  Iff.rfl

end LocalCheck

/-- The finite-domain language whose symbols are indices of local checks. -/
def localCheckLanguage {D : Type} [Fintype D] (checks : List (LocalCheck D)) :
    Language D where
  finiteDomain := inferInstance
  Symbol := Fin checks.length
  finiteSymbol := inferInstance
  relationOf := fun i => (checks.get i).rel

/-- Assignment-level satisfaction of every local check in a finite list. -/
def LocalChecksSatisfy {D : Type} (checks : List (LocalCheck D))
    (a : Assignment D) : Prop :=
  ∀ i : Fin checks.length, (checks.get i).Satisfies a

/-- The CSP constraint corresponding to one indexed local check. -/
def localCheckConstraint {D : Type} [Fintype D] (checks : List (LocalCheck D))
    (i : Fin checks.length) : Constraint (localCheckLanguage checks) where
  symbol := i
  vars := (checks.get i).scope

/-- The CSP formula containing one constraint per local tiling check. -/
def localCheckFormula {D : Type} [Fintype D] (checks : List (LocalCheck D)) :
    Formula (localCheckLanguage checks) :=
  List.ofFn fun i : Fin checks.length => localCheckConstraint checks i

@[simp]
theorem localCheckConstraint_satisfies_iff {D : Type} [Fintype D]
    (checks : List (LocalCheck D)) (i : Fin checks.length)
    (a : Assignment D) :
    Constraint.Satisfies (localCheckConstraint checks i) a ↔
      (checks.get i).Satisfies a :=
  Iff.rfl

/-- The local-check formula is satisfied exactly when every local check accepts. -/
theorem localCheckFormula_satisfies_iff {D : Type} [Fintype D]
    (checks : List (LocalCheck D)) (a : Assignment D) :
    Formula.Satisfies (localCheckFormula checks) a ↔ LocalChecksSatisfy checks a := by
  constructor
  · intro h i
    have hi : localCheckConstraint checks i ∈ localCheckFormula checks := by
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    exact (localCheckConstraint_satisfies_iff checks i a).1
      (h (localCheckConstraint checks i) hi)
  · intro h c hc
    rcases List.mem_ofFn.mp (by simpa [localCheckFormula] using hc) with ⟨i, rfl⟩
    exact (localCheckConstraint_satisfies_iff checks i a).2 (h i)

/-- The generated CSP formula has one constraint per local check. -/
@[simp]
theorem localCheckFormula_length {D : Type} [Fintype D]
    (checks : List (LocalCheck D)) :
    (localCheckFormula checks).length = checks.length := by
  simp [localCheckFormula]

/-- Directions used by nearest-neighbor grid adjacency checks. -/
inductive Direction where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Unary coverage check: the state placed at variable `x` must be allowed. -/
def coverageCheck (P : TilePalette) (x : Nat)
    (allowed : P.State → Prop) : LocalCheck P.State where
  arity := 1
  scope := unaryScope x
  accepts := fun t => allowed (t (0 : Fin 1))

@[simp]
theorem coverageCheck_satisfies_iff (P : TilePalette) (x : Nat)
    (allowed : P.State → Prop) (a : Placement P) :
    (coverageCheck P x allowed).Satisfies a ↔ allowed (a x) := by
  simp [LocalCheck.Satisfies, coverageCheck]

/--
Binary adjacency check between two cell variables.  The predicate may depend on
the direction, so horizontal and vertical edge checks can share the same shape.
-/
def adjacencyCheck (P : TilePalette) (dir : Direction) (x y : Nat)
    (allowed : Direction → P.State → P.State → Prop) : LocalCheck P.State where
  arity := 2
  scope := binaryScope x y
  accepts := fun t => allowed dir (t (0 : Fin 2)) (t (1 : Fin 2))

@[simp]
theorem adjacencyCheck_satisfies_iff (P : TilePalette) (dir : Direction)
    (x y : Nat) (allowed : Direction → P.State → P.State → Prop)
    (a : Placement P) :
    (adjacencyCheck P dir x y allowed).Satisfies a ↔
      allowed dir (a x) (a y) := by
  simp [LocalCheck.Satisfies, adjacencyCheck]

/-- A finite tiling instance: a finite cell region plus local checks over a palette. -/
structure TilingInstance (P : TilePalette) where
  region : ExplicitRegion
  checks : List (LocalCheck P.State)

namespace TilingInstance

/-- The finite-domain CSP language generated by the local checks of a tiling instance. -/
def language {P : TilePalette} (I : TilingInstance P) : Language P.State :=
  localCheckLanguage I.checks

/-- Assignment-level local tiling predicate for a finite tiling instance. -/
def Satisfies {P : TilePalette} (I : TilingInstance P) (a : Placement P) : Prop :=
  LocalChecksSatisfy I.checks a

/-- The finite-domain CSP formula generated by a finite tiling instance. -/
def tilingFormula {P : TilePalette} (I : TilingInstance P) : Formula I.language :=
  localCheckFormula I.checks

/-- A tiling instance is tileable when some placement satisfies all local checks. -/
def Tileable {P : TilePalette} (I : TilingInstance P) : Prop :=
  ∃ a : Placement P, I.Satisfies a

/-- The generated CSP formula is satisfied exactly by satisfying tile placements. -/
theorem tilingFormula_satisfies_iff {P : TilePalette} (I : TilingInstance P)
    (a : Placement P) :
    Formula.Satisfies I.tilingFormula a ↔ I.Satisfies a := by
  simpa [tilingFormula, Satisfies, language] using
    localCheckFormula_satisfies_iff I.checks a

/-- Satisfiability of the generated CSP formula is exactly local tileability. -/
theorem tilingFormula_satisfiable_iff {P : TilePalette} (I : TilingInstance P) :
    Formula.Satisfiable I.tilingFormula ↔ I.Tileable := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, (I.tilingFormula_satisfies_iff a).1 h⟩
  · rintro ⟨a, h⟩
    exact ⟨a, (I.tilingFormula_satisfies_iff a).2 h⟩

/-- The generated CSP formula has one constraint per local tiling check. -/
@[simp]
theorem tilingFormula_length {P : TilePalette} (I : TilingInstance P) :
    I.tilingFormula.length = I.checks.length := by
  change (localCheckFormula I.checks).length = I.checks.length
  exact localCheckFormula_length I.checks

end TilingInstance

end Tiling
end FiniteDomain
end CSP
end ComplexityReduction
