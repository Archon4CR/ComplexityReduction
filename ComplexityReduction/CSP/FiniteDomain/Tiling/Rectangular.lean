/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.CSP.FiniteDomain.Tiling

/-!
Rectangular-grid generators for finite-domain tiling CSP encodings.

The base tiling module provides local coverage and adjacency checks.  This
module adds the row-major rectangular enumeration layer used by reductions that
need all cell and nearest-neighbor constraints for a finite rectangle.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace Tiling
namespace Rectangular

/-- Row-major list of all cells in a rectangular region. -/
def cells (R : RectangularRegion) : List GridCell :=
  (List.range R.height).flatMap fun y =>
    (List.range R.width).map fun x => { x := x, y := y }

/-- The row-major rectangular cell list has exactly `width * height` entries. -/
@[simp]
theorem cells_length (R : RectangularRegion) :
    (cells R).length = R.cellCount := by
  simp [cells, RectangularRegion.cellCount, Nat.mul_comm]

/-- The generated rectangular cell list contains exactly the in-bounds cells. -/
@[simp]
theorem mem_cells_iff_contains (R : RectangularRegion) (c : GridCell) :
    c ∈ cells R ↔ R.Contains c := by
  constructor
  · intro hc
    rcases List.mem_flatMap.mp hc with ⟨y, hy, hcy⟩
    rcases List.mem_map.mp hcy with ⟨x, hx, hEq⟩
    rw [List.mem_range] at hx hy
    cases hEq
    exact ⟨hx, hy⟩
  · intro hc
    refine List.mem_flatMap.mpr ?_
    exact ⟨c.y, by simpa [RectangularRegion.Contains] using hc.2,
      List.mem_map.mpr
        ⟨c.x, by simpa [RectangularRegion.Contains] using hc.1, rfl⟩⟩

/-- Horizontal nearest-neighbor cell pairs, oriented from left to right. -/
def horizontalPairs (R : RectangularRegion) : List (GridCell × GridCell) :=
  (List.range R.height).flatMap fun y =>
    (List.range (R.width - 1)).map fun x =>
      ({ x := x, y := y }, { x := x + 1, y := y })

/-- Vertical nearest-neighbor cell pairs, oriented from top to bottom. -/
def verticalPairs (R : RectangularRegion) : List (GridCell × GridCell) :=
  (List.range (R.height - 1)).flatMap fun y =>
    (List.range R.width).map fun x =>
      ({ x := x, y := y }, { x := x, y := y + 1 })

/-- Number of generated horizontal nearest-neighbor checks. -/
@[simp]
theorem horizontalPairs_length (R : RectangularRegion) :
    (horizontalPairs R).length = R.height * (R.width - 1) := by
  simp [horizontalPairs]

/-- Number of generated vertical nearest-neighbor checks. -/
@[simp]
theorem verticalPairs_length (R : RectangularRegion) :
    (verticalPairs R).length = (R.height - 1) * R.width := by
  simp [verticalPairs, Nat.mul_comm]

/-- Both endpoints of a generated horizontal pair lie inside the rectangle. -/
theorem horizontalPairs_contains {R : RectangularRegion} {e : GridCell × GridCell}
    (he : e ∈ horizontalPairs R) :
    R.Contains e.1 ∧ R.Contains e.2 := by
  rcases List.mem_flatMap.mp he with ⟨y, hy, hey⟩
  rcases List.mem_map.mp hey with ⟨x, hx, hEq⟩
  rw [List.mem_range] at hx hy
  cases hEq
  have hxLeft : x < R.width := by omega
  have hxRight : x + 1 < R.width := by omega
  exact ⟨⟨hxLeft, hy⟩, ⟨hxRight, hy⟩⟩

/-- Both endpoints of a generated vertical pair lie inside the rectangle. -/
theorem verticalPairs_contains {R : RectangularRegion} {e : GridCell × GridCell}
    (he : e ∈ verticalPairs R) :
    R.Contains e.1 ∧ R.Contains e.2 := by
  rcases List.mem_flatMap.mp he with ⟨y, hy, hey⟩
  rcases List.mem_map.mp hey with ⟨x, hx, hEq⟩
  rw [List.mem_range] at hx hy
  cases hEq
  have hyTop : y < R.height := by omega
  have hyBottom : y + 1 < R.height := by omega
  exact ⟨⟨hx, hyTop⟩, ⟨hx, hyBottom⟩⟩

/-- In-bounds generated cells map below the rectangular variable bound. -/
theorem cellVar_lt_cellCount_of_mem_cells {R : RectangularRegion} {c : GridCell}
    (hc : c ∈ cells R) :
    R.cellVar c < R.cellCount :=
  R.cellVar_lt_cellCount_of_contains c ((mem_cells_iff_contains R c).1 hc)

/-- Generated horizontal pair variables are below the rectangular variable bound. -/
theorem horizontalPairs_cellVar_lt_cellCount {R : RectangularRegion}
    {e : GridCell × GridCell} (he : e ∈ horizontalPairs R) :
    R.cellVar e.1 < R.cellCount ∧ R.cellVar e.2 < R.cellCount := by
  have hContains := horizontalPairs_contains (R := R) he
  exact ⟨R.cellVar_lt_cellCount_of_contains e.1 hContains.1,
    R.cellVar_lt_cellCount_of_contains e.2 hContains.2⟩

/-- Generated vertical pair variables are below the rectangular variable bound. -/
theorem verticalPairs_cellVar_lt_cellCount {R : RectangularRegion}
    {e : GridCell × GridCell} (he : e ∈ verticalPairs R) :
    R.cellVar e.1 < R.cellCount ∧ R.cellVar e.2 < R.cellCount := by
  have hContains := verticalPairs_contains (R := R) he
  exact ⟨R.cellVar_lt_cellCount_of_contains e.1 hContains.1,
    R.cellVar_lt_cellCount_of_contains e.2 hContains.2⟩

/-- Coverage checks generated for every rectangular cell. -/
def coverageChecks (R : RectangularRegion) (P : TilePalette)
    (allowedCell : GridCell → P.State → Prop) : List (LocalCheck P.State) :=
  (cells R).map fun c => coverageCheck P (R.cellVar c) (allowedCell c)

/-- Horizontal adjacency checks generated for every horizontal nearest-neighbor pair. -/
def horizontalAdjacencyChecks (R : RectangularRegion) (P : TilePalette)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop) :
    List (LocalCheck P.State) :=
  (horizontalPairs R).map fun e =>
    adjacencyCheck P Direction.horizontal (R.cellVar e.1) (R.cellVar e.2)
      (fun dir s t => allowedAdj dir e.1 e.2 s t)

/-- Vertical adjacency checks generated for every vertical nearest-neighbor pair. -/
def verticalAdjacencyChecks (R : RectangularRegion) (P : TilePalette)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop) :
    List (LocalCheck P.State) :=
  (verticalPairs R).map fun e =>
    adjacencyCheck P Direction.vertical (R.cellVar e.1) (R.cellVar e.2)
      (fun dir s t => allowedAdj dir e.1 e.2 s t)

/-- All nearest-neighbor adjacency checks for a rectangle. -/
def adjacencyChecks (R : RectangularRegion) (P : TilePalette)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop) :
    List (LocalCheck P.State) :=
  horizontalAdjacencyChecks R P allowedAdj ++ verticalAdjacencyChecks R P allowedAdj

/-- Coverage check count for a rectangle. -/
@[simp]
theorem coverageChecks_length (R : RectangularRegion) (P : TilePalette)
    (allowedCell : GridCell → P.State → Prop) :
    (coverageChecks R P allowedCell).length = R.cellCount := by
  simp [coverageChecks]

/-- Horizontal adjacency check count for a rectangle. -/
@[simp]
theorem horizontalAdjacencyChecks_length (R : RectangularRegion) (P : TilePalette)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop) :
    (horizontalAdjacencyChecks R P allowedAdj).length = R.height * (R.width - 1) := by
  simp [horizontalAdjacencyChecks]

/-- Vertical adjacency check count for a rectangle. -/
@[simp]
theorem verticalAdjacencyChecks_length (R : RectangularRegion) (P : TilePalette)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop) :
    (verticalAdjacencyChecks R P allowedAdj).length = (R.height - 1) * R.width := by
  simp [verticalAdjacencyChecks]

/-- Total adjacency check count for a rectangle. -/
@[simp]
theorem adjacencyChecks_length (R : RectangularRegion) (P : TilePalette)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop) :
    (adjacencyChecks R P allowedAdj).length =
      R.height * (R.width - 1) + (R.height - 1) * R.width := by
  simp [adjacencyChecks]

/-- Coverage and nearest-neighbor checks for a rectangular tiling instance. -/
def localChecks (R : RectangularRegion) (P : TilePalette)
    (allowedCell : GridCell → P.State → Prop)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop) :
    List (LocalCheck P.State) :=
  coverageChecks R P allowedCell ++ adjacencyChecks R P allowedAdj

/-- Total generated local-check count for a rectangular tiling instance. -/
@[simp]
theorem localChecks_length (R : RectangularRegion) (P : TilePalette)
    (allowedCell : GridCell → P.State → Prop)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop) :
    (localChecks R P allowedCell allowedAdj).length =
      R.cellCount + (R.height * (R.width - 1) + (R.height - 1) * R.width) := by
  simp [localChecks]

/-- Assignment-level predicate for generated rectangular local tiling rules. -/
def Satisfies (R : RectangularRegion) (P : TilePalette)
    (allowedCell : GridCell → P.State → Prop)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop)
    (a : Placement P) : Prop :=
  (∀ c, c ∈ cells R → allowedCell c (a (R.cellVar c))) ∧
    (∀ e, e ∈ horizontalPairs R →
      allowedAdj Direction.horizontal e.1 e.2 (a (R.cellVar e.1)) (a (R.cellVar e.2))) ∧
    (∀ e, e ∈ verticalPairs R →
      allowedAdj Direction.vertical e.1 e.2 (a (R.cellVar e.1)) (a (R.cellVar e.2)))

/-- A rectangular tiling instance is tileable when some placement satisfies all rules. -/
def Tileable (R : RectangularRegion) (P : TilePalette)
    (allowedCell : GridCell → P.State → Prop)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop) : Prop :=
  ∃ a : Placement P, Satisfies R P allowedCell allowedAdj a

theorem localChecksSatisfy_iff_forall_mem {D : Type} (checks : List (LocalCheck D))
    (a : Assignment D) :
    LocalChecksSatisfy checks a ↔ ∀ C ∈ checks, C.Satisfies a := by
  constructor
  · intro h C hC
    rcases List.mem_iff_get.mp hC with ⟨i, rfl⟩
    exact h i
  · intro h i
    exact h (checks.get i) (List.get_mem checks i)

theorem localChecksSatisfy_append {D : Type} (xs ys : List (LocalCheck D))
    (a : Assignment D) :
    LocalChecksSatisfy (xs ++ ys) a ↔
      LocalChecksSatisfy xs a ∧ LocalChecksSatisfy ys a := by
  rw [localChecksSatisfy_iff_forall_mem, localChecksSatisfy_iff_forall_mem,
    localChecksSatisfy_iff_forall_mem]
  constructor
  · intro h
    constructor
    · intro C hC
      exact h C (List.mem_append.mpr (Or.inl hC))
    · intro C hC
      exact h C (List.mem_append.mpr (Or.inr hC))
  · intro h C hC
    rcases List.mem_append.mp hC with hC | hC
    · exact h.1 C hC
    · exact h.2 C hC

/-- Coverage checks express exactly the cell-local coverage predicate. -/
theorem coverageChecks_satisfy_iff (R : RectangularRegion) (P : TilePalette)
    (allowedCell : GridCell → P.State → Prop) (a : Placement P) :
    LocalChecksSatisfy (coverageChecks R P allowedCell) a ↔
      ∀ c, c ∈ cells R → allowedCell c (a (R.cellVar c)) := by
  rw [localChecksSatisfy_iff_forall_mem]
  constructor
  · intro h c hc
    have hCheck :
        coverageCheck P (R.cellVar c) (allowedCell c) ∈ coverageChecks R P allowedCell :=
      List.mem_map.mpr ⟨c, hc, rfl⟩
    exact (coverageCheck_satisfies_iff P (R.cellVar c) (allowedCell c) a).1
      (h _ hCheck)
  · intro h C hC
    rcases List.mem_map.mp hC with ⟨c, hc, rfl⟩
    exact (coverageCheck_satisfies_iff P (R.cellVar c) (allowedCell c) a).2 (h c hc)

/-- Horizontal adjacency checks express exactly the horizontal local-rule predicate. -/
theorem horizontalAdjacencyChecks_satisfy_iff (R : RectangularRegion) (P : TilePalette)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop)
    (a : Placement P) :
    LocalChecksSatisfy (horizontalAdjacencyChecks R P allowedAdj) a ↔
      ∀ e, e ∈ horizontalPairs R →
        allowedAdj Direction.horizontal e.1 e.2 (a (R.cellVar e.1)) (a (R.cellVar e.2)) := by
  rw [localChecksSatisfy_iff_forall_mem]
  constructor
  · intro h e he
    have hCheck :
        adjacencyCheck P Direction.horizontal (R.cellVar e.1) (R.cellVar e.2)
            (fun dir s t => allowedAdj dir e.1 e.2 s t) ∈
          horizontalAdjacencyChecks R P allowedAdj :=
      List.mem_map.mpr ⟨e, he, rfl⟩
    exact (adjacencyCheck_satisfies_iff P Direction.horizontal
      (R.cellVar e.1) (R.cellVar e.2)
      (fun dir s t => allowedAdj dir e.1 e.2 s t) a).1 (h _ hCheck)
  · intro h C hC
    rcases List.mem_map.mp hC with ⟨e, he, rfl⟩
    exact (adjacencyCheck_satisfies_iff P Direction.horizontal
      (R.cellVar e.1) (R.cellVar e.2)
      (fun dir s t => allowedAdj dir e.1 e.2 s t) a).2 (h e he)

/-- Vertical adjacency checks express exactly the vertical local-rule predicate. -/
theorem verticalAdjacencyChecks_satisfy_iff (R : RectangularRegion) (P : TilePalette)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop)
    (a : Placement P) :
    LocalChecksSatisfy (verticalAdjacencyChecks R P allowedAdj) a ↔
      ∀ e, e ∈ verticalPairs R →
        allowedAdj Direction.vertical e.1 e.2 (a (R.cellVar e.1)) (a (R.cellVar e.2)) := by
  rw [localChecksSatisfy_iff_forall_mem]
  constructor
  · intro h e he
    have hCheck :
        adjacencyCheck P Direction.vertical (R.cellVar e.1) (R.cellVar e.2)
            (fun dir s t => allowedAdj dir e.1 e.2 s t) ∈
          verticalAdjacencyChecks R P allowedAdj :=
      List.mem_map.mpr ⟨e, he, rfl⟩
    exact (adjacencyCheck_satisfies_iff P Direction.vertical
      (R.cellVar e.1) (R.cellVar e.2)
      (fun dir s t => allowedAdj dir e.1 e.2 s t) a).1 (h _ hCheck)
  · intro h C hC
    rcases List.mem_map.mp hC with ⟨e, he, rfl⟩
    exact (adjacencyCheck_satisfies_iff P Direction.vertical
      (R.cellVar e.1) (R.cellVar e.2)
      (fun dir s t => allowedAdj dir e.1 e.2 s t) a).2 (h e he)

/-- Adjacency checks express exactly the horizontal and vertical local rules. -/
theorem adjacencyChecks_satisfy_iff (R : RectangularRegion) (P : TilePalette)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop)
    (a : Placement P) :
    LocalChecksSatisfy (adjacencyChecks R P allowedAdj) a ↔
      (∀ e, e ∈ horizontalPairs R →
        allowedAdj Direction.horizontal e.1 e.2 (a (R.cellVar e.1)) (a (R.cellVar e.2))) ∧
      (∀ e, e ∈ verticalPairs R →
        allowedAdj Direction.vertical e.1 e.2 (a (R.cellVar e.1)) (a (R.cellVar e.2))) := by
  rw [adjacencyChecks, localChecksSatisfy_append,
    horizontalAdjacencyChecks_satisfy_iff, verticalAdjacencyChecks_satisfy_iff]

/-- Generated local checks are equivalent to the rectangular tiling predicate. -/
theorem localChecks_satisfy_iff (R : RectangularRegion) (P : TilePalette)
    (allowedCell : GridCell → P.State → Prop)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop)
    (a : Placement P) :
    LocalChecksSatisfy (localChecks R P allowedCell allowedAdj) a ↔
      Satisfies R P allowedCell allowedAdj a := by
  rw [localChecks, localChecksSatisfy_append, coverageChecks_satisfy_iff,
    adjacencyChecks_satisfy_iff, Satisfies]

/-- Rectangular tiling instance generated from cell and adjacency predicates. -/
def rectangularTilingInstance (R : RectangularRegion) (P : TilePalette)
    (allowedCell : GridCell → P.State → Prop)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop) :
    TilingInstance P where
  region := { cells := cells R }
  checks := localChecks R P allowedCell allowedAdj

/-- Finite-domain CSP formula generated from a rectangular tiling instance. -/
def rectangularTilingFormula (R : RectangularRegion) (P : TilePalette)
    (allowedCell : GridCell → P.State → Prop)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop) :
    Formula (rectangularTilingInstance R P allowedCell allowedAdj).language :=
  (rectangularTilingInstance R P allowedCell allowedAdj).tilingFormula

/-- Formula satisfaction is exactly rectangular local-rule satisfaction. -/
theorem rectangularTilingFormula_satisfies_iff (R : RectangularRegion) (P : TilePalette)
    (allowedCell : GridCell → P.State → Prop)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop)
    (a : Placement P) :
    Formula.Satisfies (rectangularTilingFormula R P allowedCell allowedAdj) a ↔
      Satisfies R P allowedCell allowedAdj a := by
  calc
    Formula.Satisfies (rectangularTilingFormula R P allowedCell allowedAdj) a ↔
        LocalChecksSatisfy (localChecks R P allowedCell allowedAdj) a := by
      simpa [rectangularTilingFormula, rectangularTilingInstance, TilingInstance.Satisfies]
        using
          TilingInstance.tilingFormula_satisfies_iff
            (rectangularTilingInstance R P allowedCell allowedAdj) a
    _ ↔ Satisfies R P allowedCell allowedAdj a :=
      localChecks_satisfy_iff R P allowedCell allowedAdj a

/-- Formula satisfiability is exactly rectangular tileability. -/
theorem rectangularTilingFormula_satisfiable_iff (R : RectangularRegion) (P : TilePalette)
    (allowedCell : GridCell → P.State → Prop)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop) :
    Formula.Satisfiable (rectangularTilingFormula R P allowedCell allowedAdj) ↔
      Tileable R P allowedCell allowedAdj := by
  constructor
  · rintro ⟨a, hSat⟩
    exact ⟨a, (rectangularTilingFormula_satisfies_iff R P allowedCell allowedAdj a).1 hSat⟩
  · rintro ⟨a, hSat⟩
    exact ⟨a, (rectangularTilingFormula_satisfies_iff R P allowedCell allowedAdj a).2 hSat⟩

/-- Generated rectangular formulas have exactly one constraint per generated local check. -/
@[simp]
theorem rectangularTilingFormula_length (R : RectangularRegion) (P : TilePalette)
    (allowedCell : GridCell → P.State → Prop)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop) :
    (rectangularTilingFormula R P allowedCell allowedAdj).length =
      (localChecks R P allowedCell allowedAdj).length := by
  simp [rectangularTilingFormula, rectangularTilingInstance]

/-- Generated rectangular formulas have coverage plus horizontal and vertical constraints. -/
theorem rectangularTilingFormula_length_eq (R : RectangularRegion) (P : TilePalette)
    (allowedCell : GridCell → P.State → Prop)
    (allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop) :
    (rectangularTilingFormula R P allowedCell allowedAdj).length =
      R.cellCount + (R.height * (R.width - 1) + (R.height - 1) * R.width) := by
  simp

/-- Coverage-check scopes are below `R.cellCount`. -/
theorem coverageChecks_scope_lt_cellCount {R : RectangularRegion} {P : TilePalette}
    {allowedCell : GridCell → P.State → Prop} {C : LocalCheck P.State}
    (hC : C ∈ coverageChecks R P allowedCell) (i : Fin C.arity) :
    C.scope i < R.cellCount := by
  rcases List.mem_map.mp hC with ⟨c, hc, rfl⟩
  fin_cases i
  simpa [coverageCheck, unaryScope] using cellVar_lt_cellCount_of_mem_cells (R := R) hc

/-- Horizontal adjacency-check scopes are below `R.cellCount`. -/
theorem horizontalAdjacencyChecks_scope_lt_cellCount {R : RectangularRegion}
    {P : TilePalette}
    {allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop}
    {C : LocalCheck P.State} (hC : C ∈ horizontalAdjacencyChecks R P allowedAdj)
    (i : Fin C.arity) :
    C.scope i < R.cellCount := by
  rcases List.mem_map.mp hC with ⟨e, he, rfl⟩
  have hBounds := horizontalPairs_cellVar_lt_cellCount (R := R) he
  fin_cases i
  · simpa [adjacencyCheck, binaryScope] using hBounds.1
  · simpa [adjacencyCheck, binaryScope] using hBounds.2

/-- Vertical adjacency-check scopes are below `R.cellCount`. -/
theorem verticalAdjacencyChecks_scope_lt_cellCount {R : RectangularRegion}
    {P : TilePalette}
    {allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop}
    {C : LocalCheck P.State} (hC : C ∈ verticalAdjacencyChecks R P allowedAdj)
    (i : Fin C.arity) :
    C.scope i < R.cellCount := by
  rcases List.mem_map.mp hC with ⟨e, he, rfl⟩
  have hBounds := verticalPairs_cellVar_lt_cellCount (R := R) he
  fin_cases i
  · simpa [adjacencyCheck, binaryScope] using hBounds.1
  · simpa [adjacencyCheck, binaryScope] using hBounds.2

/-- All adjacency-check scopes are below `R.cellCount`. -/
theorem adjacencyChecks_scope_lt_cellCount {R : RectangularRegion} {P : TilePalette}
    {allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop}
    {C : LocalCheck P.State} (hC : C ∈ adjacencyChecks R P allowedAdj)
    (i : Fin C.arity) :
    C.scope i < R.cellCount := by
  rw [adjacencyChecks] at hC
  rcases List.mem_append.mp hC with hC | hC
  · exact horizontalAdjacencyChecks_scope_lt_cellCount (R := R) hC i
  · exact verticalAdjacencyChecks_scope_lt_cellCount (R := R) hC i

/-- Every generated rectangular local-check scope is below `R.cellCount`. -/
theorem localChecks_scope_lt_cellCount {R : RectangularRegion} {P : TilePalette}
    {allowedCell : GridCell → P.State → Prop}
    {allowedAdj : Direction → GridCell → GridCell → P.State → P.State → Prop}
    {C : LocalCheck P.State} (hC : C ∈ localChecks R P allowedCell allowedAdj)
    (i : Fin C.arity) :
    C.scope i < R.cellCount := by
  rw [localChecks] at hC
  rcases List.mem_append.mp hC with hC | hC
  · exact coverageChecks_scope_lt_cellCount (R := R) hC i
  · exact adjacencyChecks_scope_lt_cellCount (R := R) hC i

end Rectangular
end Tiling
end FiniteDomain
end CSP
end ComplexityReduction
