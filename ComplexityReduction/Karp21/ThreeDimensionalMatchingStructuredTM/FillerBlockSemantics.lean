/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.List.Cycle
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.FillerBlocks

/-!
Semantic correctness for one executable filler-triple block.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactFillerCycleAux
    (ctx : CompactFillerBlockContext) (first prev : Nat) :
    List Nat → List (Nat × Nat × Nat)
  | [] => [compactFillerTripleFromData (ctx.1, ctx.2.1, ctx.2.2, prev, first)]
  | x :: xs =>
      compactFillerTripleFromData (ctx.1, ctx.2.1, ctx.2.2, prev, x) ::
        compactFillerCycleAux ctx first x xs

def compactFillerCycleFromData
    (ctx : CompactFillerBlockContext) : List Nat → List (Nat × Nat × Nat)
  | [] => []
  | x :: xs => compactFillerCycleAux ctx x x xs

theorem compactFillerBlockSeenFinalize_eq_append_cycleAux
    (ctx : CompactFillerBlockContext) (first prev : Nat)
    (out : List (Nat × Nat × Nat)) (xs : List Nat) :
    compactFillerBlockFinalize
        ((xs.map compactFillerBlockElementInstruction).foldl
          (fun acc instr => compactFillerBlockStep (acc, instr))
          (ctx, true, first, prev, out)) =
      out ++ compactFillerCycleAux ctx first prev xs := by
  induction xs generalizing prev out with
  | nil =>
      simp [compactFillerCycleAux, compactFillerBlockFinalize,
        compactFillerBlockClosingTriple]
  | cons x xs ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [compactFillerBlockElementInstruction, compactFillerBlockStep,
        compactFillerBlockElementStep, compactFillerBlockAppendTriple]
      have hTail :=
        ih x (out ++ [compactFillerTripleFromData (ctx.1, ctx.2.1, ctx.2.2, prev, x)])
      simpa [compactFillerCycleAux, List.append_assoc] using hTail

theorem compactFillerBlockUnseenFinalize_eq_cycleFromData
    (ctx : CompactFillerBlockContext) (xs : List Nat) :
    compactFillerBlockFinalize
        ((xs.map compactFillerBlockElementInstruction).foldl
          (fun acc instr => compactFillerBlockStep (acc, instr))
          (ctx, false, (0 : Nat), (0 : Nat), ([] : List (Nat × Nat × Nat)))) =
      compactFillerCycleFromData ctx xs := by
  cases xs with
  | nil =>
      simp [compactFillerCycleFromData, compactFillerBlockFinalize]
  | cons x xs =>
      rw [List.map_cons, List.foldl_cons]
      simp [compactFillerBlockElementInstruction, compactFillerBlockStep,
        compactFillerBlockElementStep, compactFillerCycleFromData]
      simpa using compactFillerBlockSeenFinalize_eq_append_cycleAux
        ctx x x ([] : List (Nat × Nat × Nat)) xs

theorem compactFillerTriplesForSourceSetExecutable_eq_cycleFromData
    (p : Nat × Nat × Nat × List Nat) :
    compactFillerTriplesForSourceSetExecutable p =
      compactFillerCycleFromData (p.1, p.2.1, p.2.2.1)
        (compactSupportExecutable (p.1, p.2.2.2)) := by
  change
    compactFillerBlockFinalize
        (((compactSupportExecutable (p.1, p.2.2.2)).map
            compactFillerBlockElementInstruction).foldl
          (fun acc instr => compactFillerBlockStep (acc, instr))
          ((p.1, p.2.1, p.2.2.1), false, (0 : Nat), (0 : Nat),
            ([] : List (Nat × Nat × Nat)))) =
      compactFillerCycleFromData (p.1, p.2.1, p.2.2.1)
        (compactSupportExecutable (p.1, p.2.2.2))
  exact compactFillerBlockUnseenFinalize_eq_cycleFromData
    (p.1, p.2.1, p.2.2.1) (compactSupportExecutable (p.1, p.2.2.2))

theorem compactFillerCycleAux_eq_zipWith
    (ctx : CompactFillerBlockContext) (first prev : Nat) (xs : List Nat) :
    compactFillerCycleAux ctx first prev xs =
      List.zipWith
        (fun x next => compactFillerTripleFromData (ctx.1, ctx.2.1, ctx.2.2, x, next))
        (prev :: xs) (xs ++ [first]) := by
  induction xs generalizing prev with
  | nil =>
      simp [compactFillerCycleAux]
  | cons x xs ih =>
      simp [compactFillerCycleAux, ih]

theorem compactFillerCycleFromData_eq_zipWith_rotate
    (ctx : CompactFillerBlockContext) (support : List Nat) :
    compactFillerCycleFromData ctx support =
      List.zipWith
        (fun x next => compactFillerTripleFromData (ctx.1, ctx.2.1, ctx.2.2, x, next))
        support (support.rotate 1) := by
  cases support with
  | nil =>
      simp [compactFillerCycleFromData]
  | cons x xs =>
      rw [compactFillerCycleFromData, compactFillerCycleAux_eq_zipWith]
      simp [List.rotate_cons_succ, List.rotate_zero]

theorem compactFillerCycleFromData_eq_map_getD
    (ctx : CompactFillerBlockContext) (support : List Nat)
    (hNodup : support.Nodup) :
    compactFillerCycleFromData ctx support =
      support.map fun x =>
        compactFillerTripleFromData
          (ctx.1, ctx.2.1, ctx.2.2, x,
            support.getD ((support.idxOf x + 1) % support.length) x) := by
  rw [compactFillerCycleFromData_eq_zipWith_rotate]
  apply List.ext_getElem
  · simp [List.length_zipWith, List.length_rotate]
  · intro i hZip hMap
    have hSupport : i < support.length := by
      simpa [List.length_zipWith, List.length_rotate] using hZip
    have hLen : 0 < support.length := Nat.lt_of_le_of_lt (Nat.zero_le i) hSupport
    have hIdx : support.idxOf support[i] = i :=
      hNodup.idxOf_getElem i hSupport
    have hGetD :
        support.getD ((support.idxOf support[i] + 1) % support.length) support[i] =
          support[(i + 1) % support.length]'(Nat.mod_lt _ hLen) := by
      rw [hIdx]
      exact List.getD_eq_getElem (l := support) (d := support[i]) (Nat.mod_lt _ hLen)
    simp
    change
      compactFillerTripleFromData
          (ctx.1, ctx.2.1, ctx.2.2, support[i],
            support[(i + 1) % support.length]'(Nat.mod_lt _ hLen)) =
        compactFillerTripleFromData
          (ctx.1, ctx.2.1, ctx.2.2, support[i],
            support.getD ((support.idxOf support[i] + 1) % support.length) support[i])
    rw [hGetD]

theorem compactFillerTriplesForSourceSetExecutable_eq_compactFillerTriplesForBetaSet
    (I : ExactCoverInput) (beta : Nat) (j : Nat) :
    compactFillerTriplesForSourceSetExecutable
        (I.system.universeSize, beta, j, compactSourceSetAt I j) =
      compactFillerTriplesForBetaSet I beta j := by
  rw [compactFillerTriplesForSourceSetExecutable_eq_cycleFromData]
  rw [compactSupportExecutable_eq_compactSupport]
  rw [compactFillerCycleFromData_eq_map_getD]
  · unfold compactFillerTriplesForBetaSet
    apply List.map_congr_left
    intro x hx
    exact compactFillerTripleFromData_eq_compactFillerTriple (I := I)
      (beta := beta) (x := x) (j := j)
      (next := (compactSupport I (compactSourceSetAt I j)).getD
        (((compactSupport I (compactSourceSetAt I j)).idxOf x + 1) %
          (compactSupport I (compactSourceSetAt I j)).length) x) rfl
  · exact compactSupport_nodup I (compactSourceSetAt I j)

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
