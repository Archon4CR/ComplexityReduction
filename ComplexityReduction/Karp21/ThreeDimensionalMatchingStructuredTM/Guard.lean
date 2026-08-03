/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.FillerFamily
import ComplexityReduction.Karp21.SteinerTreeStructuredTM.WellFormed

/-!
Executable guard for the compact Exact-Cover-to-3-Dimensional-Matching route.

The compact 3DM map is guarded by both source set-system well-formedness and
the semantic condition that every universe element occurs in at least one source
set.  The first condition is shared with the compact Steiner route; this file
adds the second condition as a direct finite-alphabet fold.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactElementOccursBoolInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType

def compactEveryElementGuardContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType

def compactEveryElementGuardAccEncodedType : EncodedType :=
  EncodedType.prod compactEveryElementGuardContextEncodedType EncodedType.bool

def compactEveryElementGuardInstructionEncodedType : EncodedType :=
  EncodedType.sum compactEveryElementGuardContextEncodedType EncodedType.nat

def compactEveryElementGuardInstructionListEncodedType : EncodedType :=
  EncodedType.list compactEveryElementGuardInstructionEncodedType

def compactEveryElementGuardInputEncodedType : EncodedType :=
  compactEveryElementGuardContextEncodedType

abbrev CompactEveryElementGuardContext := Nat × List (List Nat)
abbrev CompactEveryElementGuardAcc := CompactEveryElementGuardContext × Bool

def compactElementOccursBool (p : Nat × List (List Nat)) : Bool :=
  SteinerTree.natLtBool
    (0, (HittingSet.setIndexIndicesFromFamily (p.1, p.2)).length)

theorem compactElementOccursBool_eq_true_iff (p : Nat × List (List Nat)) :
    compactElementOccursBool p = true ↔
      ∃ j, j < p.2.length ∧ p.1 ∈ p.2.getD j [] := by
  rcases p with ⟨x, sets⟩
  rw [compactElementOccursBool, SteinerTree.natLtBool_eq_true_iff]
  rw [HittingSet.setIndexIndicesFromFamily_eq_findIdxs]
  constructor
  · intro hLen
    let idxs := sets.findIdxs (fun S => HittingSet.setContainsBool (x, S))
    have hIdxsPos : 0 < idxs.length := hLen
    have hNonempty : idxs ≠ [] := List.ne_nil_of_length_pos hIdxsPos
    have hMem : ∃ j, j ∈ idxs := by
      cases hIdxs : idxs with
      | nil =>
          exact False.elim (hNonempty hIdxs)
      | cons j js =>
          exact ⟨j, by simp⟩
    rcases hMem with ⟨j, hj⟩
    rcases (List.mem_findIdxs_iff_exists_getElem_pos
        (xs := sets) (p := fun S : List Nat => HittingSet.setContainsBool (x, S))).1 hj
      with ⟨hjLt, hPred⟩
    refine ⟨j, hjLt, ?_⟩
    rw [List.getD_eq_getElem (l := sets) (d := []) hjLt]
    exact (HittingSet.setContainsBool_eq_true_iff (x, sets[j])).1 hPred
  · rintro ⟨j, hjLt, hx⟩
    have hjMem :
        j ∈ sets.findIdxs (fun S => HittingSet.setContainsBool (x, S)) := by
      rw [List.getD_eq_getElem (l := sets) (d := []) hjLt] at hx
      exact
        (List.mem_findIdxs_iff_exists_getElem_pos
          (xs := sets) (p := fun S : List Nat => HittingSet.setContainsBool (x, S))).2
          ⟨hjLt, (HittingSet.setContainsBool_eq_true_iff (x, sets[j])).2 hx⟩
    exact List.length_pos_of_mem hjMem

theorem compactElementOccursBool_tm_polytime :
    TMPolyTimeMap
      compactElementOccursBoolInputEncodedType
      EncodedType.bool
      compactElementOccursBool := by
  let X := compactElementOccursBoolInputEncodedType
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, compactElementOccursBoolInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, compactElementOccursBoolInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
  have hIndexInput :
      TMPolyTimeMap X HittingSet.setIndexInstructionInputEncodedType
        (fun p : X.Carrier => (p.1, p.2)) := by
    simpa [HittingSet.setIndexInstructionInputEncodedType] using
      TMPolyTimeMap.prod_mk hX hSets
  have hIndices :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => HittingSet.setIndexIndicesFromFamily (p.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setIndexIndicesFromFamily_tm_polytime hIndexInput
    simpa [Function.comp, X] using hComp
  have hLength :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => (HittingSet.setIndexIndicesFromFamily (p.1, p.2)).length) := by
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime hIndices
    simpa [Function.comp, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hLtInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier =>
          ((0 : Nat), (HittingSet.setIndexIndicesFromFamily (p.1, p.2)).length)) :=
    TMPolyTimeMap.prod_mk hZero hLength
  have hLt := TMPolyTimeMap.comp SteinerTree.natLtBool_tm_polytime hLtInput
  simpa [Function.comp, compactElementOccursBool, X] using hLt

def compactEveryElementGuardInitAcc : CompactEveryElementGuardAcc :=
  ((0, []), true)

def compactEveryElementGuardInitInstruction (ctx : CompactEveryElementGuardContext) :
    compactEveryElementGuardInstructionEncodedType.Carrier :=
  Sum.inl ctx

def compactEveryElementGuardElementInstruction (x : Nat) :
    compactEveryElementGuardInstructionEncodedType.Carrier :=
  Sum.inr x

def compactEveryElementGuardInstructions (p : CompactEveryElementGuardContext) :
    List compactEveryElementGuardInstructionEncodedType.Carrier :=
  compactEveryElementGuardInitInstruction p ::
    (List.range p.1).map compactEveryElementGuardElementInstruction

def compactEveryElementGuardElementStep (p : CompactEveryElementGuardAcc × Nat) :
    CompactEveryElementGuardAcc :=
  let ctx := p.1.1
  let ok := p.1.2
  let x := p.2
  (ctx, graphBoolAndPair (ok, compactElementOccursBool (x, ctx.2)))

def compactEveryElementGuardStep
    (p : CompactEveryElementGuardAcc × compactEveryElementGuardInstructionEncodedType.Carrier) :
    CompactEveryElementGuardAcc :=
  match p.2 with
  | Sum.inl ctx => (ctx, true)
  | Sum.inr x => compactEveryElementGuardElementStep (p.1, x)

def compactEveryElementGuardFromInstructions
    (xs : List compactEveryElementGuardInstructionEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc instr => compactEveryElementGuardStep (acc, instr))
    compactEveryElementGuardInitAcc).2

def compactEveryElementOccursBool (p : CompactEveryElementGuardContext) : Bool :=
  compactEveryElementGuardFromInstructions (compactEveryElementGuardInstructions p)

/-! ### Semantics -/

theorem compactEveryElementGuardElementFold_eq_true_iff
    (ctx : CompactEveryElementGuardContext) (xs : List Nat) (ok : Bool) :
    ((xs.map compactEveryElementGuardElementInstruction).foldl
        (fun acc instr => compactEveryElementGuardStep (acc, instr)) (ctx, ok)).2 = true ↔
      ok = true ∧
        ∀ x ∈ xs, ∃ j, j < ctx.2.length ∧ x ∈ ctx.2.getD j [] := by
  induction xs generalizing ok with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.foldl_cons]
      have hTail :=
        ih (graphBoolAndPair (ok, compactElementOccursBool (x, ctx.2)))
      simpa [compactEveryElementGuardElementInstruction, compactEveryElementGuardStep,
        compactEveryElementGuardElementStep, graphBoolAndPair_eq_true_iff,
        compactElementOccursBool_eq_true_iff, and_assoc] using hTail

theorem compactEveryElementOccursBool_eq_true_iff
    (p : CompactEveryElementGuardContext) :
    compactEveryElementOccursBool p = true ↔
      ∀ x ∈ List.range p.1, ∃ j, j < p.2.length ∧ x ∈ p.2.getD j [] := by
  rcases p with ⟨universeSize, sets⟩
  simpa [compactEveryElementOccursBool, compactEveryElementGuardFromInstructions,
    compactEveryElementGuardInstructions, compactEveryElementGuardInitInstruction,
    compactEveryElementGuardStep, compactEveryElementGuardInitAcc] using
    (compactEveryElementGuardElementFold_eq_true_iff
      (universeSize, sets) (List.range universeSize) true)

theorem compactEveryElementOccursBool_eq_compactEveryElementOccurs
    (I : ExactCoverInput) :
    compactEveryElementOccursBool (I.system.universeSize, I.system.sets) = true ↔
      compactEveryElementOccurs I := by
  rw [compactEveryElementOccursBool_eq_true_iff]
  constructor
  · intro h x hxLt
    have hxRange : x ∈ List.range I.system.universeSize := by
      simpa using hxLt
    rcases h x hxRange with ⟨j, hj, hxSet⟩
    refine ⟨j, hj, ?_⟩
    rw [mem_compactSupport_iff]
    constructor
    · exact hxLt
    · have hSource :
          compactSourceSetAt I j = I.system.sets[j] := by
        rw [compactSourceSetAt, List.getD_eq_getElem (l := I.system.sets) (d := []) hj]
      have hGetD : I.system.sets[j]?.getD [] = I.system.sets[j] :=
        List.getD_eq_getElem (l := I.system.sets) (d := []) hj
      have hxSet' : x ∈ I.system.sets[j] := by
        simpa [hGetD] using hxSet
      simpa [hSource] using hxSet'
  · intro hEvery x hxRange
    have hxLt : x < I.system.universeSize := by
      simpa using hxRange
    rcases hEvery x hxLt with ⟨j, hj, hxSupport⟩
    have hxSet := ((mem_compactSupport_iff I (compactSourceSetAt I j) x).1 hxSupport).2
    refine ⟨j, hj, ?_⟩
    have hSource :
        compactSourceSetAt I j = I.system.sets[j] := by
      rw [compactSourceSetAt, List.getD_eq_getElem (l := I.system.sets) (d := []) hj]
    have hGetD : I.system.sets[j]?.getD [] = I.system.sets[j] :=
      List.getD_eq_getElem (l := I.system.sets) (d := []) hj
    have hxSet' : x ∈ I.system.sets[j] := by
      simpa [hSource] using hxSet
    simpa [hGetD] using hxSet'

/-! ### TM witnesses -/

theorem compactEveryElementGuardInitInstruction_tm_polytime :
    TMPolyTimeMap
      compactEveryElementGuardContextEncodedType
      compactEveryElementGuardInstructionEncodedType
      compactEveryElementGuardInitInstruction := by
  simpa [compactEveryElementGuardInstructionEncodedType,
    compactEveryElementGuardInitInstruction] using
    TMPolyTimeMap.inl compactEveryElementGuardContextEncodedType EncodedType.nat

theorem compactEveryElementGuardElementInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactEveryElementGuardInstructionEncodedType
      compactEveryElementGuardElementInstruction := by
  simpa [compactEveryElementGuardInstructionEncodedType,
    compactEveryElementGuardElementInstruction] using
    TMPolyTimeMap.inr compactEveryElementGuardContextEncodedType EncodedType.nat

theorem compactEveryElementGuardInstructions_tm_polytime :
    TMPolyTimeMap
      compactEveryElementGuardInputEncodedType
      compactEveryElementGuardInstructionListEncodedType
      compactEveryElementGuardInstructions := by
  let X := compactEveryElementGuardInputEncodedType
  have hCtx : TMPolyTimeMap X compactEveryElementGuardContextEncodedType (fun p : X.Carrier => p) :=
    TMPolyTimeMap.id X
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, compactEveryElementGuardInputEncodedType,
      compactEveryElementGuardContextEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
  have hInit :
      TMPolyTimeMap X compactEveryElementGuardInstructionEncodedType
        (fun p : X.Carrier => compactEveryElementGuardInitInstruction p) := by
    have hComp := TMPolyTimeMap.comp compactEveryElementGuardInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => List.range p.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hUniverse
    simpa [Function.comp, X] using hComp
  have hMapped :
      TMPolyTimeMap X compactEveryElementGuardInstructionListEncodedType
        (fun p : X.Carrier =>
          (List.range p.1).map compactEveryElementGuardElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactEveryElementGuardElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, compactEveryElementGuardInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactEveryElementGuardInstructionEncodedType
          compactEveryElementGuardInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactEveryElementGuardInitInstruction p,
            (List.range p.1).map compactEveryElementGuardElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMapped
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons compactEveryElementGuardInstructionEncodedType)
      hConsInput
  simpa [Function.comp, compactEveryElementGuardInstructions,
    compactEveryElementGuardInstructionListEncodedType, X] using hCons

theorem compactEveryElementGuardElementStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactEveryElementGuardAccEncodedType EncodedType.nat)
      compactEveryElementGuardAccEncodedType
      compactEveryElementGuardElementStep := by
  let X := EncodedType.prod compactEveryElementGuardAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactEveryElementGuardAccEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactEveryElementGuardAccEncodedType EncodedType.nat
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactEveryElementGuardAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X compactEveryElementGuardContextEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst compactEveryElementGuardContextEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactEveryElementGuardAccEncodedType, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd compactEveryElementGuardContextEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactEveryElementGuardAccEncodedType, X] using hComp
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, compactEveryElementGuardContextEncodedType, X] using hComp
  have hOccursInput :
      TMPolyTimeMap X compactElementOccursBoolInputEncodedType
        (fun p : X.Carrier => (p.2, p.1.1.2)) := by
    simpa [compactElementOccursBoolInputEncodedType] using TMPolyTimeMap.prod_mk hX hSets
  have hOccurs :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => compactElementOccursBool (p.2, p.1.1.2)) := by
    have hComp := TMPolyTimeMap.comp compactElementOccursBool_tm_polytime hOccursInput
    simpa [Function.comp, X] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier => (p.1.2, compactElementOccursBool (p.2, p.1.1.2))) :=
    TMPolyTimeMap.prod_mk hOk hOccurs
  have hAnd :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          graphBoolAndPair (p.1.2, compactElementOccursBool (p.2, p.1.1.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp, X] using hComp
  have hOut := TMPolyTimeMap.prod_mk hCtx hAnd
  simpa [compactEveryElementGuardElementStep,
    compactEveryElementGuardAccEncodedType, X] using hOut

theorem compactEveryElementGuardStepLeft_tm_polytime :
    TMPolyTimeMap
      compactEveryElementGuardContextEncodedType
      compactEveryElementGuardAccEncodedType
      (fun ctx : CompactEveryElementGuardContext => (ctx, true)) := by
  have hCtx := TMPolyTimeMap.id compactEveryElementGuardContextEncodedType
  have hTrue :
      TMPolyTimeMap compactEveryElementGuardContextEncodedType EncodedType.bool
        (fun _ : CompactEveryElementGuardContext => true) :=
    TMPolyTimeMap.const compactEveryElementGuardContextEncodedType EncodedType.bool true
  simpa [compactEveryElementGuardAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hTrue

theorem compactEveryElementGuardStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactEveryElementGuardAccEncodedType
        compactEveryElementGuardInstructionEncodedType)
      compactEveryElementGuardAccEncodedType
      compactEveryElementGuardStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      compactEveryElementGuardAccEncodedType compactEveryElementGuardContextEncodedType
      EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim compactEveryElementGuardStepLeft_tm_polytime
      compactEveryElementGuardElementStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem compactEveryElementGuardInitAcc_bound
    (xs : List compactEveryElementGuardInstructionEncodedType.Carrier) :
    compactEveryElementGuardAccEncodedType.inputSize compactEveryElementGuardInitAcc ≤
      (Polynomial.C 10).eval
        (compactEveryElementGuardInstructionListEncodedType.inputSize xs) := by
  have hNilSets :
      setStructuredEncodedType.list.inputSize ([] : List (List Nat)) = 0 :=
    EncodedType.inputSize_list_nil setStructuredEncodedType
  simp [compactEveryElementGuardInitAcc, compactEveryElementGuardAccEncodedType,
    compactEveryElementGuardContextEncodedType, setFamilyStructuredEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat,
    EncodedType.inputSize_bool, hNilSets]

theorem compactEveryElementGuardStep_growth
    (source : List compactEveryElementGuardInstructionEncodedType.Carrier)
    (acc : compactEveryElementGuardAccEncodedType.Carrier)
    (instr : compactEveryElementGuardInstructionEncodedType.Carrier)
    (hInstr :
      compactEveryElementGuardInstructionEncodedType.inputSize instr ≤
        compactEveryElementGuardInstructionListEncodedType.inputSize source) :
    compactEveryElementGuardAccEncodedType.inputSize
        (compactEveryElementGuardStep (acc, instr)) ≤
      compactEveryElementGuardAccEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 20).eval
          (compactEveryElementGuardInstructionListEncodedType.inputSize source) := by
  let N := compactEveryElementGuardInstructionListEncodedType.inputSize source
  rcases acc with ⟨ctx, ok⟩
  rcases ctx with ⟨universeSize, sets⟩
  cases instr with
  | inl newCtx =>
      rcases newCtx with ⟨newUniverse, newSets⟩
      have hCtx :
          compactEveryElementGuardContextEncodedType.inputSize (newUniverse, newSets) + 1 ≤
            N := by
        simpa [N, compactEveryElementGuardInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hInstr
      simp [compactEveryElementGuardStep, compactEveryElementGuardAccEncodedType,
        compactEveryElementGuardContextEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_bool, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X] at hCtx ⊢
      omega
  | inr x =>
      simp [compactEveryElementGuardStep, compactEveryElementGuardElementStep,
        compactEveryElementGuardAccEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_bool, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X]

theorem compactEveryElementGuardFold_tm_polytime :
    TMPolyTimeMap
      compactEveryElementGuardInstructionListEncodedType
      compactEveryElementGuardAccEncodedType
      (fun xs : List compactEveryElementGuardInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactEveryElementGuardStep (acc, instr))
          compactEveryElementGuardInitAcc) := by
  rcases compactEveryElementGuardStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      compactEveryElementGuardInstructionEncodedType compactEveryElementGuardAccEncodedType
      compactEveryElementGuardStep compactEveryElementGuardInitAcc hStep
      (Polynomial.C 10) (Polynomial.C 10 * Polynomial.X + Polynomial.C 20) ?_ ?_
  · intro xs
    exact compactEveryElementGuardInitAcc_bound xs
  · intro source acc instr hInstr
    exact compactEveryElementGuardStep_growth source acc instr hInstr

theorem compactEveryElementGuardFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactEveryElementGuardInstructionListEncodedType
      EncodedType.bool
      compactEveryElementGuardFromInstructions := by
  have hFold := compactEveryElementGuardFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd compactEveryElementGuardContextEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, compactEveryElementGuardFromInstructions,
    compactEveryElementGuardAccEncodedType] using hComp

theorem compactEveryElementOccursBool_tm_polytime :
    TMPolyTimeMap
      compactEveryElementGuardInputEncodedType
      EncodedType.bool
      compactEveryElementOccursBool := by
  have hComp :=
    TMPolyTimeMap.comp compactEveryElementGuardFromInstructions_tm_polytime
      compactEveryElementGuardInstructions_tm_polytime
  simpa [Function.comp, compactEveryElementOccursBool] using hComp

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
