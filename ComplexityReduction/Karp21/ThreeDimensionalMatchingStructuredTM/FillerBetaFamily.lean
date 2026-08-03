/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.FillerBlockSemantics
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.CoverFamily
import ComplexityReduction.Karp21.SteinerTreeStructuredTM.Lookup

/-!
Family-level filler-triple assembly for one fixed non-alpha beta code.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactFillerBetaFamilyContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType))

def compactFillerBetaFamilyAccEncodedType : EncodedType :=
  EncodedType.prod compactFillerBetaFamilyContextEncodedType tripleListStructuredEncodedType

def compactFillerBetaFamilyInstructionEncodedType : EncodedType :=
  EncodedType.sum compactFillerBetaFamilyContextEncodedType EncodedType.nat

def compactFillerBetaFamilyInstructionListEncodedType : EncodedType :=
  EncodedType.list compactFillerBetaFamilyInstructionEncodedType

def compactFillerBetaFamilyInputEncodedType : EncodedType :=
  compactFillerBetaFamilyContextEncodedType

abbrev CompactFillerBetaFamilyContext := Nat × Nat × Nat × List (List Nat)
abbrev CompactFillerBetaFamilyAcc :=
  CompactFillerBetaFamilyContext × List (Nat × Nat × Nat)

def compactFillerBetaFamilyInitAcc : CompactFillerBetaFamilyAcc :=
  ((0, 0, 0, []), [])

def compactFillerBetaFamilyInitInstruction (ctx : CompactFillerBetaFamilyContext) :
    compactFillerBetaFamilyInstructionEncodedType.Carrier :=
  Sum.inl ctx

def compactFillerBetaFamilyIndexInstruction (j : Nat) :
    compactFillerBetaFamilyInstructionEncodedType.Carrier :=
  Sum.inr j

def compactFillerBetaFamilyInstructions (p : CompactFillerBetaFamilyContext) :
    List compactFillerBetaFamilyInstructionEncodedType.Carrier :=
  compactFillerBetaFamilyInitInstruction p ::
    (List.range p.2.2.1).map compactFillerBetaFamilyIndexInstruction

def compactFillerBetaFamilyIndexStep (p : CompactFillerBetaFamilyAcc × Nat) :
    CompactFillerBetaFamilyAcc :=
  let ctx := p.1.1
  let out := p.1.2
  let j := p.2
  let S := SteinerTree.setFamilyGetD (ctx.2.2.2, j)
  (ctx, out ++ compactFillerTriplesForSourceSetExecutable (ctx.1, ctx.2.1, j, S))

def compactFillerBetaFamilyStep
    (p : CompactFillerBetaFamilyAcc × compactFillerBetaFamilyInstructionEncodedType.Carrier) :
    CompactFillerBetaFamilyAcc :=
  match p.2 with
  | Sum.inl ctx => (ctx, [])
  | Sum.inr j => compactFillerBetaFamilyIndexStep (p.1, j)

def compactFillerBetaFamilyFromInstructions
    (xs : List compactFillerBetaFamilyInstructionEncodedType.Carrier) :
    List (Nat × Nat × Nat) :=
  (xs.foldl (fun acc instr => compactFillerBetaFamilyStep (acc, instr))
    compactFillerBetaFamilyInitAcc).2

def compactFillerTriplesForBetaExecutable (p : CompactFillerBetaFamilyContext) :
    List (Nat × Nat × Nat) :=
  compactFillerBetaFamilyFromInstructions (compactFillerBetaFamilyInstructions p)

/-! ### Semantics -/

theorem compactFillerBetaFamilyIndexFold_eq_append_flatMap
    (ctx : CompactFillerBetaFamilyContext) (xs : List Nat)
    (out : List (Nat × Nat × Nat)) :
    ((xs.map compactFillerBetaFamilyIndexInstruction).foldl
        (fun acc instr => compactFillerBetaFamilyStep (acc, instr)) (ctx, out)).2 =
      out ++ xs.flatMap (fun j =>
        compactFillerTriplesForSourceSetExecutable
          (ctx.1, ctx.2.1, j, SteinerTree.setFamilyGetD (ctx.2.2.2, j))) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons j js ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [compactFillerBetaFamilyIndexInstruction, compactFillerBetaFamilyStep,
        compactFillerBetaFamilyIndexStep]
      have hTail := ih (out ++
        compactFillerTriplesForSourceSetExecutable
          (ctx.1, ctx.2.1, j, SteinerTree.setFamilyGetD (ctx.2.2.2, j)))
      simpa [List.append_assoc] using hTail

theorem compactFillerTriplesForBetaExecutable_eq_flatMap
    (p : CompactFillerBetaFamilyContext) :
    compactFillerTriplesForBetaExecutable p =
      (List.range p.2.2.1).flatMap (fun j =>
        compactFillerTriplesForSourceSetExecutable
          (p.1, p.2.1, j, SteinerTree.setFamilyGetD (p.2.2.2, j))) := by
  change
    (((List.range p.2.2.1).map compactFillerBetaFamilyIndexInstruction).foldl
        (fun acc instr => compactFillerBetaFamilyStep (acc, instr)) (p, [])).2 =
      (List.range p.2.2.1).flatMap (fun j =>
        compactFillerTriplesForSourceSetExecutable
          (p.1, p.2.1, j, SteinerTree.setFamilyGetD (p.2.2.2, j)))
  simpa using compactFillerBetaFamilyIndexFold_eq_append_flatMap p (List.range p.2.2.1) []

theorem compactFillerTriplesForBetaExecutable_eq_compactFillerTriplesForBeta_tail
    (I : ExactCoverInput) (beta : Nat) :
    compactFillerTriplesForBetaExecutable
        (I.system.universeSize, beta, I.system.sets.length, I.system.sets) =
      (List.range I.system.sets.length).flatMap (compactFillerTriplesForBetaSet I beta) := by
  rw [compactFillerTriplesForBetaExecutable_eq_flatMap]
  apply List.flatMap_congr
  intro j hj
  have hGet :
      SteinerTree.setFamilyGetD (I.system.sets, j) = compactSourceSetAt I j := by
    rfl
  rw [hGet]
  exact compactFillerTriplesForSourceSetExecutable_eq_compactFillerTriplesForBetaSet
    (I := I) (beta := beta) (j := j)

theorem compactFillerTriplesForBetaExecutable_eq_compactFillerTriplesForBeta
    (I : ExactCoverInput) (beta : Nat) :
    compactFillerTriplesForBetaExecutable
        (I.system.universeSize, beta, I.system.sets.length, I.system.sets) =
      compactFillerTriplesForBeta I beta := by
  simpa [compactFillerTriplesForBeta] using
    compactFillerTriplesForBetaExecutable_eq_compactFillerTriplesForBeta_tail I beta

/-! ### Local size facts for the fold -/

theorem compactSupportExecutable_nodup (bound : Nat) (S : List Nat) :
    (compactSupportExecutable (bound, S)).Nodup := by
  rw [compactSupportExecutable_eq_filter]
  exact (List.nodup_range (n := bound)).filter _

theorem compactFillerTriplesForSourceSetExecutable_inputSize_le
    (N universeSize beta j : Nat) (S : List Nat)
    (hUniverse : universeSize + 1 ≤ N)
    (hBeta : beta + 1 ≤ N)
    (hj : j + 1 ≤ N) :
    tripleListStructuredEncodedType.inputSize
        (compactFillerTriplesForSourceSetExecutable (universeSize, beta, j, S)) ≤
      50 * (N * (N * N)) + 50 := by
  let support := compactSupportExecutable (universeSize, S)
  let block := compactFillerTriplesForSourceSetExecutable (universeSize, beta, j, S)
  have hBlockEq :
      block =
        support.map fun x =>
          compactFillerTripleFromData
            (universeSize, beta, j, x,
              support.getD ((support.idxOf x + 1) % support.length) x) := by
    dsimp [block, support]
    rw [compactFillerTriplesForSourceSetExecutable_eq_cycleFromData]
    exact compactFillerCycleFromData_eq_map_getD
      (universeSize, beta, j) (compactSupportExecutable (universeSize, S))
      (compactSupportExecutable_nodup universeSize S)
  have hLen : block.length ≤ N := by
    rw [hBlockEq]
    simp
    have hSupport : support.length ≤ universeSize := by
      simpa [support] using compactSupportExecutable_length_le universeSize S
    omega
  have hEach :
      ∀ t ∈ block, tripleStructuredEncodedType.inputSize t ≤ 10 * (N * N) + 10 := by
    intro t ht
    rw [hBlockEq] at ht
    simp only [List.mem_map] at ht
    rcases ht with ⟨x, hx, rfl⟩
    have hxLt := mem_compactSupportExecutable_lt (bound := universeSize) (S := S) hx
    have hLenPos : 0 < support.length := List.length_pos_of_mem hx
    have hIdx : (support.idxOf x + 1) % support.length < support.length :=
      Nat.mod_lt _ hLenPos
    have hNextMem :
        support.getD ((support.idxOf x + 1) % support.length) x ∈ support := by
      rw [List.getD_eq_getElem (l := support) (d := x) hIdx]
      simp
    have hNextLt := mem_compactSupportExecutable_lt (bound := universeSize) (S := S) hNextMem
    exact compactFillerTripleFromData_inputSize_le N universeSize beta j x
      (support.getD ((support.idxOf x + 1) % support.length) x)
      hUniverse hBeta hj (by omega) (by omega)
  have hList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      tripleStructuredEncodedType block (10 * (N * N) + 10) hEach
  have hPoly :
      block.length * (10 * (N * N) + 10 + 1) ≤ 50 * (N * (N * N)) + 50 := by
    have hN : 1 ≤ N := by omega
    have hLenBound :
        block.length * (10 * (N * N) + 10 + 1) ≤
          N * (10 * (N * N) + 10 + 1) :=
      Nat.mul_le_mul_right _ hLen
    have hN2 : N ≤ N * N := Nat.le_mul_of_pos_right N hN
    have hN3 : N * N ≤ N * (N * N) := Nat.mul_le_mul_left N hN2
    have hNle3 : N ≤ N * (N * N) := hN2.trans hN3
    have hBase :
        N * (10 * (N * N) + 10 + 1) ≤ 50 * (N * (N * N)) + 50 := by
      calc
        N * (10 * (N * N) + 10 + 1)
            = 10 * (N * (N * N)) + 11 * N := by ring
        _ ≤ 50 * (N * (N * N)) + 50 := by omega
    exact hLenBound.trans hBase
  exact hList.trans hPoly

/-! ### TM witnesses -/

theorem compactFillerBetaFamilyInitInstruction_tm_polytime :
    TMPolyTimeMap
      compactFillerBetaFamilyContextEncodedType
      compactFillerBetaFamilyInstructionEncodedType
      compactFillerBetaFamilyInitInstruction := by
  simpa [compactFillerBetaFamilyInstructionEncodedType,
    compactFillerBetaFamilyInitInstruction] using
    TMPolyTimeMap.inl compactFillerBetaFamilyContextEncodedType EncodedType.nat

theorem compactFillerBetaFamilyIndexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactFillerBetaFamilyInstructionEncodedType
      compactFillerBetaFamilyIndexInstruction := by
  simpa [compactFillerBetaFamilyInstructionEncodedType,
    compactFillerBetaFamilyIndexInstruction] using
    TMPolyTimeMap.inr compactFillerBetaFamilyContextEncodedType EncodedType.nat

theorem compactFillerBetaFamilyInstructions_tm_polytime :
    TMPolyTimeMap
      compactFillerBetaFamilyInputEncodedType
      compactFillerBetaFamilyInstructionListEncodedType
      compactFillerBetaFamilyInstructions := by
  let X := compactFillerBetaFamilyInputEncodedType
  have hCtx : TMPolyTimeMap X compactFillerBetaFamilyContextEncodedType (fun p : X.Carrier => p) :=
    TMPolyTimeMap.id X
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType))
        (fun p : X.Carrier => p.2) := by
    simpa [X, compactFillerBetaFamilyInputEncodedType,
      compactFillerBetaFamilyContextEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType))
  have hSetPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
        (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hSetCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hSetPayload
    simpa [Function.comp, X] using hComp
  have hInit :
      TMPolyTimeMap X compactFillerBetaFamilyInstructionEncodedType
        (fun p : X.Carrier => compactFillerBetaFamilyInitInstruction p) := by
    have hComp := TMPolyTimeMap.comp compactFillerBetaFamilyInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => List.range p.2.2.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hSetCount
    simpa [Function.comp, X] using hComp
  have hIndexInstructions :
      TMPolyTimeMap X compactFillerBetaFamilyInstructionListEncodedType
        (fun p : X.Carrier => (List.range p.2.2.1).map
          compactFillerBetaFamilyIndexInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactFillerBetaFamilyIndexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, compactFillerBetaFamilyInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactFillerBetaFamilyInstructionEncodedType
          compactFillerBetaFamilyInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactFillerBetaFamilyInitInstruction p,
            (List.range p.2.2.1).map compactFillerBetaFamilyIndexInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hIndexInstructions
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons compactFillerBetaFamilyInstructionEncodedType)
      hConsInput
  simpa [Function.comp, compactFillerBetaFamilyInstructions,
    compactFillerBetaFamilyInstructionListEncodedType, X] using hCons

theorem compactFillerBetaFamilyStepLeft_tm_polytime :
    TMPolyTimeMap
      compactFillerBetaFamilyContextEncodedType
      compactFillerBetaFamilyAccEncodedType
      (fun ctx : CompactFillerBetaFamilyContext =>
        (ctx, ([] : List (Nat × Nat × Nat)))) := by
  have hCtx := TMPolyTimeMap.id compactFillerBetaFamilyContextEncodedType
  have hEmpty :
      TMPolyTimeMap compactFillerBetaFamilyContextEncodedType tripleListStructuredEncodedType
        (fun _ : CompactFillerBetaFamilyContext => ([] : List (Nat × Nat × Nat))) :=
    TMPolyTimeMap.const compactFillerBetaFamilyContextEncodedType
      tripleListStructuredEncodedType []
  simpa [compactFillerBetaFamilyAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hEmpty

theorem compactFillerBetaFamilyIndexStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactFillerBetaFamilyAccEncodedType EncodedType.nat)
      compactFillerBetaFamilyAccEncodedType
      compactFillerBetaFamilyIndexStep := by
  let X := EncodedType.prod compactFillerBetaFamilyAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactFillerBetaFamilyAccEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactFillerBetaFamilyAccEncodedType EncodedType.nat
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactFillerBetaFamilyAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X compactFillerBetaFamilyContextEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst compactFillerBetaFamilyContextEncodedType
      tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactFillerBetaFamilyAccEncodedType, X] using hComp
  have hOut : TMPolyTimeMap X tripleListStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd compactFillerBetaFamilyContextEncodedType
      tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactFillerBetaFamilyAccEncodedType, X] using hComp
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, compactFillerBetaFamilyContextEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType))
        (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, compactFillerBetaFamilyContextEncodedType, X] using hComp
  have hBeta : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hSetPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
        (fun p : X.Carrier => p.1.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hSetPayload
    simpa [Function.comp, X] using hComp
  have hLookupInput :
      TMPolyTimeMap X (EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.1.1.2.2.2, p.2)) :=
    TMPolyTimeMap.prod_mk hSets hJ
  have hSet :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : X.Carrier => SteinerTree.setFamilyGetD (p.1.1.2.2.2, p.2)) := by
    have hComp := TMPolyTimeMap.comp SteinerTree.setFamilyGetD_tm_polytime hLookupInput
    simpa [Function.comp, X] using hComp
  have hBlockInput :
      TMPolyTimeMap X compactFillerBlockInputEncodedType
        (fun p : X.Carrier =>
          (p.1.1.1, p.1.1.2.1, p.2, SteinerTree.setFamilyGetD (p.1.1.2.2.2, p.2))) := by
    have hInner :
        TMPolyTimeMap X (EncodedType.prod EncodedType.nat setStructuredEncodedType)
          (fun p : X.Carrier => (p.2, SteinerTree.setFamilyGetD (p.1.1.2.2.2, p.2))) :=
      TMPolyTimeMap.prod_mk hJ hSet
    simpa [compactFillerBlockInputEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse (TMPolyTimeMap.prod_mk hBeta hInner)
  have hBlock :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier =>
          compactFillerTriplesForSourceSetExecutable
            (p.1.1.1, p.1.1.2.1, p.2,
              SteinerTree.setFamilyGetD (p.1.1.2.2.2, p.2))) := by
    have hComp := TMPolyTimeMap.comp
      compactFillerTriplesForSourceSetExecutable_tm_polytime hBlockInput
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show List (Nat × Nat × Nat) from p.1.2),
            compactFillerTriplesForSourceSetExecutable
              (p.1.1.1, p.1.1.2.1, p.2,
                SteinerTree.setFamilyGetD (p.1.1.2.2.2, p.2)))) :=
    TMPolyTimeMap.prod_mk hOut hBlock
  have hAppend :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat × Nat) from p.1.2) ++
            compactFillerTriplesForSourceSetExecutable
              (p.1.1.1, p.1.1.2.1, p.2,
                SteinerTree.setFamilyGetD (p.1.1.2.2.2, p.2))) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append tripleStructuredEncodedType) hAppendInput
    simpa [Function.comp, tripleListStructuredEncodedType, X] using hComp
  have hPair := TMPolyTimeMap.prod_mk hCtx hAppend
  simpa [compactFillerBetaFamilyIndexStep, compactFillerBetaFamilyAccEncodedType, X] using hPair

theorem compactFillerBetaFamilyStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactFillerBetaFamilyAccEncodedType
        compactFillerBetaFamilyInstructionEncodedType)
      compactFillerBetaFamilyAccEncodedType
      compactFillerBetaFamilyStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      compactFillerBetaFamilyAccEncodedType compactFillerBetaFamilyContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim compactFillerBetaFamilyStepLeft_tm_polytime
      compactFillerBetaFamilyIndexStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def compactFillerBetaFamilyFoldInv
    (N : Nat) (acc : compactFillerBetaFamilyAccEncodedType.Carrier) : Prop :=
  acc = compactFillerBetaFamilyInitAcc ∨
    ((show Nat from acc.1.1) + 1 ≤ N ∧
      (show Nat from acc.1.2.1) + 1 ≤ N ∧
      (show Nat from acc.1.2.2.1) + 1 ≤ N ∧
      setFamilyStructuredEncodedType.inputSize
        (show List (List Nat) from acc.1.2.2.2) ≤ N)

theorem compactFillerBetaFamilyInitAcc_bound
    (xs : List compactFillerBetaFamilyInstructionEncodedType.Carrier) :
    compactFillerBetaFamilyFoldInv
        (compactFillerBetaFamilyInstructionListEncodedType.inputSize xs)
        compactFillerBetaFamilyInitAcc ∧
      compactFillerBetaFamilyAccEncodedType.inputSize compactFillerBetaFamilyInitAcc ≤
        (Polynomial.C 10).eval
          (compactFillerBetaFamilyInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · have hNilTriples :
        tripleStructuredEncodedType.list.inputSize ([] : List (Nat × Nat × Nat)) = 0 :=
      EncodedType.inputSize_list_nil tripleStructuredEncodedType
    have hNilSets :
        setStructuredEncodedType.list.inputSize ([] : List (List Nat)) = 0 :=
      EncodedType.inputSize_list_nil setStructuredEncodedType
    simp [compactFillerBetaFamilyInitAcc, compactFillerBetaFamilyAccEncodedType,
      compactFillerBetaFamilyContextEncodedType, tripleListStructuredEncodedType,
      setFamilyStructuredEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat, hNilTriples, hNilSets]

theorem compactFillerBetaFamilyStep_growth
    (source : List compactFillerBetaFamilyInstructionEncodedType.Carrier)
    (acc : compactFillerBetaFamilyAccEncodedType.Carrier)
    (instr : compactFillerBetaFamilyInstructionEncodedType.Carrier)
    (hInv :
      compactFillerBetaFamilyFoldInv
        (compactFillerBetaFamilyInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactFillerBetaFamilyInstructionEncodedType.inputSize instr ≤
        compactFillerBetaFamilyInstructionListEncodedType.inputSize source) :
    compactFillerBetaFamilyFoldInv
        (compactFillerBetaFamilyInstructionListEncodedType.inputSize source)
        (compactFillerBetaFamilyStep (acc, instr)) ∧
      compactFillerBetaFamilyAccEncodedType.inputSize
          (compactFillerBetaFamilyStep (acc, instr)) ≤
        compactFillerBetaFamilyAccEncodedType.inputSize acc +
          (Polynomial.C 50 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
            Polynomial.C 50).eval
            (compactFillerBetaFamilyInstructionListEncodedType.inputSize source) := by
  let N := compactFillerBetaFamilyInstructionListEncodedType.inputSize source
  rcases acc with ⟨ctx, out⟩
  rcases ctx with ⟨universeSize, beta, setCount, sets⟩
  change Nat at universeSize
  change Nat at beta
  change Nat at setCount
  cases instr with
  | inl newCtx =>
      rcases newCtx with ⟨newUniverse, newBeta, newSetCount, newSets⟩
      change Nat at newUniverse
      change Nat at newBeta
      change Nat at newSetCount
      have hCtx :
          compactFillerBetaFamilyContextEncodedType.inputSize
              (newUniverse, newBeta, newSetCount, newSets) + 1 ≤ N := by
        simpa [N, compactFillerBetaFamilyInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hInstr
      have hNewUniverse : newUniverse + 1 ≤ N := by
        simp [compactFillerBetaFamilyContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewBeta : newBeta + 1 ≤ N := by
        simp [compactFillerBetaFamilyContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewSetCount : newSetCount + 1 ≤ N := by
        simp [compactFillerBetaFamilyContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewSets : setFamilyStructuredEncodedType.inputSize newSets ≤ N := by
        simp [compactFillerBetaFamilyContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      constructor
      · exact Or.inr ⟨hNewUniverse, hNewBeta, hNewSetCount, hNewSets⟩
      · have hNilTriples :
            tripleStructuredEncodedType.list.inputSize ([] : List (Nat × Nat × Nat)) = 0 :=
          EncodedType.inputSize_list_nil tripleStructuredEncodedType
        have hNewAcc :
            compactFillerBetaFamilyAccEncodedType.inputSize
                ((newUniverse, newBeta, newSetCount, newSets),
                  ([] : List (Nat × Nat × Nat))) ≤ N := by
          simpa [compactFillerBetaFamilyAccEncodedType,
            compactFillerBetaFamilyContextEncodedType, tripleListStructuredEncodedType,
            EncodedType.inputSize_prod, EncodedType.inputSize_nat, hNilTriples] using hCtx
        have hPolyN :
            N ≤ compactFillerBetaFamilyAccEncodedType.inputSize
                ((universeSize, beta, setCount, sets), out) +
              (Polynomial.C 50 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
                Polynomial.C 50).eval N := by
          have hBase :
              N ≤
                (Polynomial.C 50 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
                  Polynomial.C 50).eval N := by
            have hN : 1 ≤ N := by omega
            have hN2 : N ≤ N * N := Nat.le_mul_of_pos_right N hN
            have hN3 : N * N ≤ N * (N * N) := Nat.mul_le_mul_left N hN2
            have hNle3 : N ≤ N * (N * N) := hN2.trans hN3
            simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
            omega
          exact hBase.trans (Nat.le_add_left _ _)
        simpa [compactFillerBetaFamilyStep, N] using
          hNewAcc.trans (by simpa [N] using hPolyN)
  | inr j =>
      change Nat at j
      have hj : j + 1 ≤ N := by
        have hjTagged : j + 1 < N := by
          simpa [N, compactFillerBetaFamilyInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, EncodedType.nat] using hInstr
        omega
      have hBounds :
          universeSize + 1 ≤ N ∧ beta + 1 ≤ N ∧ setCount + 1 ≤ N ∧
            setFamilyStructuredEncodedType.inputSize sets ≤ N := by
        rcases hInv with hInit | hBound
        · injection hInit with hCtxEq _hOut
          injection hCtxEq with hUniverse hTail
          injection hTail with hBeta hTail2
          injection hTail2 with hSetCount hSets
          subst universeSize
          subst beta
          subst setCount
          subst sets
          have hNil : setFamilyStructuredEncodedType.inputSize ([] : List (List Nat)) = 0 := rfl
          omega
        · exact hBound
      let S := SteinerTree.setFamilyGetD (sets, j)
      let block := compactFillerTriplesForSourceSetExecutable (universeSize, beta, j, S)
      have hBlock :
          tripleListStructuredEncodedType.inputSize block ≤ 50 * (N * (N * N)) + 50 := by
        simpa [block, S] using
          compactFillerTriplesForSourceSetExecutable_inputSize_le
            N universeSize beta j S hBounds.1 hBounds.2.1 hj
      have hAppendSize :
          tripleListStructuredEncodedType.inputSize
              ((show List (Nat × Nat × Nat) from out) ++ block) =
            tripleListStructuredEncodedType.inputSize out +
              tripleListStructuredEncodedType.inputSize block := by
        simpa [tripleListStructuredEncodedType] using
          list_inputSize_append tripleStructuredEncodedType out block
      have hAppendLe :
          tripleListStructuredEncodedType.inputSize
              ((show List (Nat × Nat × Nat) from out) ++ block) ≤
            tripleListStructuredEncodedType.inputSize out + (50 * (N * (N * N)) + 50) := by
        rw [hAppendSize]
        exact Nat.add_le_add_left hBlock _
      constructor
      · exact Or.inr hBounds
      · change
          compactFillerBetaFamilyAccEncodedType.inputSize
              ((universeSize, beta, setCount, sets),
                (show List (Nat × Nat × Nat) from out) ++ block) ≤
            compactFillerBetaFamilyAccEncodedType.inputSize
                ((universeSize, beta, setCount, sets), out) +
              (Polynomial.C 50 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
                Polynomial.C 50).eval N
        simp [compactFillerBetaFamilyAccEncodedType, EncodedType.inputSize_prod,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hAppendLe ⊢
        omega

theorem compactFillerBetaFamilyFold_tm_polytime :
    TMPolyTimeMap
      compactFillerBetaFamilyInstructionListEncodedType
      compactFillerBetaFamilyAccEncodedType
      (fun xs : List compactFillerBetaFamilyInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactFillerBetaFamilyStep (acc, instr))
          compactFillerBetaFamilyInitAcc) := by
  rcases compactFillerBetaFamilyStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactFillerBetaFamilyInstructionEncodedType compactFillerBetaFamilyAccEncodedType
      compactFillerBetaFamilyStep compactFillerBetaFamilyInitAcc hStep
      (Polynomial.C 10)
      (Polynomial.C 50 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
        Polynomial.C 50)
      compactFillerBetaFamilyFoldInv ?_ ?_
  · intro xs
    exact compactFillerBetaFamilyInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactFillerBetaFamilyStep_growth source acc instr hInv hInstr

theorem compactFillerBetaFamilyFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactFillerBetaFamilyInstructionListEncodedType
      tripleListStructuredEncodedType
      compactFillerBetaFamilyFromInstructions := by
  have hFold := compactFillerBetaFamilyFold_tm_polytime
  have hSnd :=
    TMPolyTimeMap.snd compactFillerBetaFamilyContextEncodedType tripleListStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, compactFillerBetaFamilyFromInstructions,
    compactFillerBetaFamilyAccEncodedType] using hComp

theorem compactFillerTriplesForBetaExecutable_tm_polytime :
    TMPolyTimeMap
      compactFillerBetaFamilyInputEncodedType
      tripleListStructuredEncodedType
      compactFillerTriplesForBetaExecutable := by
  have hComp :=
    TMPolyTimeMap.comp compactFillerBetaFamilyFromInstructions_tm_polytime
      compactFillerBetaFamilyInstructions_tm_polytime
  simpa [Function.comp, compactFillerTriplesForBetaExecutable] using hComp

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
