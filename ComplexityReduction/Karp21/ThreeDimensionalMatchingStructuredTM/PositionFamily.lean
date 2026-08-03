/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.PositionBlocks
import ComplexityReduction.Karp21.SteinerTreeStructuredTM.Lookup

/-!
Family-level membership-position code assembly for the compact
Exact-Cover-to-3-Dimensional-Matching route.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactPositionFamilyContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)

def compactPositionFamilyAccEncodedType : EncodedType :=
  EncodedType.prod compactPositionFamilyContextEncodedType compactPositionCodeListEncodedType

def compactPositionFamilyInstructionEncodedType : EncodedType :=
  EncodedType.sum compactPositionFamilyContextEncodedType EncodedType.nat

def compactPositionFamilyInstructionListEncodedType : EncodedType :=
  EncodedType.list compactPositionFamilyInstructionEncodedType

def compactPositionFamilyInputEncodedType : EncodedType :=
  compactPositionFamilyContextEncodedType

abbrev CompactPositionFamilyContext := Nat × Nat × List (List Nat)
abbrev CompactPositionFamilyAcc := CompactPositionFamilyContext × List Nat

def compactPositionFamilyInitAcc : CompactPositionFamilyAcc :=
  ((0, (0, [])), [])

def compactPositionFamilyInitInstruction (ctx : CompactPositionFamilyContext) :
    compactPositionFamilyInstructionEncodedType.Carrier :=
  Sum.inl ctx

def compactPositionFamilyIndexInstruction (j : Nat) :
    compactPositionFamilyInstructionEncodedType.Carrier :=
  Sum.inr j

def compactPositionFamilyInstructions (p : CompactPositionFamilyContext) :
    List compactPositionFamilyInstructionEncodedType.Carrier :=
  compactPositionFamilyInitInstruction p ::
    (List.range p.2.1).map compactPositionFamilyIndexInstruction

def compactPositionFamilyIndexStep (p : CompactPositionFamilyAcc × Nat) :
    CompactPositionFamilyAcc :=
  let ctx := p.1.1
  let out := p.1.2
  let j := p.2
  let S := SteinerTree.setFamilyGetD (ctx.2.2, j)
  (ctx, out ++ compactPositionCodesForSourceSetExecutable (ctx.1, j, S))

def compactPositionFamilyStep
    (p : CompactPositionFamilyAcc × compactPositionFamilyInstructionEncodedType.Carrier) :
    CompactPositionFamilyAcc :=
  match p.2 with
  | Sum.inl ctx => (ctx, [])
  | Sum.inr j => compactPositionFamilyIndexStep (p.1, j)

def compactPositionFamilyFromInstructions
    (xs : List compactPositionFamilyInstructionEncodedType.Carrier) : List Nat :=
  (xs.foldl (fun acc instr => compactPositionFamilyStep (acc, instr))
    compactPositionFamilyInitAcc).2

def compactPositionCodesExecutable (p : CompactPositionFamilyContext) : List Nat :=
  compactPositionFamilyFromInstructions (compactPositionFamilyInstructions p)

/-! ### Semantics -/

theorem compactPositionFamilyIndexFold_eq_append_flatMap
    (ctx : CompactPositionFamilyContext) (xs : List Nat) (out : List Nat) :
    ((xs.map compactPositionFamilyIndexInstruction).foldl
        (fun acc instr => compactPositionFamilyStep (acc, instr)) (ctx, out)).2 =
      out ++ xs.flatMap (fun j =>
        compactPositionCodesForSourceSetExecutable
          (ctx.1, j, SteinerTree.setFamilyGetD (ctx.2.2, j))) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons j js ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [compactPositionFamilyIndexInstruction, compactPositionFamilyStep,
        compactPositionFamilyIndexStep]
      have hTail := ih (out ++
        compactPositionCodesForSourceSetExecutable
          (ctx.1, j, SteinerTree.setFamilyGetD (ctx.2.2, j)))
      simpa [List.append_assoc] using hTail

theorem compactPositionCodesExecutable_eq_flatMap
    (p : CompactPositionFamilyContext) :
    compactPositionCodesExecutable p =
      (List.range p.2.1).flatMap (fun j =>
        compactPositionCodesForSourceSetExecutable
          (p.1, j, SteinerTree.setFamilyGetD (p.2.2, j))) := by
  change
    (((List.range p.2.1).map compactPositionFamilyIndexInstruction).foldl
        (fun acc instr => compactPositionFamilyStep (acc, instr)) (p, [])).2 =
      (List.range p.2.1).flatMap (fun j =>
        compactPositionCodesForSourceSetExecutable
          (p.1, j, SteinerTree.setFamilyGetD (p.2.2, j)))
  simpa using compactPositionFamilyIndexFold_eq_append_flatMap p (List.range p.2.1) []

theorem compactPositionCodesExecutable_eq_compactPositionCodes_tail (I : ExactCoverInput) :
    compactPositionCodesExecutable
        (I.system.universeSize, I.system.sets.length, I.system.sets) =
      (List.range I.system.sets.length).flatMap (compactPositionCodesForSet I) := by
  rw [compactPositionCodesExecutable_eq_flatMap]
  apply List.flatMap_congr
  intro j _hj
  have hGet :
      SteinerTree.setFamilyGetD (I.system.sets, j) = compactSourceSetAt I j := by
    rfl
  rw [hGet]
  exact compactPositionCodesForSourceSetExecutable_eq_compactPositionCodesForSet I j

theorem compactPositionCodesExecutable_eq_compactPositionCodes (I : ExactCoverInput) :
    compactPositionCodesExecutable
        (I.system.universeSize, I.system.sets.length, I.system.sets) =
      compactPositionCodes I := by
  simpa [compactPositionCodes] using compactPositionCodesExecutable_eq_compactPositionCodes_tail I

/-! ### Local size facts for the fold -/

theorem compactPosition_mem_compactSupportExecutable_lt {bound : Nat} {S : List Nat} {x : Nat}
    (hx : x ∈ compactSupportExecutable (bound, S)) :
    x < bound := by
  rw [compactSupportExecutable_eq_filter] at hx
  simp only [List.mem_filter, List.mem_range] at hx
  exact hx.1

theorem compactPosition_supportExecutable_length_le (bound : Nat) (S : List Nat) :
    (compactSupportExecutable (bound, S)).length ≤ bound := by
  rw [compactSupportExecutable_eq_filter]
  exact (List.length_filter_le _ _).trans_eq (by simp)

theorem compactPositionCodeFromCounts_inputSize_le
    (N universeSize x j : Nat)
    (hUniverse : universeSize + 1 ≤ N) (hj : j + 1 ≤ N) (hx : x + 2 ≤ N) :
    EncodedType.nat.inputSize (compactPositionCodeFromCounts (universeSize, x, j)) ≤
      4 * (N * N) + 10 := by
  have hUniverseLe : universeSize ≤ N := by omega
  have hJLe : j ≤ N := by omega
  have hXLe : x ≤ N := by omega
  have hProduct : j * universeSize ≤ N * N :=
    Nat.mul_le_mul hJLe hUniverseLe
  have hCode : compactPositionCodeFromCounts (universeSize, x, j) ≤ 2 * (N * N) := by
    simp [compactPositionCodeFromCounts]
    nlinarith [hProduct, hXLe, sq_nonneg (N : Int)]
  simp [EncodedType.inputSize_nat]
  nlinarith [hCode, sq_nonneg (N : Int)]

theorem compactPositionCodesForSourceSetExecutable_inputSize_le
    (N universeSize j : Nat) (S : List Nat)
    (hUniverse : universeSize + 1 ≤ N) (hj : j + 1 ≤ N) :
    compactPositionCodeListEncodedType.inputSize
        (compactPositionCodesForSourceSetExecutable (universeSize, j, S)) ≤
      10 * (N * (N * N)) + 10 := by
  let block := compactPositionCodesForSourceSetExecutable (universeSize, j, S)
  have hLen : block.length ≤ N := by
    have hSupport := compactPosition_supportExecutable_length_le universeSize S
    dsimp [block]
    rw [compactPositionCodesForSourceSetExecutable_eq_map]
    simp
    omega
  have hEach :
      ∀ c ∈ block, EncodedType.nat.inputSize c ≤ 4 * (N * N) + 10 := by
    intro c hc
    dsimp [block] at hc
    rw [compactPositionCodesForSourceSetExecutable_eq_map] at hc
    simp only [List.mem_map] at hc
    rcases hc with ⟨x, hx, rfl⟩
    have hxLt := compactPosition_mem_compactSupportExecutable_lt hx
    have hxN : x + 2 ≤ N := by omega
    exact compactPositionCodeFromCounts_inputSize_le N universeSize x j hUniverse hj hxN
  have hList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      EncodedType.nat block (4 * (N * N) + 10) hEach
  have hPoly :
      block.length * (4 * (N * N) + 10 + 1) ≤
        10 * (N * (N * N)) + 10 := by
    have hN : 1 ≤ N := by omega
    have hN2 : N ≤ N * N := Nat.le_mul_of_pos_right N hN
    have hN3 : N * N ≤ N * (N * N) := Nat.mul_le_mul_left N hN2
    have hLenBound :
        block.length * (4 * (N * N) + 10 + 1) ≤
          N * (4 * (N * N) + 10 + 1) :=
      Nat.mul_le_mul_right _ hLen
    have hBase :
        N * (4 * (N * N) + 10 + 1) ≤
          10 * (N * (N * N)) + 10 := by
      nlinarith [hN, hN2, hN3, sq_nonneg (N : Int)]
    exact hLenBound.trans hBase
  exact hList.trans hPoly

/-! ### TM witnesses -/

theorem compactPositionFamilyInitInstruction_tm_polytime :
    TMPolyTimeMap
      compactPositionFamilyContextEncodedType
      compactPositionFamilyInstructionEncodedType
      compactPositionFamilyInitInstruction := by
  simpa [compactPositionFamilyInstructionEncodedType,
    compactPositionFamilyInitInstruction] using
    TMPolyTimeMap.inl compactPositionFamilyContextEncodedType EncodedType.nat

theorem compactPositionFamilyIndexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactPositionFamilyInstructionEncodedType
      compactPositionFamilyIndexInstruction := by
  simpa [compactPositionFamilyInstructionEncodedType,
    compactPositionFamilyIndexInstruction] using
    TMPolyTimeMap.inr compactPositionFamilyContextEncodedType EncodedType.nat

theorem compactPositionFamilyInstructions_tm_polytime :
    TMPolyTimeMap
      compactPositionFamilyInputEncodedType
      compactPositionFamilyInstructionListEncodedType
      compactPositionFamilyInstructions := by
  let X := compactPositionFamilyInputEncodedType
  have hCtx : TMPolyTimeMap X compactPositionFamilyContextEncodedType (fun p : X.Carrier => p) :=
    TMPolyTimeMap.id X
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
        (fun p : X.Carrier => p.2) := by
    simpa [X, compactPositionFamilyInputEncodedType,
      compactPositionFamilyContextEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
  have hSetCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hInit :
      TMPolyTimeMap X compactPositionFamilyInstructionEncodedType
        (fun p : X.Carrier => compactPositionFamilyInitInstruction p) := by
    have hComp := TMPolyTimeMap.comp compactPositionFamilyInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X compactPositionCodeListEncodedType
        (fun p : X.Carrier => List.range p.2.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hSetCount
    simpa [Function.comp, compactPositionCodeListEncodedType, X] using hComp
  have hIndexInstructions :
      TMPolyTimeMap X compactPositionFamilyInstructionListEncodedType
        (fun p : X.Carrier => (List.range p.2.1).map compactPositionFamilyIndexInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactPositionFamilyIndexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, compactPositionFamilyInstructionListEncodedType,
      compactPositionCodeListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactPositionFamilyInstructionEncodedType
          compactPositionFamilyInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactPositionFamilyInitInstruction p,
            (List.range p.2.1).map compactPositionFamilyIndexInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hIndexInstructions
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons compactPositionFamilyInstructionEncodedType)
      hConsInput
  simpa [Function.comp, compactPositionFamilyInstructions,
    compactPositionFamilyInstructionListEncodedType, X] using hCons

theorem compactPositionFamilyStepLeft_tm_polytime :
    TMPolyTimeMap
      compactPositionFamilyContextEncodedType
      compactPositionFamilyAccEncodedType
      (fun ctx : CompactPositionFamilyContext => (ctx, ([] : List Nat))) := by
  have hCtx := TMPolyTimeMap.id compactPositionFamilyContextEncodedType
  have hEmpty :
      TMPolyTimeMap compactPositionFamilyContextEncodedType compactPositionCodeListEncodedType
        (fun _ : CompactPositionFamilyContext => ([] : List Nat)) :=
    TMPolyTimeMap.const compactPositionFamilyContextEncodedType compactPositionCodeListEncodedType []
  simpa [compactPositionFamilyAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hEmpty

theorem compactPositionFamilyIndexStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactPositionFamilyAccEncodedType EncodedType.nat)
      compactPositionFamilyAccEncodedType
      compactPositionFamilyIndexStep := by
  let X := EncodedType.prod compactPositionFamilyAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactPositionFamilyAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactPositionFamilyAccEncodedType EncodedType.nat
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactPositionFamilyAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X compactPositionFamilyContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst compactPositionFamilyContextEncodedType
      compactPositionCodeListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactPositionFamilyAccEncodedType, X] using hComp
  have hOut : TMPolyTimeMap X compactPositionCodeListEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd compactPositionFamilyContextEncodedType
      compactPositionCodeListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactPositionFamilyAccEncodedType, X] using hComp
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, compactPositionFamilyContextEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
        (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, compactPositionFamilyContextEncodedType, X] using hComp
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hLookupInput :
      TMPolyTimeMap X (EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.1.1.2.2, p.2)) :=
    TMPolyTimeMap.prod_mk hSets hJ
  have hSet :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : X.Carrier => SteinerTree.setFamilyGetD (p.1.1.2.2, p.2)) := by
    have hComp := TMPolyTimeMap.comp SteinerTree.setFamilyGetD_tm_polytime hLookupInput
    simpa [Function.comp, X] using hComp
  have hBlockInput :
      TMPolyTimeMap X compactPositionBlockInputEncodedType
        (fun p : X.Carrier =>
          (p.1.1.1, p.2, SteinerTree.setFamilyGetD (p.1.1.2.2, p.2))) := by
    simpa [compactPositionBlockInputEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse (TMPolyTimeMap.prod_mk hJ hSet)
  have hBlock :
      TMPolyTimeMap X compactPositionCodeListEncodedType
        (fun p : X.Carrier =>
          compactPositionCodesForSourceSetExecutable
            (p.1.1.1, p.2, SteinerTree.setFamilyGetD (p.1.1.2.2, p.2))) := by
    have hComp := TMPolyTimeMap.comp
      compactPositionCodesForSourceSetExecutable_tm_polytime hBlockInput
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod compactPositionCodeListEncodedType compactPositionCodeListEncodedType)
        (fun p : X.Carrier =>
          ((show List Nat from p.1.2),
            compactPositionCodesForSourceSetExecutable
              (p.1.1.1, p.2, SteinerTree.setFamilyGetD (p.1.1.2.2, p.2)))) :=
    TMPolyTimeMap.prod_mk hOut hBlock
  have hAppend :
      TMPolyTimeMap X compactPositionCodeListEncodedType
        (fun p : X.Carrier =>
          (show List Nat from p.1.2) ++
            compactPositionCodesForSourceSetExecutable
              (p.1.1.1, p.2, SteinerTree.setFamilyGetD (p.1.1.2.2, p.2))) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append EncodedType.nat) hAppendInput
    simpa [Function.comp, compactPositionCodeListEncodedType, X] using hComp
  have hPair := TMPolyTimeMap.prod_mk hCtx hAppend
  simpa [compactPositionFamilyIndexStep, compactPositionFamilyAccEncodedType,
    compactPositionCodeListEncodedType, X] using hPair

theorem compactPositionFamilyStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactPositionFamilyAccEncodedType
        compactPositionFamilyInstructionEncodedType)
      compactPositionFamilyAccEncodedType
      compactPositionFamilyStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      compactPositionFamilyAccEncodedType compactPositionFamilyContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim compactPositionFamilyStepLeft_tm_polytime
      compactPositionFamilyIndexStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def compactPositionFamilyFoldInv
    (N : Nat) (acc : compactPositionFamilyAccEncodedType.Carrier) : Prop :=
  acc = compactPositionFamilyInitAcc ∨
    ((show Nat from acc.1.1) + 1 ≤ N ∧
      (show Nat from acc.1.2.1) + 1 ≤ N ∧
      setFamilyStructuredEncodedType.inputSize (show List (List Nat) from acc.1.2.2) ≤ N)

theorem compactPositionFamilyInitAcc_bound
    (xs : List compactPositionFamilyInstructionEncodedType.Carrier) :
    compactPositionFamilyFoldInv (compactPositionFamilyInstructionListEncodedType.inputSize xs)
        compactPositionFamilyInitAcc ∧
      compactPositionFamilyAccEncodedType.inputSize compactPositionFamilyInitAcc ≤
        (Polynomial.C 10).eval (compactPositionFamilyInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · have hNilSets :
        setStructuredEncodedType.list.inputSize ([] : List (List Nat)) = 0 :=
      EncodedType.inputSize_list_nil setStructuredEncodedType
    simp [compactPositionFamilyInitAcc, compactPositionFamilyAccEncodedType,
      compactPositionFamilyContextEncodedType, compactPositionCodeListEncodedType,
      setFamilyStructuredEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat, hNilSets]
    have hNilCodes : EncodedType.nat.list.inputSize ([] : List Nat) = 0 :=
      EncodedType.inputSize_list_nil EncodedType.nat
    rw [hNilCodes]
    norm_num

theorem compactPositionFamilyStep_growth
    (source : List compactPositionFamilyInstructionEncodedType.Carrier)
    (acc : compactPositionFamilyAccEncodedType.Carrier)
    (instr : compactPositionFamilyInstructionEncodedType.Carrier)
    (hInv :
      compactPositionFamilyFoldInv
        (compactPositionFamilyInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactPositionFamilyInstructionEncodedType.inputSize instr ≤
        compactPositionFamilyInstructionListEncodedType.inputSize source) :
    compactPositionFamilyFoldInv
        (compactPositionFamilyInstructionListEncodedType.inputSize source)
        (compactPositionFamilyStep (acc, instr)) ∧
      compactPositionFamilyAccEncodedType.inputSize (compactPositionFamilyStep (acc, instr)) ≤
        compactPositionFamilyAccEncodedType.inputSize acc +
          (Polynomial.C 10 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
            Polynomial.C 10).eval
            (compactPositionFamilyInstructionListEncodedType.inputSize source) := by
  let N := compactPositionFamilyInstructionListEncodedType.inputSize source
  rcases acc with ⟨ctx, out⟩
  rcases ctx with ⟨universeSize, setCount, sets⟩
  change Nat at universeSize
  change Nat at setCount
  cases instr with
  | inl newCtx =>
      rcases newCtx with ⟨newUniverse, newSetCount, newSets⟩
      change Nat at newUniverse
      change Nat at newSetCount
      have hCtx :
          compactPositionFamilyContextEncodedType.inputSize
              (newUniverse, newSetCount, newSets) + 1 ≤ N := by
        simpa [N, compactPositionFamilyInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hInstr
      have hNewUniverse : newUniverse + 1 ≤ N := by
        simp [compactPositionFamilyContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewSetCount : newSetCount + 1 ≤ N := by
        simp [compactPositionFamilyContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewSets : setFamilyStructuredEncodedType.inputSize newSets ≤ N := by
        simp [compactPositionFamilyContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      constructor
      · exact Or.inr ⟨hNewUniverse, hNewSetCount, hNewSets⟩
      · have hNilCodes :
            compactPositionCodeListEncodedType.inputSize ([] : List Nat) = 0 :=
          EncodedType.inputSize_list_nil EncodedType.nat
        have hNewAcc :
            compactPositionFamilyAccEncodedType.inputSize
                ((newUniverse, newSetCount, newSets), ([] : List Nat)) ≤ N := by
          simpa [compactPositionFamilyAccEncodedType, compactPositionFamilyContextEncodedType,
            compactPositionCodeListEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_nat, hNilCodes] using hCtx
        have hPolyN :
            N ≤ compactPositionFamilyAccEncodedType.inputSize ((universeSize, setCount, sets), out) +
              (Polynomial.C 10 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
                Polynomial.C 10).eval N := by
          have hBase :
              N ≤
                (Polynomial.C 10 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
                  Polynomial.C 10).eval N := by
            have hN : 1 ≤ N := by omega
            have hN2 : N ≤ N * N := Nat.le_mul_of_pos_right N hN
            have hN3 : N * N ≤ N * (N * N) := Nat.mul_le_mul_left N hN2
            simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
            omega
          exact hBase.trans (Nat.le_add_left _ _)
        simpa [compactPositionFamilyStep, N] using hNewAcc.trans (by simpa [N] using hPolyN)
  | inr j =>
      change Nat at j
      have hj : j + 1 ≤ N := by
        have hjTagged : j + 1 < N := by
          simpa [N, compactPositionFamilyInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, EncodedType.nat] using hInstr
        omega
      have hBounds :
          universeSize + 1 ≤ N ∧ setCount + 1 ≤ N ∧
            setFamilyStructuredEncodedType.inputSize sets ≤ N := by
        rcases hInv with hInit | hBound
        · injection hInit with hCtxEq _hOut
          injection hCtxEq with hUniverse hTail
          injection hTail with hSetCount hSets
          subst universeSize
          subst setCount
          subst sets
          have hNil : setFamilyStructuredEncodedType.inputSize ([] : List (List Nat)) = 0 := rfl
          omega
        · exact hBound
      let S := SteinerTree.setFamilyGetD (sets, j)
      let block := compactPositionCodesForSourceSetExecutable (universeSize, j, S)
      have hBlock :
          compactPositionCodeListEncodedType.inputSize block ≤
            10 * (N * (N * N)) + 10 := by
        simpa [block, S] using
          compactPositionCodesForSourceSetExecutable_inputSize_le
            N universeSize j S hBounds.1 hj
      have hAppendSize :
          compactPositionCodeListEncodedType.inputSize
              ((show List Nat from out) ++ block) =
            compactPositionCodeListEncodedType.inputSize out +
              compactPositionCodeListEncodedType.inputSize block := by
        simpa [compactPositionCodeListEncodedType] using
          list_inputSize_append EncodedType.nat out block
      have hAppendLe :
          compactPositionCodeListEncodedType.inputSize
              ((show List Nat from out) ++ block) ≤
            compactPositionCodeListEncodedType.inputSize out +
              (10 * (N * (N * N)) + 10) := by
        rw [hAppendSize]
        exact Nat.add_le_add_left hBlock _
      constructor
      · exact Or.inr hBounds
      · change
          compactPositionFamilyAccEncodedType.inputSize
              ((universeSize, setCount, sets), (show List Nat from out) ++ block) ≤
            compactPositionFamilyAccEncodedType.inputSize ((universeSize, setCount, sets), out) +
              (Polynomial.C 10 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
                Polynomial.C 10).eval N
        simp [compactPositionFamilyAccEncodedType, compactPositionCodeListEncodedType,
          EncodedType.inputSize_prod, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_X] at hAppendLe ⊢
        omega

theorem compactPositionFamilyFold_tm_polytime :
    TMPolyTimeMap
      compactPositionFamilyInstructionListEncodedType
      compactPositionFamilyAccEncodedType
      (fun xs : List compactPositionFamilyInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactPositionFamilyStep (acc, instr))
          compactPositionFamilyInitAcc) := by
  rcases compactPositionFamilyStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactPositionFamilyInstructionEncodedType compactPositionFamilyAccEncodedType
      compactPositionFamilyStep compactPositionFamilyInitAcc hStep
      (Polynomial.C 10)
      (Polynomial.C 10 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
        Polynomial.C 10)
      compactPositionFamilyFoldInv ?_ ?_
  · intro xs
    exact compactPositionFamilyInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactPositionFamilyStep_growth source acc instr hInv hInstr

theorem compactPositionFamilyFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactPositionFamilyInstructionListEncodedType
      compactPositionCodeListEncodedType
      compactPositionFamilyFromInstructions := by
  have hFold := compactPositionFamilyFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd compactPositionFamilyContextEncodedType
    compactPositionCodeListEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, compactPositionFamilyFromInstructions,
    compactPositionFamilyAccEncodedType] using hComp

theorem compactPositionCodesExecutable_tm_polytime :
    TMPolyTimeMap
      compactPositionFamilyInputEncodedType
      compactPositionCodeListEncodedType
      compactPositionCodesExecutable := by
  have hComp :=
    TMPolyTimeMap.comp compactPositionFamilyFromInstructions_tm_polytime
      compactPositionFamilyInstructions_tm_polytime
  simpa [Function.comp, compactPositionCodesExecutable] using hComp

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
