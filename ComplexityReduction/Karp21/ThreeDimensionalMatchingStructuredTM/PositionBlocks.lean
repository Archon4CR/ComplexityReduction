/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.PositionCodes
import ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold

/-!
Executable membership-position code blocks for one source set in the compact
Exact-Cover-to-3-Dimensional-Matching route.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactPositionCodeListEncodedType : EncodedType :=
  EncodedType.list EncodedType.nat

def compactPositionBlockContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

def compactPositionBlockAccEncodedType : EncodedType :=
  EncodedType.prod compactPositionBlockContextEncodedType compactPositionCodeListEncodedType

def compactPositionBlockInstructionEncodedType : EncodedType :=
  EncodedType.sum compactPositionBlockContextEncodedType EncodedType.nat

def compactPositionBlockInstructionListEncodedType : EncodedType :=
  EncodedType.list compactPositionBlockInstructionEncodedType

def compactPositionBlockInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat setStructuredEncodedType)

abbrev CompactPositionBlockContext := Nat × Nat
abbrev CompactPositionBlockAcc := CompactPositionBlockContext × List Nat

def compactPositionBlockInitAcc : CompactPositionBlockAcc :=
  ((0, 0), [])

def compactPositionBlockInitInstruction (ctx : CompactPositionBlockContext) :
    compactPositionBlockInstructionEncodedType.Carrier :=
  Sum.inl ctx

def compactPositionBlockElementInstruction (x : Nat) :
    compactPositionBlockInstructionEncodedType.Carrier :=
  Sum.inr x

def compactPositionBlockInstructions (p : Nat × Nat × List Nat) :
    List compactPositionBlockInstructionEncodedType.Carrier :=
  compactPositionBlockInitInstruction (p.1, p.2.1) ::
    (compactSupportExecutable (p.1, p.2.2)).map compactPositionBlockElementInstruction

def compactPositionBlockElementStep (p : CompactPositionBlockAcc × Nat) :
    CompactPositionBlockAcc :=
  let ctx := p.1.1
  let out := p.1.2
  let x := p.2
  let code := compactPositionCodeFromCounts (ctx.1, x, ctx.2)
  (ctx, out ++ [code])

def compactPositionBlockStep
    (p : CompactPositionBlockAcc × compactPositionBlockInstructionEncodedType.Carrier) :
    CompactPositionBlockAcc :=
  match p.2 with
  | Sum.inl ctx => (ctx, [])
  | Sum.inr x => compactPositionBlockElementStep (p.1, x)

def compactPositionBlockFromInstructions
    (xs : List compactPositionBlockInstructionEncodedType.Carrier) : List Nat :=
  (xs.foldl (fun acc instr => compactPositionBlockStep (acc, instr))
    compactPositionBlockInitAcc).2

def compactPositionCodesForSourceSetExecutable (p : Nat × Nat × List Nat) : List Nat :=
  compactPositionBlockFromInstructions (compactPositionBlockInstructions p)

/-! ### Semantics -/

theorem compactPositionBlockElementFold_eq_append_map
    (ctx : CompactPositionBlockContext) (xs : List Nat) (out : List Nat) :
    ((xs.map compactPositionBlockElementInstruction).foldl
        (fun acc instr => compactPositionBlockStep (acc, instr)) (ctx, out)).2 =
      out ++ xs.map (fun x => compactPositionCodeFromCounts (ctx.1, x, ctx.2)) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [compactPositionBlockElementInstruction, compactPositionBlockStep,
        compactPositionBlockElementStep]
      have hTail := ih (out ++ [compactPositionCodeFromCounts (ctx.1, x, ctx.2)])
      simpa [List.append_assoc] using hTail

theorem compactPositionCodesForSourceSetExecutable_eq_map
    (p : Nat × Nat × List Nat) :
    compactPositionCodesForSourceSetExecutable p =
      (compactSupportExecutable (p.1, p.2.2)).map
        (fun x => compactPositionCodeFromCounts (p.1, x, p.2.1)) := by
  change
    (((compactSupportExecutable (p.1, p.2.2)).map
        compactPositionBlockElementInstruction).foldl
        (fun acc instr => compactPositionBlockStep (acc, instr))
        ((p.1, p.2.1), [])).2 =
      (compactSupportExecutable (p.1, p.2.2)).map
        (fun x => compactPositionCodeFromCounts (p.1, x, p.2.1))
  simpa using
    compactPositionBlockElementFold_eq_append_map
      (p.1, p.2.1) (compactSupportExecutable (p.1, p.2.2)) []

theorem compactPositionCodesForSourceSetExecutable_eq_compactPositionCodesForSet
    (I : ExactCoverInput) (j : Nat) :
    compactPositionCodesForSourceSetExecutable
        (I.system.universeSize, j, compactSourceSetAt I j) =
      compactPositionCodesForSet I j := by
  rw [compactPositionCodesForSourceSetExecutable_eq_map]
  rw [compactSupportExecutable_eq_compactSupport]
  unfold compactPositionCodesForSet
  rfl

/-! ### TM witnesses for one source-set position-code block -/

theorem compactPositionBlockInitInstruction_tm_polytime :
    TMPolyTimeMap
      compactPositionBlockContextEncodedType
      compactPositionBlockInstructionEncodedType
      compactPositionBlockInitInstruction := by
  simpa [compactPositionBlockInstructionEncodedType,
    compactPositionBlockInitInstruction] using
    TMPolyTimeMap.inl compactPositionBlockContextEncodedType EncodedType.nat

theorem compactPositionBlockElementInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactPositionBlockInstructionEncodedType
      compactPositionBlockElementInstruction := by
  simpa [compactPositionBlockInstructionEncodedType,
    compactPositionBlockElementInstruction] using
    TMPolyTimeMap.inr compactPositionBlockContextEncodedType EncodedType.nat

theorem compactPositionBlockInstructions_tm_polytime :
    TMPolyTimeMap
      compactPositionBlockInputEncodedType
      compactPositionBlockInstructionListEncodedType
      compactPositionBlockInstructions := by
  let X := compactPositionBlockInputEncodedType
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, compactPositionBlockInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat setStructuredEncodedType)
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setStructuredEncodedType)
        (fun p : X.Carrier => p.2) := by
    simpa [X, compactPositionBlockInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat setStructuredEncodedType)
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hSet : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hCtx :
      TMPolyTimeMap X compactPositionBlockContextEncodedType
        (fun p : X.Carrier => (p.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hUniverse hJ
  have hInit :
      TMPolyTimeMap X compactPositionBlockInstructionEncodedType
        (fun p : X.Carrier => compactPositionBlockInitInstruction (p.1, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp compactPositionBlockInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hSupportInput :
      TMPolyTimeMap X compactSupportInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hUniverse hSet
  have hSupport :
      TMPolyTimeMap X compactPositionCodeListEncodedType
        (fun p : X.Carrier => compactSupportExecutable (p.1, p.2.2)) := by
    have hComp := TMPolyTimeMap.comp compactSupportExecutable_tm_polytime hSupportInput
    simpa [Function.comp, compactPositionCodeListEncodedType, X] using hComp
  have hMapped :
      TMPolyTimeMap X compactPositionBlockInstructionListEncodedType
        (fun p : X.Carrier =>
          (compactSupportExecutable (p.1, p.2.2)).map
            compactPositionBlockElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactPositionBlockElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hSupport
    simpa [Function.comp, compactPositionBlockInstructionListEncodedType,
      compactPositionCodeListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactPositionBlockInstructionEncodedType
          compactPositionBlockInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactPositionBlockInitInstruction (p.1, p.2.1),
            (compactSupportExecutable (p.1, p.2.2)).map
              compactPositionBlockElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMapped
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons compactPositionBlockInstructionEncodedType) hConsInput
  simpa [Function.comp, compactPositionBlockInstructions,
    compactPositionBlockInstructionListEncodedType, X] using hCons

theorem compactPositionBlockStepLeft_tm_polytime :
    TMPolyTimeMap
      compactPositionBlockContextEncodedType
      compactPositionBlockAccEncodedType
      (fun ctx : CompactPositionBlockContext => (ctx, ([] : List Nat))) := by
  have hCtx := TMPolyTimeMap.id compactPositionBlockContextEncodedType
  have hEmpty :
      TMPolyTimeMap compactPositionBlockContextEncodedType compactPositionCodeListEncodedType
        (fun _ : CompactPositionBlockContext => ([] : List Nat)) :=
    TMPolyTimeMap.const compactPositionBlockContextEncodedType
      compactPositionCodeListEncodedType []
  simpa [compactPositionBlockAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hEmpty

theorem compactPositionBlockElementStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactPositionBlockAccEncodedType EncodedType.nat)
      compactPositionBlockAccEncodedType
      compactPositionBlockElementStep := by
  let X := EncodedType.prod compactPositionBlockAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactPositionBlockAccEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactPositionBlockAccEncodedType EncodedType.nat
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactPositionBlockAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X compactPositionBlockContextEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst compactPositionBlockContextEncodedType
      compactPositionCodeListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactPositionBlockAccEncodedType, X] using hComp
  have hOut : TMPolyTimeMap X compactPositionCodeListEncodedType
      (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd compactPositionBlockContextEncodedType
      compactPositionCodeListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactPositionBlockAccEncodedType, X] using hComp
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, compactPositionBlockContextEncodedType, X] using hComp
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, compactPositionBlockContextEncodedType, X] using hComp
  have hCodeInput :
      TMPolyTimeMap X compactPositionCodeInputEncodedType
        (fun p : X.Carrier => (p.1.1.1, p.2, p.1.1.2)) := by
    simpa [compactPositionCodeInputEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse (TMPolyTimeMap.prod_mk hX hJ)
  have hCode :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => compactPositionCodeFromCounts (p.1.1.1, p.2, p.1.1.2)) := by
    have hComp := TMPolyTimeMap.comp compactPositionCodeFromCounts_tm_polytime hCodeInput
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X compactPositionCodeListEncodedType
        (fun p : X.Carrier => [compactPositionCodeFromCounts (p.1.1.1, p.2, p.1.1.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hCode
    simpa [Function.comp, compactPositionCodeListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod compactPositionCodeListEncodedType compactPositionCodeListEncodedType)
        (fun p : X.Carrier =>
          ((show List Nat from p.1.2),
            [compactPositionCodeFromCounts (p.1.1.1, p.2, p.1.1.2)])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X compactPositionCodeListEncodedType
        (fun p : X.Carrier =>
          (show List Nat from p.1.2) ++
            [compactPositionCodeFromCounts (p.1.1.1, p.2, p.1.1.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat)
      hAppendInput
    simpa [Function.comp, compactPositionCodeListEncodedType, X] using hComp
  have hPair := TMPolyTimeMap.prod_mk hCtx hAppend
  simpa [compactPositionBlockElementStep, compactPositionBlockAccEncodedType,
    compactPositionCodeListEncodedType, X] using hPair

theorem compactPositionBlockStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactPositionBlockAccEncodedType
        compactPositionBlockInstructionEncodedType)
      compactPositionBlockAccEncodedType
      compactPositionBlockStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      compactPositionBlockAccEncodedType compactPositionBlockContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim compactPositionBlockStepLeft_tm_polytime
      compactPositionBlockElementStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem compactPositionCodeFromCounts_singleton_inputSize_le
    (N universeSize x j : Nat)
    (hUniverse : universeSize + 1 ≤ N) (hj : j + 1 ≤ N) (hx : x + 2 ≤ N) :
    compactPositionCodeListEncodedType.inputSize
        [compactPositionCodeFromCounts (universeSize, x, j)] ≤
      4 * (N * N) + 10 := by
  have hUniverseLe : universeSize ≤ N := by omega
  have hJLe : j ≤ N := by omega
  have hXLe : x ≤ N := by omega
  have hProduct : j * universeSize ≤ N * N :=
    Nat.mul_le_mul hJLe hUniverseLe
  have hCode : compactPositionCodeFromCounts (universeSize, x, j) ≤ 2 * (N * N) := by
    simp [compactPositionCodeFromCounts]
    nlinarith [hProduct, hXLe, sq_nonneg (N : Int)]
  simp [compactPositionCodeListEncodedType, EncodedType.inputSize_list_cons,
    EncodedType.inputSize_list_nil, EncodedType.inputSize_nat]
  nlinarith [hCode, sq_nonneg (N : Int)]

def compactPositionBlockFoldInv
    (N : Nat) (acc : compactPositionBlockAccEncodedType.Carrier) : Prop :=
  acc = compactPositionBlockInitAcc ∨
    ((show Nat from acc.1.1) + 1 ≤ N ∧ (show Nat from acc.1.2) + 1 ≤ N)

theorem compactPositionBlockInitAcc_bound
    (xs : List compactPositionBlockInstructionEncodedType.Carrier) :
    compactPositionBlockFoldInv (compactPositionBlockInstructionListEncodedType.inputSize xs)
        compactPositionBlockInitAcc ∧
      compactPositionBlockAccEncodedType.inputSize compactPositionBlockInitAcc ≤
        (Polynomial.C 10).eval (compactPositionBlockInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [compactPositionBlockInitAcc, compactPositionBlockAccEncodedType,
      compactPositionBlockContextEncodedType, compactPositionCodeListEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat]
    have hNil : EncodedType.nat.list.inputSize ([] : List Nat) = 0 :=
      EncodedType.inputSize_list_nil EncodedType.nat
    rw [hNil]
    norm_num

theorem compactPositionBlockStep_growth
    (source : List compactPositionBlockInstructionEncodedType.Carrier)
    (acc : compactPositionBlockAccEncodedType.Carrier)
    (instr : compactPositionBlockInstructionEncodedType.Carrier)
    (hInv :
      compactPositionBlockFoldInv
        (compactPositionBlockInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactPositionBlockInstructionEncodedType.inputSize instr ≤
        compactPositionBlockInstructionListEncodedType.inputSize source) :
    compactPositionBlockFoldInv
        (compactPositionBlockInstructionListEncodedType.inputSize source)
        (compactPositionBlockStep (acc, instr)) ∧
      compactPositionBlockAccEncodedType.inputSize (compactPositionBlockStep (acc, instr)) ≤
        compactPositionBlockAccEncodedType.inputSize acc +
          (Polynomial.C 4 * (Polynomial.X * Polynomial.X) + Polynomial.C 10).eval
            (compactPositionBlockInstructionListEncodedType.inputSize source) := by
  let N := compactPositionBlockInstructionListEncodedType.inputSize source
  rcases acc with ⟨ctx, out⟩
  rcases ctx with ⟨universeSize, j⟩
  change Nat at universeSize
  change Nat at j
  cases instr with
  | inl newCtx =>
      rcases newCtx with ⟨newUniverse, newJ⟩
      change Nat at newUniverse
      change Nat at newJ
      have hCtx :
          compactPositionBlockContextEncodedType.inputSize
              (newUniverse, newJ) + 1 ≤ N := by
        simpa [N, compactPositionBlockInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hInstr
      have hNewUniverse : newUniverse + 1 ≤ N := by
        simp [compactPositionBlockContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewJ : newJ + 1 ≤ N := by
        simp [compactPositionBlockContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      constructor
      · exact Or.inr ⟨hNewUniverse, hNewJ⟩
      · have hNil :
            compactPositionCodeListEncodedType.inputSize ([] : List Nat) = 0 :=
          EncodedType.inputSize_list_nil EncodedType.nat
        have hNewAcc :
            compactPositionBlockAccEncodedType.inputSize
                ((newUniverse, newJ), ([] : List Nat)) ≤ N := by
          simpa [compactPositionBlockAccEncodedType, compactPositionBlockContextEncodedType,
            compactPositionCodeListEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_nat, hNil] using hCtx
        have hPolyN :
            N ≤
              compactPositionBlockAccEncodedType.inputSize ((universeSize, j), out) +
                (Polynomial.C 4 * (Polynomial.X * Polynomial.X) + Polynomial.C 10).eval N := by
          simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
          nlinarith [sq_nonneg (N : Int)]
        simpa [compactPositionBlockStep, N] using hNewAcc.trans (by simpa [N] using hPolyN)
  | inr x =>
      change Nat at x
      have hx : x + 2 ≤ N := by
        simpa [N, compactPositionBlockInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum, EncodedType.nat] using hInstr
      have hBounds : universeSize + 1 ≤ N ∧ j + 1 ≤ N := by
        rcases hInv with hInit | hBound
        · injection hInit with hCtxEq _hOut
          injection hCtxEq with hUniverse hJ
          subst universeSize
          subst j
          omega
        · exact hBound
      let code := compactPositionCodeFromCounts (universeSize, x, j)
      have hSingleton :
          compactPositionCodeListEncodedType.inputSize [code] ≤
            4 * (N * N) + 10 := by
        simpa [code] using
          compactPositionCodeFromCounts_singleton_inputSize_le
            N universeSize x j hBounds.1 hBounds.2 hx
      have hAppendSize :
          compactPositionCodeListEncodedType.inputSize
              ((show List Nat from out) ++ [code]) =
            compactPositionCodeListEncodedType.inputSize out +
              compactPositionCodeListEncodedType.inputSize [code] := by
        simpa [compactPositionCodeListEncodedType] using
          list_inputSize_append EncodedType.nat out [code]
      have hAppendLe :
          compactPositionCodeListEncodedType.inputSize
              ((show List Nat from out) ++ [code]) ≤
            compactPositionCodeListEncodedType.inputSize out + (4 * (N * N) + 10) := by
        rw [hAppendSize]
        exact Nat.add_le_add_left hSingleton _
      constructor
      · exact Or.inr hBounds
      · change
          compactPositionBlockAccEncodedType.inputSize
              ((universeSize, j), (show List Nat from out) ++ [code]) ≤
            compactPositionBlockAccEncodedType.inputSize ((universeSize, j), out) +
              (Polynomial.C 4 * (Polynomial.X * Polynomial.X) + Polynomial.C 10).eval N
        simp [compactPositionBlockAccEncodedType, compactPositionBlockContextEncodedType,
          compactPositionCodeListEncodedType, EncodedType.inputSize_prod,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hAppendLe ⊢
        omega

theorem compactPositionBlockFold_tm_polytime :
    TMPolyTimeMap
      compactPositionBlockInstructionListEncodedType
      compactPositionBlockAccEncodedType
      (fun xs : List compactPositionBlockInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactPositionBlockStep (acc, instr))
          compactPositionBlockInitAcc) := by
  rcases compactPositionBlockStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactPositionBlockInstructionEncodedType compactPositionBlockAccEncodedType
      compactPositionBlockStep compactPositionBlockInitAcc hStep
      (Polynomial.C 10)
      (Polynomial.C 4 * (Polynomial.X * Polynomial.X) + Polynomial.C 10)
      compactPositionBlockFoldInv ?_ ?_
  · intro xs
    exact compactPositionBlockInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactPositionBlockStep_growth source acc instr hInv hInstr

theorem compactPositionBlockFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactPositionBlockInstructionListEncodedType
      compactPositionCodeListEncodedType
      compactPositionBlockFromInstructions := by
  have hFold := compactPositionBlockFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd compactPositionBlockContextEncodedType
    compactPositionCodeListEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, compactPositionBlockFromInstructions,
    compactPositionBlockAccEncodedType] using hComp

theorem compactPositionCodesForSourceSetExecutable_tm_polytime :
    TMPolyTimeMap
      compactPositionBlockInputEncodedType
      compactPositionCodeListEncodedType
      compactPositionCodesForSourceSetExecutable := by
  have hComp :=
    TMPolyTimeMap.comp compactPositionBlockFromInstructions_tm_polytime
      compactPositionBlockInstructions_tm_polytime
  simpa [Function.comp, compactPositionCodesForSourceSetExecutable] using hComp

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
