/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.PositionBlocks
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.CoverBlocks

/-!
Executable `α`-code list assembly for the compact
Exact-Cover-to-3-Dimensional-Matching route.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactAlphaFamilyContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType

def compactAlphaFamilyAccEncodedType : EncodedType :=
  EncodedType.prod compactAlphaFamilyContextEncodedType compactPositionCodeListEncodedType

def compactAlphaFamilyInstructionEncodedType : EncodedType :=
  EncodedType.sum compactAlphaFamilyContextEncodedType EncodedType.nat

def compactAlphaFamilyInstructionListEncodedType : EncodedType :=
  EncodedType.list compactAlphaFamilyInstructionEncodedType

def compactAlphaFamilyInputEncodedType : EncodedType :=
  compactAlphaFamilyContextEncodedType

abbrev CompactAlphaFamilyContext := Nat × List (List Nat)
abbrev CompactAlphaFamilyAcc := CompactAlphaFamilyContext × List Nat

def compactAlphaFamilyInitAcc : CompactAlphaFamilyAcc :=
  ((0, []), [])

def compactAlphaFamilyInitInstruction (ctx : CompactAlphaFamilyContext) :
    compactAlphaFamilyInstructionEncodedType.Carrier :=
  Sum.inl ctx

def compactAlphaFamilyElementInstruction (x : Nat) :
    compactAlphaFamilyInstructionEncodedType.Carrier :=
  Sum.inr x

def compactAlphaFamilyInstructions (p : CompactAlphaFamilyContext) :
    List compactAlphaFamilyInstructionEncodedType.Carrier :=
  compactAlphaFamilyInitInstruction p ::
    (List.range p.1).map compactAlphaFamilyElementInstruction

def compactAlphaFamilyElementStep (p : CompactAlphaFamilyAcc × Nat) :
    CompactAlphaFamilyAcc :=
  let ctx := p.1.1
  let out := p.1.2
  let x := p.2
  let code := compactAlphaCodeFromData (ctx.1, ctx.2, x)
  (ctx, out ++ [code])

def compactAlphaFamilyStep
    (p : CompactAlphaFamilyAcc × compactAlphaFamilyInstructionEncodedType.Carrier) :
    CompactAlphaFamilyAcc :=
  match p.2 with
  | Sum.inl ctx => (ctx, [])
  | Sum.inr x => compactAlphaFamilyElementStep (p.1, x)

def compactAlphaFamilyFromInstructions
    (xs : List compactAlphaFamilyInstructionEncodedType.Carrier) : List Nat :=
  (xs.foldl (fun acc instr => compactAlphaFamilyStep (acc, instr))
    compactAlphaFamilyInitAcc).2

def compactAlphaCodesExecutable (p : CompactAlphaFamilyContext) : List Nat :=
  compactAlphaFamilyFromInstructions (compactAlphaFamilyInstructions p)

/-! ### Semantics -/

theorem compactAlphaFamilyElementFold_eq_append_map
    (ctx : CompactAlphaFamilyContext) (xs : List Nat) (out : List Nat) :
    ((xs.map compactAlphaFamilyElementInstruction).foldl
        (fun acc instr => compactAlphaFamilyStep (acc, instr)) (ctx, out)).2 =
      out ++ xs.map (fun x => compactAlphaCodeFromData (ctx.1, ctx.2, x)) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [compactAlphaFamilyElementInstruction, compactAlphaFamilyStep,
        compactAlphaFamilyElementStep]
      have hTail := ih (out ++ [compactAlphaCodeFromData (ctx.1, ctx.2, x)])
      simpa [List.append_assoc] using hTail

theorem compactAlphaCodesExecutable_eq_map (p : CompactAlphaFamilyContext) :
    compactAlphaCodesExecutable p =
      (List.range p.1).map (fun x => compactAlphaCodeFromData (p.1, p.2, x)) := by
  change
    (((List.range p.1).map compactAlphaFamilyElementInstruction).foldl
        (fun acc instr => compactAlphaFamilyStep (acc, instr)) (p, [])).2 =
      (List.range p.1).map (fun x => compactAlphaCodeFromData (p.1, p.2, x))
  simpa using compactAlphaFamilyElementFold_eq_append_map p (List.range p.1) []

theorem compactAlphaCodesExecutable_eq_compactAlphaCodes
    (I : ExactCoverInput) (hEvery : compactEveryElementOccurs I) :
    compactAlphaCodesExecutable (I.system.universeSize, I.system.sets) =
      compactAlphaCodes I := by
  rw [compactAlphaCodesExecutable_eq_map]
  unfold compactAlphaCodes
  apply List.map_congr_left
  intro x hx
  have hxLt : x < I.system.universeSize := by
    simpa using hx
  exact compactAlphaCodeFromData_eq_compactAlphaCode I x (hEvery x hxLt)

/-! ### Size facts -/

theorem compactAlphaCodeFromData_inputSize_le
    (N universeSize : Nat) (sets : List (List Nat)) (x : Nat)
    (hUniverse : universeSize + 1 ≤ N)
    (hSets : setFamilyStructuredEncodedType.inputSize sets ≤ N)
    (hx : x + 2 ≤ N) :
    EncodedType.nat.inputSize (compactAlphaCodeFromData (universeSize, sets, x)) ≤
      50 * (N * (N * N)) + 10 := by
  let alphaIndex := compactAlphaSetIndexExecutable (x, sets)
  have hAlphaIndexRaw := compactAlphaSetIndexExecutable_le_poly x sets
  have hAlphaIndexSize :
      compactAlphaSetIndexInputEncodedType.inputSize (x, sets) ≤ 2 * N := by
    simp [compactAlphaSetIndexInputEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat]
    omega
  have hAlphaIndex : alphaIndex ≤ 20 * (N * N) := by
    have hRaw : alphaIndex ≤
        3 * compactAlphaSetIndexInputEncodedType.inputSize (x, sets) ^ 2 + 10 := by
      simpa [alphaIndex] using hAlphaIndexRaw
    have hMono :
        3 * compactAlphaSetIndexInputEncodedType.inputSize (x, sets) ^ 2 + 10 ≤
          20 * (N * N) := by
      have hN : 2 ≤ N := by omega
      nlinarith [hAlphaIndexSize, hN, sq_nonneg (N : Int),
        sq_nonneg (compactAlphaSetIndexInputEncodedType.inputSize (x, sets) : Int)]
    exact hRaw.trans hMono
  have hUniverseLe : universeSize ≤ N := by omega
  have hXLe : x ≤ N := by omega
  have hAlphaProduct : alphaIndex * universeSize ≤ (20 * (N * N)) * N :=
    Nat.mul_le_mul hAlphaIndex hUniverseLe
  have hCode : compactAlphaCodeFromData (universeSize, sets, x) ≤
      30 * (N * (N * N)) := by
    simp [compactAlphaCodeFromData, compactPositionCodeFromCounts]
    nlinarith [hAlphaProduct, hXLe, sq_nonneg (N : Int)]
  simp [EncodedType.inputSize_nat]
  nlinarith [hCode, sq_nonneg (N : Int)]

theorem compactAlphaCodeFromData_singleton_inputSize_le
    (N universeSize : Nat) (sets : List (List Nat)) (x : Nat)
    (hUniverse : universeSize + 1 ≤ N)
    (hSets : setFamilyStructuredEncodedType.inputSize sets ≤ N)
    (hx : x + 2 ≤ N) :
    compactPositionCodeListEncodedType.inputSize
        [compactAlphaCodeFromData (universeSize, sets, x)] ≤
      50 * (N * (N * N)) + 20 := by
  have hCode := compactAlphaCodeFromData_inputSize_le N universeSize sets x
    hUniverse hSets hx
  simp [EncodedType.inputSize_nat] at hCode
  simp [compactPositionCodeListEncodedType, EncodedType.inputSize_list_cons,
    EncodedType.inputSize_list_nil]
  omega

/-! ### TM witnesses -/

theorem compactAlphaFamilyInitInstruction_tm_polytime :
    TMPolyTimeMap
      compactAlphaFamilyContextEncodedType
      compactAlphaFamilyInstructionEncodedType
      compactAlphaFamilyInitInstruction := by
  simpa [compactAlphaFamilyInstructionEncodedType,
    compactAlphaFamilyInitInstruction] using
    TMPolyTimeMap.inl compactAlphaFamilyContextEncodedType EncodedType.nat

theorem compactAlphaFamilyElementInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactAlphaFamilyInstructionEncodedType
      compactAlphaFamilyElementInstruction := by
  simpa [compactAlphaFamilyInstructionEncodedType,
    compactAlphaFamilyElementInstruction] using
    TMPolyTimeMap.inr compactAlphaFamilyContextEncodedType EncodedType.nat

theorem compactAlphaFamilyInstructions_tm_polytime :
    TMPolyTimeMap
      compactAlphaFamilyInputEncodedType
      compactAlphaFamilyInstructionListEncodedType
      compactAlphaFamilyInstructions := by
  let X := compactAlphaFamilyInputEncodedType
  have hCtx : TMPolyTimeMap X compactAlphaFamilyContextEncodedType (fun p : X.Carrier => p) :=
    TMPolyTimeMap.id X
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, compactAlphaFamilyInputEncodedType,
      compactAlphaFamilyContextEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
  have hInit :
      TMPolyTimeMap X compactAlphaFamilyInstructionEncodedType
        (fun p : X.Carrier => compactAlphaFamilyInitInstruction p) := by
    have hComp := TMPolyTimeMap.comp compactAlphaFamilyInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X compactPositionCodeListEncodedType
        (fun p : X.Carrier => List.range p.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hUniverse
    simpa [Function.comp, compactPositionCodeListEncodedType, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X compactAlphaFamilyInstructionListEncodedType
        (fun p : X.Carrier => (List.range p.1).map compactAlphaFamilyElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactAlphaFamilyElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, compactAlphaFamilyInstructionListEncodedType,
      compactPositionCodeListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactAlphaFamilyInstructionEncodedType
          compactAlphaFamilyInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactAlphaFamilyInitInstruction p,
            (List.range p.1).map compactAlphaFamilyElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hElementInstructions
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons compactAlphaFamilyInstructionEncodedType) hConsInput
  simpa [Function.comp, compactAlphaFamilyInstructions,
    compactAlphaFamilyInstructionListEncodedType, X] using hCons

theorem compactAlphaFamilyStepLeft_tm_polytime :
    TMPolyTimeMap
      compactAlphaFamilyContextEncodedType
      compactAlphaFamilyAccEncodedType
      (fun ctx : CompactAlphaFamilyContext => (ctx, ([] : List Nat))) := by
  have hCtx := TMPolyTimeMap.id compactAlphaFamilyContextEncodedType
  have hEmpty :
      TMPolyTimeMap compactAlphaFamilyContextEncodedType compactPositionCodeListEncodedType
        (fun _ : CompactAlphaFamilyContext => ([] : List Nat)) :=
    TMPolyTimeMap.const compactAlphaFamilyContextEncodedType compactPositionCodeListEncodedType []
  simpa [compactAlphaFamilyAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hEmpty

theorem compactAlphaFamilyElementStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactAlphaFamilyAccEncodedType EncodedType.nat)
      compactAlphaFamilyAccEncodedType
      compactAlphaFamilyElementStep := by
  let X := EncodedType.prod compactAlphaFamilyAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactAlphaFamilyAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactAlphaFamilyAccEncodedType EncodedType.nat
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactAlphaFamilyAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X compactAlphaFamilyContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst compactAlphaFamilyContextEncodedType
      compactPositionCodeListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactAlphaFamilyAccEncodedType, X] using hComp
  have hOut : TMPolyTimeMap X compactPositionCodeListEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd compactAlphaFamilyContextEncodedType
      compactPositionCodeListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactAlphaFamilyAccEncodedType, X] using hComp
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, compactAlphaFamilyContextEncodedType, X] using hComp
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, compactAlphaFamilyContextEncodedType, X] using hComp
  have hCodeInput :
      TMPolyTimeMap X compactAlphaCodeFromDataInputEncodedType
        (fun p : X.Carrier => (p.1.1.1, p.1.1.2, p.2)) := by
    simpa [compactAlphaCodeFromDataInputEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse (TMPolyTimeMap.prod_mk hSets hX)
  have hCode :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => compactAlphaCodeFromData (p.1.1.1, p.1.1.2, p.2)) := by
    have hComp := TMPolyTimeMap.comp compactAlphaCodeFromData_tm_polytime hCodeInput
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X compactPositionCodeListEncodedType
        (fun p : X.Carrier => [compactAlphaCodeFromData (p.1.1.1, p.1.1.2, p.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hCode
    simpa [Function.comp, compactPositionCodeListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod compactPositionCodeListEncodedType compactPositionCodeListEncodedType)
        (fun p : X.Carrier =>
          ((show List Nat from p.1.2),
            [compactAlphaCodeFromData (p.1.1.1, p.1.1.2, p.2)])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X compactPositionCodeListEncodedType
        (fun p : X.Carrier =>
          (show List Nat from p.1.2) ++
            [compactAlphaCodeFromData (p.1.1.1, p.1.1.2, p.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat)
      hAppendInput
    simpa [Function.comp, compactPositionCodeListEncodedType, X] using hComp
  have hPair := TMPolyTimeMap.prod_mk hCtx hAppend
  simpa [compactAlphaFamilyElementStep, compactAlphaFamilyAccEncodedType,
    compactPositionCodeListEncodedType, X] using hPair

theorem compactAlphaFamilyStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactAlphaFamilyAccEncodedType
        compactAlphaFamilyInstructionEncodedType)
      compactAlphaFamilyAccEncodedType
      compactAlphaFamilyStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      compactAlphaFamilyAccEncodedType compactAlphaFamilyContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim compactAlphaFamilyStepLeft_tm_polytime
      compactAlphaFamilyElementStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def compactAlphaFamilyFoldInv
    (N : Nat) (acc : compactAlphaFamilyAccEncodedType.Carrier) : Prop :=
  acc = compactAlphaFamilyInitAcc ∨
    ((show Nat from acc.1.1) + 1 ≤ N ∧
      setFamilyStructuredEncodedType.inputSize (show List (List Nat) from acc.1.2) ≤ N)

theorem compactAlphaFamilyInitAcc_bound
    (xs : List compactAlphaFamilyInstructionEncodedType.Carrier) :
    compactAlphaFamilyFoldInv (compactAlphaFamilyInstructionListEncodedType.inputSize xs)
        compactAlphaFamilyInitAcc ∧
      compactAlphaFamilyAccEncodedType.inputSize compactAlphaFamilyInitAcc ≤
        (Polynomial.C 10).eval (compactAlphaFamilyInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · have hNilSets :
        setStructuredEncodedType.list.inputSize ([] : List (List Nat)) = 0 :=
      EncodedType.inputSize_list_nil setStructuredEncodedType
    simp [compactAlphaFamilyInitAcc, compactAlphaFamilyAccEncodedType,
      compactAlphaFamilyContextEncodedType, compactPositionCodeListEncodedType,
      setFamilyStructuredEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat, hNilSets]
    have hNilCodes : EncodedType.nat.list.inputSize ([] : List Nat) = 0 :=
      EncodedType.inputSize_list_nil EncodedType.nat
    rw [hNilCodes]
    norm_num

theorem compactAlphaFamilyStep_growth
    (source : List compactAlphaFamilyInstructionEncodedType.Carrier)
    (acc : compactAlphaFamilyAccEncodedType.Carrier)
    (instr : compactAlphaFamilyInstructionEncodedType.Carrier)
    (hInv :
      compactAlphaFamilyFoldInv
        (compactAlphaFamilyInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactAlphaFamilyInstructionEncodedType.inputSize instr ≤
        compactAlphaFamilyInstructionListEncodedType.inputSize source) :
    compactAlphaFamilyFoldInv
        (compactAlphaFamilyInstructionListEncodedType.inputSize source)
        (compactAlphaFamilyStep (acc, instr)) ∧
      compactAlphaFamilyAccEncodedType.inputSize (compactAlphaFamilyStep (acc, instr)) ≤
        compactAlphaFamilyAccEncodedType.inputSize acc +
          (Polynomial.C 50 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
            Polynomial.C 20).eval
            (compactAlphaFamilyInstructionListEncodedType.inputSize source) := by
  let N := compactAlphaFamilyInstructionListEncodedType.inputSize source
  rcases acc with ⟨ctx, out⟩
  rcases ctx with ⟨universeSize, sets⟩
  change Nat at universeSize
  cases instr with
  | inl newCtx =>
      rcases newCtx with ⟨newUniverse, newSets⟩
      change Nat at newUniverse
      have hCtx :
          compactAlphaFamilyContextEncodedType.inputSize (newUniverse, newSets) + 1 ≤ N := by
        simpa [N, compactAlphaFamilyInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hInstr
      have hNewUniverse : newUniverse + 1 ≤ N := by
        simp [compactAlphaFamilyContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewSets : setFamilyStructuredEncodedType.inputSize newSets ≤ N := by
        simp [compactAlphaFamilyContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      constructor
      · exact Or.inr ⟨hNewUniverse, hNewSets⟩
      · have hNilCodes :
            compactPositionCodeListEncodedType.inputSize ([] : List Nat) = 0 :=
          EncodedType.inputSize_list_nil EncodedType.nat
        have hNewAcc :
            compactAlphaFamilyAccEncodedType.inputSize
                ((newUniverse, newSets), ([] : List Nat)) ≤ N := by
          simpa [compactAlphaFamilyAccEncodedType, compactAlphaFamilyContextEncodedType,
            compactPositionCodeListEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_nat, hNilCodes] using hCtx
        have hPolyN :
            N ≤ compactAlphaFamilyAccEncodedType.inputSize ((universeSize, sets), out) +
              (Polynomial.C 50 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
                Polynomial.C 20).eval N := by
          have hBase :
              N ≤
                (Polynomial.C 50 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
                  Polynomial.C 20).eval N := by
            have hN : 1 ≤ N := by omega
            have hN2 : N ≤ N * N := Nat.le_mul_of_pos_right N hN
            have hN3 : N * N ≤ N * (N * N) := Nat.mul_le_mul_left N hN2
            simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
            omega
          exact hBase.trans (Nat.le_add_left _ _)
        simpa [compactAlphaFamilyStep, N] using hNewAcc.trans (by simpa [N] using hPolyN)
  | inr x =>
      change Nat at x
      have hx : x + 2 ≤ N := by
        simpa [N, compactAlphaFamilyInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum, EncodedType.nat] using hInstr
      have hBounds :
          universeSize + 1 ≤ N ∧ setFamilyStructuredEncodedType.inputSize sets ≤ N := by
        rcases hInv with hInit | hBound
        · injection hInit with hCtxEq _hOut
          injection hCtxEq with hUniverse hSets
          subst universeSize
          subst sets
          have hNil : setFamilyStructuredEncodedType.inputSize ([] : List (List Nat)) = 0 := rfl
          omega
        · exact hBound
      let code := compactAlphaCodeFromData (universeSize, sets, x)
      have hSingleton :
          compactPositionCodeListEncodedType.inputSize [code] ≤
            50 * (N * (N * N)) + 20 := by
        simpa [code] using
          compactAlphaCodeFromData_singleton_inputSize_le
            N universeSize sets x hBounds.1 hBounds.2 hx
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
            compactPositionCodeListEncodedType.inputSize out +
              (50 * (N * (N * N)) + 20) := by
        rw [hAppendSize]
        exact Nat.add_le_add_left hSingleton _
      constructor
      · exact Or.inr hBounds
      · change
          compactAlphaFamilyAccEncodedType.inputSize
              ((universeSize, sets), (show List Nat from out) ++ [code]) ≤
            compactAlphaFamilyAccEncodedType.inputSize ((universeSize, sets), out) +
              (Polynomial.C 50 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
                Polynomial.C 20).eval N
        simp [compactAlphaFamilyAccEncodedType, compactPositionCodeListEncodedType,
          EncodedType.inputSize_prod, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_X] at hAppendLe ⊢
        omega

theorem compactAlphaFamilyFold_tm_polytime :
    TMPolyTimeMap
      compactAlphaFamilyInstructionListEncodedType
      compactAlphaFamilyAccEncodedType
      (fun xs : List compactAlphaFamilyInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactAlphaFamilyStep (acc, instr))
          compactAlphaFamilyInitAcc) := by
  rcases compactAlphaFamilyStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactAlphaFamilyInstructionEncodedType compactAlphaFamilyAccEncodedType
      compactAlphaFamilyStep compactAlphaFamilyInitAcc hStep
      (Polynomial.C 10)
      (Polynomial.C 50 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
        Polynomial.C 20)
      compactAlphaFamilyFoldInv ?_ ?_
  · intro xs
    exact compactAlphaFamilyInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactAlphaFamilyStep_growth source acc instr hInv hInstr

theorem compactAlphaFamilyFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactAlphaFamilyInstructionListEncodedType
      compactPositionCodeListEncodedType
      compactAlphaFamilyFromInstructions := by
  have hFold := compactAlphaFamilyFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd compactAlphaFamilyContextEncodedType
    compactPositionCodeListEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, compactAlphaFamilyFromInstructions,
    compactAlphaFamilyAccEncodedType] using hComp

theorem compactAlphaCodesExecutable_tm_polytime :
    TMPolyTimeMap
      compactAlphaFamilyInputEncodedType
      compactPositionCodeListEncodedType
      compactAlphaCodesExecutable := by
  have hComp :=
    TMPolyTimeMap.comp compactAlphaFamilyFromInstructions_tm_polytime
      compactAlphaFamilyInstructions_tm_polytime
  simpa [Function.comp, compactAlphaCodesExecutable] using hComp

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
