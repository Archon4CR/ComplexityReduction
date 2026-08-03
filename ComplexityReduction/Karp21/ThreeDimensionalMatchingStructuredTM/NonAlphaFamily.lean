/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.PositionFamily
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.AlphaFamily

/-!
Executable non-alpha code filtering for the compact
Exact-Cover-to-3-Dimensional-Matching route.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactNonAlphaFilterAccEncodedType : EncodedType :=
  EncodedType.prod compactPositionCodeListEncodedType compactPositionCodeListEncodedType

def compactNonAlphaFilterInstructionEncodedType : EncodedType :=
  EncodedType.sum compactPositionCodeListEncodedType EncodedType.nat

def compactNonAlphaFilterInstructionListEncodedType : EncodedType :=
  EncodedType.list compactNonAlphaFilterInstructionEncodedType

def compactNonAlphaFilterInputEncodedType : EncodedType :=
  EncodedType.prod compactPositionCodeListEncodedType compactPositionCodeListEncodedType

def compactNonAlphaInputEncodedType : EncodedType :=
  compactPositionFamilyInputEncodedType

abbrev CompactNonAlphaFilterAcc := List Nat × List Nat

def compactNonAlphaFilterInitAcc : CompactNonAlphaFilterAcc :=
  ([], [])

def compactNonAlphaFilterInitInstruction (alphaCodes : List Nat) :
    compactNonAlphaFilterInstructionEncodedType.Carrier :=
  Sum.inl alphaCodes

def compactNonAlphaFilterCodeInstruction (c : Nat) :
    compactNonAlphaFilterInstructionEncodedType.Carrier :=
  Sum.inr c

def compactNonAlphaFilterAppendCode (p : CompactNonAlphaFilterAcc × Nat) : List Nat :=
  p.1.2 ++ [p.2]

def compactNonAlphaFilterInstructions (p : List Nat × List Nat) :
    List compactNonAlphaFilterInstructionEncodedType.Carrier :=
  compactNonAlphaFilterInitInstruction p.2 ::
    p.1.map compactNonAlphaFilterCodeInstruction

def compactNonAlphaFilterCodeStep (p : CompactNonAlphaFilterAcc × Nat) :
    CompactNonAlphaFilterAcc :=
  let alphaCodes := p.1.1
  let out := p.1.2
  let c := p.2
  if HittingSet.setContainsBool (c, alphaCodes) then
    (alphaCodes, out)
  else
    (alphaCodes, compactNonAlphaFilterAppendCode p)

def compactNonAlphaFilterStep
    (p : CompactNonAlphaFilterAcc × compactNonAlphaFilterInstructionEncodedType.Carrier) :
    CompactNonAlphaFilterAcc :=
  match p.2 with
  | Sum.inl alphaCodes => (alphaCodes, [])
  | Sum.inr c => compactNonAlphaFilterCodeStep (p.1, c)

def compactNonAlphaFilterFromInstructions
    (xs : List compactNonAlphaFilterInstructionEncodedType.Carrier) : List Nat :=
  (xs.foldl (fun acc instr => compactNonAlphaFilterStep (acc, instr))
    compactNonAlphaFilterInitAcc).2

def compactNonAlphaCodesFromListsExecutable (p : List Nat × List Nat) : List Nat :=
  compactNonAlphaFilterFromInstructions (compactNonAlphaFilterInstructions p)

def compactNonAlphaCodesExecutable (p : CompactPositionFamilyContext) : List Nat :=
  compactNonAlphaCodesFromListsExecutable
    (compactPositionCodesExecutable p, compactAlphaCodesExecutable (p.1, p.2.2))

/-! ### Semantics -/

theorem compactNonAlphaFilterCodeFold_eq_append_filter
    (xs alphaCodes out : List Nat) :
    ((xs.map compactNonAlphaFilterCodeInstruction).foldl
        (fun acc instr => compactNonAlphaFilterStep (acc, instr)) (alphaCodes, out)).2 =
      out ++ xs.filter (fun c => Bool.not (HittingSet.setContainsBool (c, alphaCodes))) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons c cs ih =>
      rw [List.map_cons, List.foldl_cons]
      by_cases hMem : HittingSet.setContainsBool (c, alphaCodes) = true
      · simp [compactNonAlphaFilterCodeInstruction, compactNonAlphaFilterStep,
          compactNonAlphaFilterCodeStep, hMem]
        have hTail := ih out
        simpa [compactNonAlphaFilterStep] using hTail
      · have hFalse : HittingSet.setContainsBool (c, alphaCodes) = false := by
          cases h : HittingSet.setContainsBool (c, alphaCodes)
          · rfl
          · exact False.elim (hMem h)
        simp [compactNonAlphaFilterCodeInstruction, compactNonAlphaFilterStep,
          compactNonAlphaFilterCodeStep, hFalse]
        have hTail := ih (out ++ [c])
        simpa [compactNonAlphaFilterStep, List.append_assoc] using hTail

theorem compactNonAlphaCodesFromListsExecutable_eq_filter
    (positionCodes alphaCodes : List Nat) :
    compactNonAlphaCodesFromListsExecutable (positionCodes, alphaCodes) =
      positionCodes.filter (fun c => Bool.not (HittingSet.setContainsBool (c, alphaCodes))) := by
  change
    (((positionCodes.map compactNonAlphaFilterCodeInstruction).foldl
        (fun acc instr => compactNonAlphaFilterStep (acc, instr)) (alphaCodes, [])).2 =
      positionCodes.filter (fun c => Bool.not (HittingSet.setContainsBool (c, alphaCodes))))
  simpa using compactNonAlphaFilterCodeFold_eq_append_filter positionCodes alphaCodes []

theorem compactNonAlphaFilter_predicate_eq_of_everyElementOccurs
    (I : ExactCoverInput) (hEvery : compactEveryElementOccurs I) (c : Nat)
    [Decidable (¬ compactIsAlphaCode I c)] :
    Bool.not (HittingSet.setContainsBool (c, compactAlphaCodes I)) =
      decide (¬ compactIsAlphaCode I c) := by
  classical
  have hIff := mem_compactAlphaCodes_iff_of_everyElementOccurs (I := I) hEvery c
  by_cases hAlpha : compactIsAlphaCode I c
  · have hMem : c ∈ compactAlphaCodes I := hIff.2 hAlpha
    simp [HittingSet.setContainsBool_eq_decide, hMem, hAlpha]
  · have hNotMem : ¬ c ∈ compactAlphaCodes I := by
      intro hMem
      exact hAlpha (hIff.1 hMem)
    simp [HittingSet.setContainsBool_eq_decide, hNotMem, hAlpha]

theorem compactNonAlphaCodesExecutable_eq_compactNonAlphaCodes
    (I : ExactCoverInput) (hEvery : compactEveryElementOccurs I) :
    compactNonAlphaCodesExecutable
        (I.system.universeSize, I.system.sets.length, I.system.sets) =
      compactNonAlphaCodes I := by
  classical
  unfold compactNonAlphaCodesExecutable
  rw [compactNonAlphaCodesFromListsExecutable_eq_filter]
  rw [compactPositionCodesExecutable_eq_compactPositionCodes]
  rw [compactAlphaCodesExecutable_eq_compactAlphaCodes I hEvery]
  unfold compactNonAlphaCodes
  apply List.filter_congr
  intro c _hc
  exact compactNonAlphaFilter_predicate_eq_of_everyElementOccurs I hEvery c

/-! ### TM witnesses -/

theorem compactNonAlphaFilterInitInstruction_tm_polytime :
    TMPolyTimeMap
      compactPositionCodeListEncodedType
      compactNonAlphaFilterInstructionEncodedType
      compactNonAlphaFilterInitInstruction := by
  simpa [compactNonAlphaFilterInstructionEncodedType,
    compactNonAlphaFilterInitInstruction] using
    TMPolyTimeMap.inl compactPositionCodeListEncodedType EncodedType.nat

theorem compactNonAlphaFilterCodeInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactNonAlphaFilterInstructionEncodedType
      compactNonAlphaFilterCodeInstruction := by
  simpa [compactNonAlphaFilterInstructionEncodedType,
    compactNonAlphaFilterCodeInstruction] using
    TMPolyTimeMap.inr compactPositionCodeListEncodedType EncodedType.nat

theorem compactNonAlphaFilterInstructions_tm_polytime :
    TMPolyTimeMap
      compactNonAlphaFilterInputEncodedType
      compactNonAlphaFilterInstructionListEncodedType
      compactNonAlphaFilterInstructions := by
  let X := compactNonAlphaFilterInputEncodedType
  have hPositionCodes :
      TMPolyTimeMap X compactPositionCodeListEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, compactNonAlphaFilterInputEncodedType] using
      TMPolyTimeMap.fst compactPositionCodeListEncodedType compactPositionCodeListEncodedType
  have hAlphaCodes :
      TMPolyTimeMap X compactPositionCodeListEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, compactNonAlphaFilterInputEncodedType] using
      TMPolyTimeMap.snd compactPositionCodeListEncodedType compactPositionCodeListEncodedType
  have hInit :
      TMPolyTimeMap X compactNonAlphaFilterInstructionEncodedType
        (fun p : X.Carrier => compactNonAlphaFilterInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp compactNonAlphaFilterInitInstruction_tm_polytime hAlphaCodes
    simpa [Function.comp, X] using hComp
  have hMapped :
      TMPolyTimeMap X compactNonAlphaFilterInstructionListEncodedType
        (fun p : X.Carrier => p.1.map compactNonAlphaFilterCodeInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactNonAlphaFilterCodeInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hPositionCodes
    simpa [Function.comp, compactNonAlphaFilterInstructionListEncodedType,
      compactPositionCodeListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactNonAlphaFilterInstructionEncodedType
          compactNonAlphaFilterInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactNonAlphaFilterInitInstruction p.2,
            p.1.map compactNonAlphaFilterCodeInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMapped
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons compactNonAlphaFilterInstructionEncodedType) hConsInput
  simpa [Function.comp, compactNonAlphaFilterInstructions,
    compactNonAlphaFilterInstructionListEncodedType, X] using hCons

theorem compactNonAlphaFilterStepLeft_tm_polytime :
    TMPolyTimeMap
      compactPositionCodeListEncodedType
      compactNonAlphaFilterAccEncodedType
      (fun alphaCodes : List Nat => (alphaCodes, ([] : List Nat))) := by
  have hAlpha := TMPolyTimeMap.id compactPositionCodeListEncodedType
  have hEmpty :
      TMPolyTimeMap compactPositionCodeListEncodedType compactPositionCodeListEncodedType
        (fun _ : List Nat => ([] : List Nat)) :=
    TMPolyTimeMap.const compactPositionCodeListEncodedType compactPositionCodeListEncodedType []
  simpa [compactNonAlphaFilterAccEncodedType] using TMPolyTimeMap.prod_mk hAlpha hEmpty

theorem compactNonAlphaFilterCodeStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactNonAlphaFilterAccEncodedType EncodedType.nat)
      compactNonAlphaFilterAccEncodedType
      compactNonAlphaFilterCodeStep := by
  let X := EncodedType.prod compactNonAlphaFilterAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactNonAlphaFilterAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactNonAlphaFilterAccEncodedType EncodedType.nat
  have hCode : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactNonAlphaFilterAccEncodedType EncodedType.nat
  have hAlpha :
      TMPolyTimeMap X compactPositionCodeListEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst compactPositionCodeListEncodedType compactPositionCodeListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactNonAlphaFilterAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X compactPositionCodeListEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd compactPositionCodeListEncodedType compactPositionCodeListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactNonAlphaFilterAccEncodedType, X] using hComp
  have hContainsInput :
      TMPolyTimeMap X HittingSet.setContainsInstructionInputEncodedType
        (fun p : X.Carrier => (p.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hCode hAlpha
  have hContains :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => HittingSet.setContainsBool (p.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setContainsBool_tm_polytime hContainsInput
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X compactPositionCodeListEncodedType (fun p : X.Carrier => [p.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hCode
    simpa [Function.comp, compactPositionCodeListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod compactPositionCodeListEncodedType compactPositionCodeListEncodedType)
        (fun p : X.Carrier => ((p.1.2 : List Nat), ([p.2] : List Nat))) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X compactPositionCodeListEncodedType
        (fun p : X.Carrier => compactNonAlphaFilterAppendCode p) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat) hAppendInput
    simpa [Function.comp, compactNonAlphaFilterAppendCode, compactPositionCodeListEncodedType, X]
      using hComp
  have hAppendBranch :
      TMPolyTimeMap X compactNonAlphaFilterAccEncodedType
        (fun p : X.Carrier => (p.1.1, compactNonAlphaFilterAppendCode p)) :=
    TMPolyTimeMap.prod_mk hAlpha hAppend
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (HittingSet.setContainsBool (p.2, p.1.1), p)) :=
    TMPolyTimeMap.prod_mk hContains (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) compactNonAlphaFilterAccEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => p.2.1
          | false => (p.2.1.1, compactNonAlphaFilterAppendCode p.2)) :=
    graphBoolProduct_dispatch_tm_polytime X compactNonAlphaFilterAccEncodedType
      (fFalse := fun p : X.Carrier => (p.1.1, compactNonAlphaFilterAppendCode p))
      (fTrue := fun p : X.Carrier => p.1)
      hAppendBranch hAcc
  have hComp := TMPolyTimeMap.comp hBranch hBranchInput
  convert hComp using 1
  funext p
  cases h : HittingSet.setContainsBool (p.2, p.1.1)
  · simp [Function.comp, compactNonAlphaFilterCodeStep, compactNonAlphaFilterAppendCode, h]
    rfl
  · simp [Function.comp, compactNonAlphaFilterCodeStep, h]

theorem compactNonAlphaFilterStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactNonAlphaFilterAccEncodedType
        compactNonAlphaFilterInstructionEncodedType)
      compactNonAlphaFilterAccEncodedType
      compactNonAlphaFilterStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      compactNonAlphaFilterAccEncodedType compactPositionCodeListEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim compactNonAlphaFilterStepLeft_tm_polytime
      compactNonAlphaFilterCodeStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def compactNonAlphaFilterFoldInv (_N : Nat) (_acc : compactNonAlphaFilterAccEncodedType.Carrier) :
    Prop :=
  True

theorem compactNonAlphaFilterInitAcc_bound
    (xs : List compactNonAlphaFilterInstructionEncodedType.Carrier) :
    compactNonAlphaFilterFoldInv (compactNonAlphaFilterInstructionListEncodedType.inputSize xs)
        compactNonAlphaFilterInitAcc ∧
      compactNonAlphaFilterAccEncodedType.inputSize compactNonAlphaFilterInitAcc ≤
        (Polynomial.C 5).eval (compactNonAlphaFilterInstructionListEncodedType.inputSize xs) := by
  constructor
  · trivial
  · have hBase : compactNonAlphaFilterAccEncodedType.inputSize compactNonAlphaFilterInitAcc ≤ 5 := by
      unfold compactNonAlphaFilterInitAcc compactNonAlphaFilterAccEncodedType
      unfold compactPositionCodeListEncodedType
      simp [EncodedType.inputSize, EncodedType.prod, EncodedType.list, EncodedType.nat]
    simpa using hBase

theorem compactNonAlphaFilterStep_growth
    (source : List compactNonAlphaFilterInstructionEncodedType.Carrier)
    (acc : compactNonAlphaFilterAccEncodedType.Carrier)
    (instr : compactNonAlphaFilterInstructionEncodedType.Carrier)
    (_hInv :
      compactNonAlphaFilterFoldInv
        (compactNonAlphaFilterInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactNonAlphaFilterInstructionEncodedType.inputSize instr ≤
        compactNonAlphaFilterInstructionListEncodedType.inputSize source) :
    compactNonAlphaFilterFoldInv
        (compactNonAlphaFilterInstructionListEncodedType.inputSize source)
        (compactNonAlphaFilterStep (acc, instr)) ∧
      compactNonAlphaFilterAccEncodedType.inputSize (compactNonAlphaFilterStep (acc, instr)) ≤
        compactNonAlphaFilterAccEncodedType.inputSize acc +
          (Polynomial.X + Polynomial.C 10).eval
            (compactNonAlphaFilterInstructionListEncodedType.inputSize source) := by
  constructor
  · trivial
  · let N := compactNonAlphaFilterInstructionListEncodedType.inputSize source
    rcases acc with ⟨alphaCodes, out⟩
    change List Nat at alphaCodes
    change List Nat at out
    cases instr with
    | inl newAlphaCodes =>
        have hNewAlpha :
            compactPositionCodeListEncodedType.inputSize newAlphaCodes + 1 ≤ N := by
          simpa [N, compactNonAlphaFilterInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum] using hInstr
        have hNil : compactPositionCodeListEncodedType.inputSize ([] : List Nat) = 0 :=
          EncodedType.inputSize_list_nil EncodedType.nat
        simp [compactNonAlphaFilterStep, compactNonAlphaFilterAccEncodedType,
          EncodedType.inputSize_prod, Polynomial.eval_add, Polynomial.eval_X, hNil]
        omega
    | inr c =>
        change Nat at c
        by_cases hMem : HittingSet.setContainsBool (c, alphaCodes) = true
        · simp [compactNonAlphaFilterStep, compactNonAlphaFilterCodeStep, hMem,
            Polynomial.eval_add, Polynomial.eval_X]
          exact Nat.le_add_right _ _
        · have hFalse : HittingSet.setContainsBool (c, alphaCodes) = false := by
            cases h : HittingSet.setContainsBool (c, alphaCodes)
            · rfl
            · exact False.elim (hMem h)
          have hc : c + 2 ≤ N := by
            simpa [N, compactNonAlphaFilterInstructionEncodedType, EncodedType.inputSize,
              EncodedType.sum, EncodedType.nat] using hInstr
          have hAppendSize :
              compactPositionCodeListEncodedType.inputSize
                  (out ++ [c]) =
                compactPositionCodeListEncodedType.inputSize out + (c + 2) := by
            change (EncodedType.list EncodedType.nat).inputSize (out ++ [c]) =
              (EncodedType.list EncodedType.nat).inputSize out + (c + 2)
            calc
              (EncodedType.list EncodedType.nat).inputSize (out ++ [c])
                  =
                (EncodedType.list EncodedType.nat).inputSize out +
                    (EncodedType.list EncodedType.nat).inputSize ([c] : List Nat) :=
                  natList_inputSize_append out ([c] : List Nat)
              _ = (EncodedType.list EncodedType.nat).inputSize out + (c + 2) := by
                  simp [EncodedType.inputSize, EncodedType.list, EncodedType.nat]
          simp [compactNonAlphaFilterStep, compactNonAlphaFilterCodeStep, hFalse,
            compactNonAlphaFilterAppendCode,
            compactNonAlphaFilterAccEncodedType, EncodedType.inputSize_prod,
            Polynomial.eval_add, Polynomial.eval_X, hAppendSize]
          omega

theorem compactNonAlphaFilterFold_tm_polytime :
    TMPolyTimeMap
      compactNonAlphaFilterInstructionListEncodedType
      compactNonAlphaFilterAccEncodedType
      (fun xs : List compactNonAlphaFilterInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactNonAlphaFilterStep (acc, instr))
          compactNonAlphaFilterInitAcc) := by
  rcases compactNonAlphaFilterStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactNonAlphaFilterInstructionEncodedType compactNonAlphaFilterAccEncodedType
      compactNonAlphaFilterStep compactNonAlphaFilterInitAcc hStep
      (Polynomial.C 5) (Polynomial.X + Polynomial.C 10)
      compactNonAlphaFilterFoldInv ?_ ?_
  · intro xs
    exact compactNonAlphaFilterInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactNonAlphaFilterStep_growth source acc instr hInv hInstr

theorem compactNonAlphaFilterFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactNonAlphaFilterInstructionListEncodedType
      compactPositionCodeListEncodedType
      compactNonAlphaFilterFromInstructions := by
  have hFold := compactNonAlphaFilterFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd compactPositionCodeListEncodedType compactPositionCodeListEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, compactNonAlphaFilterFromInstructions,
    compactNonAlphaFilterAccEncodedType] using hComp

theorem compactNonAlphaCodesFromListsExecutable_tm_polytime :
    TMPolyTimeMap
      compactNonAlphaFilterInputEncodedType
      compactPositionCodeListEncodedType
      compactNonAlphaCodesFromListsExecutable := by
  have hComp :=
    TMPolyTimeMap.comp compactNonAlphaFilterFromInstructions_tm_polytime
      compactNonAlphaFilterInstructions_tm_polytime
  simpa [Function.comp, compactNonAlphaCodesFromListsExecutable] using hComp

theorem compactNonAlphaCodesExecutable_tm_polytime :
    TMPolyTimeMap
      compactNonAlphaInputEncodedType
      compactPositionCodeListEncodedType
      compactNonAlphaCodesExecutable := by
  let X := compactNonAlphaInputEncodedType
  have hPositions :
      TMPolyTimeMap X compactPositionCodeListEncodedType compactPositionCodesExecutable := by
    simpa [X, compactNonAlphaInputEncodedType] using compactPositionCodesExecutable_tm_polytime
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, compactNonAlphaInputEncodedType, compactPositionFamilyInputEncodedType,
      compactPositionFamilyContextEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
        (fun p : X.Carrier => p.2) := by
    simpa [X, compactNonAlphaInputEncodedType, compactPositionFamilyInputEncodedType,
      compactPositionFamilyContextEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
  have hSets :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hAlphaInput :
      TMPolyTimeMap X compactAlphaFamilyInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hUniverse hSets
  have hAlpha :
      TMPolyTimeMap X compactPositionCodeListEncodedType
        (fun p : X.Carrier => compactAlphaCodesExecutable (p.1, p.2.2)) := by
    have hComp := TMPolyTimeMap.comp compactAlphaCodesExecutable_tm_polytime hAlphaInput
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X compactNonAlphaFilterInputEncodedType
        (fun p : X.Carrier =>
          (compactPositionCodesExecutable p, compactAlphaCodesExecutable (p.1, p.2.2))) :=
    TMPolyTimeMap.prod_mk hPositions hAlpha
  have hComp := TMPolyTimeMap.comp compactNonAlphaCodesFromListsExecutable_tm_polytime hPair
  simpa [Function.comp, compactNonAlphaCodesExecutable, X] using hComp

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
