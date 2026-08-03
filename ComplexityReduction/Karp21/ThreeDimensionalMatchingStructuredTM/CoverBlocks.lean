/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.CoverTriples
import ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold

/-!
Executable cover-triple blocks for one source set in the compact
Exact-Cover-to-3-Dimensional-Matching route.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactCoverBlockContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat)

def compactCoverBlockAccEncodedType : EncodedType :=
  EncodedType.prod compactCoverBlockContextEncodedType tripleListStructuredEncodedType

def compactCoverBlockInstructionEncodedType : EncodedType :=
  EncodedType.sum compactCoverBlockContextEncodedType EncodedType.nat

def compactCoverBlockInstructionListEncodedType : EncodedType :=
  EncodedType.list compactCoverBlockInstructionEncodedType

def compactCoverBlockInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod setFamilyStructuredEncodedType
      (EncodedType.prod EncodedType.nat setStructuredEncodedType))

abbrev CompactCoverBlockContext := Nat × List (List Nat) × Nat
abbrev CompactCoverBlockAcc := CompactCoverBlockContext × List (Nat × Nat × Nat)

def compactCoverBlockInitAcc : CompactCoverBlockAcc :=
  ((0, ([], 0)), [])

def compactCoverBlockInitInstruction (ctx : CompactCoverBlockContext) :
    compactCoverBlockInstructionEncodedType.Carrier :=
  Sum.inl ctx

def compactCoverBlockElementInstruction (x : Nat) :
    compactCoverBlockInstructionEncodedType.Carrier :=
  Sum.inr x

def compactCoverBlockInstructions
    (p : Nat × List (List Nat) × Nat × List Nat) :
    List compactCoverBlockInstructionEncodedType.Carrier :=
  compactCoverBlockInitInstruction (p.1, p.2.1, p.2.2.1) ::
    (compactSupportExecutable (p.1, p.2.2.2)).map compactCoverBlockElementInstruction

def compactCoverBlockElementStep (p : CompactCoverBlockAcc × Nat) :
    CompactCoverBlockAcc :=
  let ctx := p.1.1
  let out := p.1.2
  let x := p.2
  let triple := compactCoverTripleFromData (ctx.1, ctx.2.1, ctx.2.2, x)
  (ctx, out ++ [triple])

def compactCoverBlockStep
    (p : CompactCoverBlockAcc × compactCoverBlockInstructionEncodedType.Carrier) :
    CompactCoverBlockAcc :=
  match p.2 with
  | Sum.inl ctx => (ctx, [])
  | Sum.inr x => compactCoverBlockElementStep (p.1, x)

def compactCoverBlockFromInstructions
    (xs : List compactCoverBlockInstructionEncodedType.Carrier) :
    List (Nat × Nat × Nat) :=
  (xs.foldl (fun acc instr => compactCoverBlockStep (acc, instr))
    compactCoverBlockInitAcc).2

def compactCoverTriplesForSourceSetExecutable
    (p : Nat × List (List Nat) × Nat × List Nat) :
    List (Nat × Nat × Nat) :=
  compactCoverBlockFromInstructions (compactCoverBlockInstructions p)

theorem compactCoverBlockElementFold_eq_append_map
    (ctx : CompactCoverBlockContext) (xs : List Nat)
    (out : List (Nat × Nat × Nat)) :
    ((xs.map compactCoverBlockElementInstruction).foldl
        (fun acc instr => compactCoverBlockStep (acc, instr)) (ctx, out)).2 =
      out ++ xs.map (fun x => compactCoverTripleFromData (ctx.1, ctx.2.1, ctx.2.2, x)) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [compactCoverBlockElementInstruction, compactCoverBlockStep,
        compactCoverBlockElementStep]
      have hTail := ih (out ++ [compactCoverTripleFromData (ctx.1, ctx.2.1, ctx.2.2, x)])
      simpa [List.append_assoc] using hTail

theorem compactCoverTriplesForSourceSetExecutable_eq_map
    (p : Nat × List (List Nat) × Nat × List Nat) :
    compactCoverTriplesForSourceSetExecutable p =
      (compactSupportExecutable (p.1, p.2.2.2)).map
        (fun x => compactCoverTripleFromData (p.1, p.2.1, p.2.2.1, x)) := by
  change
    (((compactSupportExecutable (p.1, p.2.2.2)).map
        compactCoverBlockElementInstruction).foldl
        (fun acc instr => compactCoverBlockStep (acc, instr))
        ((p.1, p.2.1, p.2.2.1), [])).2 =
      (compactSupportExecutable (p.1, p.2.2.2)).map
        (fun x => compactCoverTripleFromData (p.1, p.2.1, p.2.2.1, x))
  simpa using
    compactCoverBlockElementFold_eq_append_map
      (p.1, p.2.1, p.2.2.1) (compactSupportExecutable (p.1, p.2.2.2)) []

theorem compactCoverTriplesForSourceSetExecutable_eq_compactCoverTriplesForSet
    (I : ExactCoverInput) {j : Nat} (hj : j < I.system.sets.length) :
    compactCoverTriplesForSourceSetExecutable
        (I.system.universeSize, I.system.sets, j, compactSourceSetAt I j) =
      compactCoverTriplesForSet I j := by
  rw [compactCoverTriplesForSourceSetExecutable_eq_map]
  rw [compactSupportExecutable_eq_compactSupport]
  unfold compactCoverTriplesForSet
  apply List.map_congr_left
  intro x hx
  exact compactCoverTripleFromData_eq_compactCoverTriple
    (I := I) (x := x) (j := j) ⟨j, hj, hx⟩

/-! ### TM certificates for one source-set cover block -/

theorem compactCoverBlockInitInstruction_tm_polytime :
    TMPolyTimeMap
      compactCoverBlockContextEncodedType
      compactCoverBlockInstructionEncodedType
      compactCoverBlockInitInstruction := by
  simpa [compactCoverBlockInstructionEncodedType, compactCoverBlockInitInstruction] using
    TMPolyTimeMap.inl compactCoverBlockContextEncodedType EncodedType.nat

theorem compactCoverBlockElementInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactCoverBlockInstructionEncodedType
      compactCoverBlockElementInstruction := by
  simpa [compactCoverBlockInstructionEncodedType,
    compactCoverBlockElementInstruction] using
    TMPolyTimeMap.inr compactCoverBlockContextEncodedType EncodedType.nat

theorem compactCoverBlockInstructions_tm_polytime :
    TMPolyTimeMap
      compactCoverBlockInputEncodedType
      compactCoverBlockInstructionListEncodedType
      compactCoverBlockInstructions := by
  let X := compactCoverBlockInputEncodedType
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, compactCoverBlockInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod setFamilyStructuredEncodedType
          (EncodedType.prod EncodedType.nat setStructuredEncodedType))
  have hPayload :
      TMPolyTimeMap X
        (EncodedType.prod setFamilyStructuredEncodedType
          (EncodedType.prod EncodedType.nat setStructuredEncodedType))
        (fun p : X.Carrier => p.2) := by
    simpa [X, compactCoverBlockInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod setFamilyStructuredEncodedType
          (EncodedType.prod EncodedType.nat setStructuredEncodedType))
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst setFamilyStructuredEncodedType
      (EncodedType.prod EncodedType.nat setStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hInner :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setStructuredEncodedType)
        (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd setFamilyStructuredEncodedType
      (EncodedType.prod EncodedType.nat setStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInner
    simpa [Function.comp, X] using hComp
  have hSet : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInner
    simpa [Function.comp, X] using hComp
  have hCtx :
      TMPolyTimeMap X compactCoverBlockContextEncodedType
        (fun p : X.Carrier => (p.1, p.2.1, p.2.2.1)) := by
    simpa [compactCoverBlockContextEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse (TMPolyTimeMap.prod_mk hSets hJ)
  have hInit :
      TMPolyTimeMap X compactCoverBlockInstructionEncodedType
        (fun p : X.Carrier => compactCoverBlockInitInstruction (p.1, p.2.1, p.2.2.1)) := by
    have hComp := TMPolyTimeMap.comp compactCoverBlockInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hSupportInput :
      TMPolyTimeMap X compactSupportInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hUniverse hSet
  have hSupport :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => compactSupportExecutable (p.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp compactSupportExecutable_tm_polytime hSupportInput
    simpa [Function.comp, X] using hComp
  have hMapped :
      TMPolyTimeMap X compactCoverBlockInstructionListEncodedType
        (fun p : X.Carrier =>
          (compactSupportExecutable (p.1, p.2.2.2)).map
            compactCoverBlockElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactCoverBlockElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hSupport
    simpa [Function.comp, compactCoverBlockInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactCoverBlockInstructionEncodedType
          compactCoverBlockInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactCoverBlockInitInstruction (p.1, p.2.1, p.2.2.1),
            (compactSupportExecutable (p.1, p.2.2.2)).map
              compactCoverBlockElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMapped
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons compactCoverBlockInstructionEncodedType) hConsInput
  simpa [Function.comp, compactCoverBlockInstructions,
    compactCoverBlockInstructionListEncodedType, X] using hCons

theorem compactCoverBlockStepLeft_tm_polytime :
    TMPolyTimeMap
      compactCoverBlockContextEncodedType
      compactCoverBlockAccEncodedType
      (fun ctx : CompactCoverBlockContext => (ctx, ([] : List (Nat × Nat × Nat)))) := by
  have hCtx := TMPolyTimeMap.id compactCoverBlockContextEncodedType
  have hEmpty :
      TMPolyTimeMap compactCoverBlockContextEncodedType tripleListStructuredEncodedType
        (fun _ : CompactCoverBlockContext => ([] : List (Nat × Nat × Nat))) :=
    TMPolyTimeMap.const compactCoverBlockContextEncodedType tripleListStructuredEncodedType []
  simpa [compactCoverBlockAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hEmpty

theorem compactCoverBlockElementStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactCoverBlockAccEncodedType EncodedType.nat)
      compactCoverBlockAccEncodedType
      compactCoverBlockElementStep := by
  let X := EncodedType.prod compactCoverBlockAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactCoverBlockAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactCoverBlockAccEncodedType EncodedType.nat
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactCoverBlockAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X compactCoverBlockContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst compactCoverBlockContextEncodedType tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactCoverBlockAccEncodedType, X] using hComp
  have hOut : TMPolyTimeMap X tripleListStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd compactCoverBlockContextEncodedType tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactCoverBlockAccEncodedType, X] using hComp
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, compactCoverBlockContextEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat)
        (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, compactCoverBlockContextEncodedType, X] using hComp
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun p : X.Carrier => p.1.1.2.1) := by
    have hFst := TMPolyTimeMap.fst setFamilyStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd setFamilyStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hTripleInput :
      TMPolyTimeMap X compactCoverTripleFromDataInputEncodedType
        (fun p : X.Carrier => (p.1.1.1, p.1.1.2.1, p.1.1.2.2, p.2)) := by
    simpa [compactCoverTripleFromDataInputEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse
        (TMPolyTimeMap.prod_mk hSets (TMPolyTimeMap.prod_mk hJ hX))
  have hTriple :
      TMPolyTimeMap X tripleStructuredEncodedType
        (fun p : X.Carrier =>
          compactCoverTripleFromData (p.1.1.1, p.1.1.2.1, p.1.1.2.2, p.2)) := by
    have hComp := TMPolyTimeMap.comp compactCoverTripleFromData_tm_polytime hTripleInput
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier =>
          [compactCoverTripleFromData (p.1.1.1, p.1.1.2.1, p.1.1.2.2, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton tripleStructuredEncodedType) hTriple
    simpa [Function.comp, tripleListStructuredEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show List (Nat × Nat × Nat) from p.1.2),
            [compactCoverTripleFromData (p.1.1.1, p.1.1.2.1, p.1.1.2.2, p.2)])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat × Nat) from p.1.2) ++
            [compactCoverTripleFromData (p.1.1.1, p.1.1.2.1, p.1.1.2.2, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append tripleStructuredEncodedType) hAppendInput
    simpa [Function.comp, tripleListStructuredEncodedType, X] using hComp
  have hPair := TMPolyTimeMap.prod_mk hCtx hAppend
  simpa [compactCoverBlockElementStep, compactCoverBlockAccEncodedType, X] using hPair

theorem compactCoverBlockStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactCoverBlockAccEncodedType compactCoverBlockInstructionEncodedType)
      compactCoverBlockAccEncodedType
      compactCoverBlockStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      compactCoverBlockAccEncodedType compactCoverBlockContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim compactCoverBlockStepLeft_tm_polytime
      compactCoverBlockElementStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem compactAlphaSetIndexExecutable_le_poly (x : Nat) (sets : List (List Nat)) :
    compactAlphaSetIndexExecutable (x, sets) ≤
      3 * compactAlphaSetIndexInputEncodedType.inputSize (x, sets) ^ 2 + 10 := by
  rw [compactAlphaSetIndexExecutable, MaxCut.natListGetDFromInput_eq_getD]
  have hGet :
      (HittingSet.setIndexIndicesFromFamily (x, sets)).getD 0 0 ≤
        (EncodedType.list EncodedType.nat).inputSize
          (HittingSet.setIndexIndicesFromFamily (x, sets)) := by
    by_cases hLen : 0 < (HittingSet.setIndexIndicesFromFamily (x, sets)).length
    · rw [List.getD_eq_getElem (l := HittingSet.setIndexIndicesFromFamily (x, sets))
        (d := 0) hLen]
      have hMem :
          (HittingSet.setIndexIndicesFromFamily (x, sets))[0] ∈
            HittingSet.setIndexIndicesFromFamily (x, sets) :=
        List.getElem_mem hLen
      have hElem :=
        SetCovering.incidentEncodedList_element_inputSize_le
          (X := EncodedType.nat) hMem
      simp [EncodedType.inputSize_nat] at hElem
      omega
    · rw [List.getD_eq_default (l := HittingSet.setIndexIndicesFromFamily (x, sets))
        (d := 0) (n := 0) (Nat.le_of_not_gt hLen)]
      exact Nat.zero_le _
  exact hGet.trans (HittingSet.setIndexIndicesFromFamily_inputSize_le (x, sets))

theorem compactCoverTripleFromData_inputSize_le
    (N universeSize : Nat) (sets : List (List Nat)) (j x : Nat)
    (hUniverse : universeSize + 1 ≤ N)
    (hSets : setFamilyStructuredEncodedType.inputSize sets ≤ N)
    (hj : j + 1 ≤ N) (hx : x + 2 ≤ N) :
    tripleStructuredEncodedType.inputSize
        (compactCoverTripleFromData (universeSize, sets, j, x)) ≤
      100 * (N * (N * N)) := by
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
  have hJLe : j ≤ N := by omega
  have hXLe : x ≤ N := by omega
  have hAlphaProduct : alphaIndex * universeSize ≤ (20 * (N * N)) * N :=
    Nat.mul_le_mul hAlphaIndex hUniverseLe
  have hAlphaCode :
      compactAlphaCodeFromData (universeSize, sets, x) ≤ 30 * (N * (N * N)) := by
    simp [compactAlphaCodeFromData, compactPositionCodeFromCounts]
    nlinarith [hAlphaProduct, hXLe, sq_nonneg (N : Int)]
  have hCodeProduct : j * universeSize ≤ N * N :=
    Nat.mul_le_mul hJLe hUniverseLe
  have hCode : compactPositionCodeFromCounts (universeSize, x, j) ≤ 2 * (N * N) := by
    simp [compactPositionCodeFromCounts]
    nlinarith [hCodeProduct, hXLe, sq_nonneg (N : Int)]
  simp [compactCoverTripleFromData, tripleStructuredEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat]
  nlinarith [hAlphaCode, hCode, sq_nonneg (N : Int)]

theorem compactCoverTripleFromData_singleton_inputSize_le
    (N universeSize : Nat) (sets : List (List Nat)) (j x : Nat)
    (hUniverse : universeSize + 1 ≤ N)
    (hSets : setFamilyStructuredEncodedType.inputSize sets ≤ N)
    (hj : j + 1 ≤ N) (hx : x + 2 ≤ N) :
    tripleListStructuredEncodedType.inputSize
        [compactCoverTripleFromData (universeSize, sets, j, x)] ≤
      100 * (N * (N * N)) + 100 := by
  have hTriple :=
    compactCoverTripleFromData_inputSize_le N universeSize sets j x hUniverse hSets hj hx
  simp [tripleListStructuredEncodedType, EncodedType.inputSize_list_cons,
    EncodedType.inputSize_list_nil]
  omega

def compactCoverBlockFoldInv
    (N : Nat) (acc : compactCoverBlockAccEncodedType.Carrier) : Prop :=
  acc = compactCoverBlockInitAcc ∨
    ((show Nat from acc.1.1) + 1 ≤ N ∧
      setFamilyStructuredEncodedType.inputSize (show List (List Nat) from acc.1.2.1) ≤ N ∧
      (show Nat from acc.1.2.2) + 1 ≤ N)

theorem compactCoverBlockInitAcc_bound
    (xs : List compactCoverBlockInstructionEncodedType.Carrier) :
    compactCoverBlockFoldInv (compactCoverBlockInstructionListEncodedType.inputSize xs)
        compactCoverBlockInitAcc ∧
      compactCoverBlockAccEncodedType.inputSize compactCoverBlockInitAcc ≤
        (Polynomial.C 10).eval (compactCoverBlockInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · have hNilTriples :
        tripleStructuredEncodedType.list.inputSize ([] : List (Nat × Nat × Nat)) = 0 :=
      EncodedType.inputSize_list_nil tripleStructuredEncodedType
    have hNilSets :
        setStructuredEncodedType.list.inputSize ([] : List (List Nat)) = 0 :=
      EncodedType.inputSize_list_nil setStructuredEncodedType
    simp [compactCoverBlockInitAcc, compactCoverBlockAccEncodedType,
      compactCoverBlockContextEncodedType, tripleListStructuredEncodedType,
      setFamilyStructuredEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat, hNilTriples, hNilSets]

theorem compactCoverBlockStep_growth
    (source : List compactCoverBlockInstructionEncodedType.Carrier)
    (acc : compactCoverBlockAccEncodedType.Carrier)
    (instr : compactCoverBlockInstructionEncodedType.Carrier)
    (hInv :
      compactCoverBlockFoldInv
        (compactCoverBlockInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactCoverBlockInstructionEncodedType.inputSize instr ≤
        compactCoverBlockInstructionListEncodedType.inputSize source) :
    compactCoverBlockFoldInv
        (compactCoverBlockInstructionListEncodedType.inputSize source)
        (compactCoverBlockStep (acc, instr)) ∧
      compactCoverBlockAccEncodedType.inputSize (compactCoverBlockStep (acc, instr)) ≤
        compactCoverBlockAccEncodedType.inputSize acc +
          (Polynomial.C 100 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
              Polynomial.C 100).eval
            (compactCoverBlockInstructionListEncodedType.inputSize source) := by
  let N := compactCoverBlockInstructionListEncodedType.inputSize source
  rcases acc with ⟨ctx, out⟩
  rcases ctx with ⟨universeSize, sets, j⟩
  change Nat at universeSize
  change Nat at j
  cases instr with
  | inl newCtx =>
      rcases newCtx with ⟨newUniverse, newSets, newJ⟩
      change Nat at newUniverse
      change Nat at newJ
      have hCtx :
          compactCoverBlockContextEncodedType.inputSize
              (newUniverse, newSets, newJ) + 1 ≤ N := by
        simpa [N, compactCoverBlockInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hInstr
      have hNewUniverse : newUniverse + 1 ≤ N := by
        simp [compactCoverBlockContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewSets : setFamilyStructuredEncodedType.inputSize newSets ≤ N := by
        simp [compactCoverBlockContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewJ : newJ + 1 ≤ N := by
        simp [compactCoverBlockContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      constructor
      · exact Or.inr ⟨hNewUniverse, hNewSets, hNewJ⟩
      · have hNilTriples :
            tripleStructuredEncodedType.list.inputSize ([] : List (Nat × Nat × Nat)) = 0 :=
          EncodedType.inputSize_list_nil tripleStructuredEncodedType
        have hNewAcc :
            compactCoverBlockAccEncodedType.inputSize
                ((newUniverse, newSets, newJ), ([] : List (Nat × Nat × Nat))) ≤ N := by
          simpa [compactCoverBlockAccEncodedType, compactCoverBlockContextEncodedType,
            tripleListStructuredEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_nat, hNilTriples] using hCtx
        have hPolyN :
            N ≤
              compactCoverBlockAccEncodedType.inputSize ((universeSize, sets, j), out) +
                (Polynomial.C 100 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
                    Polynomial.C 100).eval N := by
          simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
          nlinarith [sq_nonneg (N : Int)]
        simpa [compactCoverBlockStep, N] using hNewAcc.trans (by simpa [N] using hPolyN)
  | inr x =>
      change Nat at x
      have hx : x + 2 ≤ N := by
        simpa [N, compactCoverBlockInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum, EncodedType.nat] using hInstr
      have hBounds :
          universeSize + 1 ≤ N ∧
            setFamilyStructuredEncodedType.inputSize sets ≤ N ∧
            j + 1 ≤ N := by
        rcases hInv with hInit | hBound
        · injection hInit with hCtxEq _hOut
          injection hCtxEq with hUniverse hTail
          injection hTail with hSets hJ
          subst universeSize
          subst sets
          subst j
          constructor
          · omega
          · constructor
            · have hNil :
                setFamilyStructuredEncodedType.inputSize ([] : List (List Nat)) = 0 := rfl
              omega
            · omega
        · exact hBound
      let triple := compactCoverTripleFromData (universeSize, sets, j, x)
      have hSingleton :
          tripleListStructuredEncodedType.inputSize [triple] ≤
            100 * (N * (N * N)) + 100 := by
        simpa [triple] using
          compactCoverTripleFromData_singleton_inputSize_le
            N universeSize sets j x hBounds.1 hBounds.2.1 hBounds.2.2 hx
      have hAppendSize :
          tripleListStructuredEncodedType.inputSize
              ((show List (Nat × Nat × Nat) from out) ++ [triple]) =
            tripleListStructuredEncodedType.inputSize out +
              tripleListStructuredEncodedType.inputSize [triple] := by
        simpa [tripleListStructuredEncodedType] using
          list_inputSize_append tripleStructuredEncodedType out [triple]
      have hAppendLe :
          tripleListStructuredEncodedType.inputSize
              ((show List (Nat × Nat × Nat) from out) ++ [triple]) ≤
            tripleListStructuredEncodedType.inputSize out +
              (100 * (N * (N * N)) + 100) := by
        rw [hAppendSize]
        exact Nat.add_le_add_left hSingleton _
      constructor
      · exact Or.inr hBounds
      · change
          compactCoverBlockAccEncodedType.inputSize
              ((universeSize, sets, j),
                (show List (Nat × Nat × Nat) from out) ++ [triple]) ≤
            compactCoverBlockAccEncodedType.inputSize ((universeSize, sets, j), out) +
              (Polynomial.C 100 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
                  Polynomial.C 100).eval N
        simp [compactCoverBlockAccEncodedType, EncodedType.inputSize_prod,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hAppendLe ⊢
        omega

theorem compactCoverBlockFold_tm_polytime :
    TMPolyTimeMap
      compactCoverBlockInstructionListEncodedType
      compactCoverBlockAccEncodedType
      (fun xs : List compactCoverBlockInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactCoverBlockStep (acc, instr))
          compactCoverBlockInitAcc) := by
  rcases compactCoverBlockStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactCoverBlockInstructionEncodedType compactCoverBlockAccEncodedType
      compactCoverBlockStep compactCoverBlockInitAcc hStep
      (Polynomial.C 10)
      (Polynomial.C 100 * (Polynomial.X * (Polynomial.X * Polynomial.X)) +
        Polynomial.C 100)
      compactCoverBlockFoldInv ?_ ?_
  · intro xs
    exact compactCoverBlockInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactCoverBlockStep_growth source acc instr hInv hInstr

theorem compactCoverBlockFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactCoverBlockInstructionListEncodedType
      tripleListStructuredEncodedType
      compactCoverBlockFromInstructions := by
  have hFold := compactCoverBlockFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd compactCoverBlockContextEncodedType tripleListStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, compactCoverBlockFromInstructions,
    compactCoverBlockAccEncodedType] using hComp

theorem compactCoverTriplesForSourceSetExecutable_tm_polytime :
    TMPolyTimeMap
      compactCoverBlockInputEncodedType
      tripleListStructuredEncodedType
      compactCoverTriplesForSourceSetExecutable := by
  have hComp :=
    TMPolyTimeMap.comp compactCoverBlockFromInstructions_tm_polytime
      compactCoverBlockInstructions_tm_polytime
  simpa [Function.comp, compactCoverTriplesForSourceSetExecutable] using hComp

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
