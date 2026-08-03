/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.FillerBetaFamily
import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.NonAlphaFamily

/-!
Outer family-level filler-triple assembly for all non-alpha beta codes in the
compact Exact-Cover-to-3-Dimensional-Matching route.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactFillerFamilyContextEncodedType : EncodedType :=
  compactPositionFamilyContextEncodedType

def compactFillerFamilyAccEncodedType : EncodedType :=
  EncodedType.prod compactFillerFamilyContextEncodedType tripleListStructuredEncodedType

def compactFillerFamilyInstructionEncodedType : EncodedType :=
  EncodedType.sum compactFillerFamilyContextEncodedType EncodedType.nat

def compactFillerFamilyInstructionListEncodedType : EncodedType :=
  EncodedType.list compactFillerFamilyInstructionEncodedType

def compactFillerFamilyInputEncodedType : EncodedType :=
  compactFillerFamilyContextEncodedType

abbrev CompactFillerFamilyContext := CompactPositionFamilyContext
abbrev CompactFillerFamilyAcc := CompactFillerFamilyContext × List (Nat × Nat × Nat)

def compactFillerFamilyInitAcc : CompactFillerFamilyAcc :=
  ((0, (0, [])), [])

def compactFillerFamilyInitInstruction (ctx : CompactFillerFamilyContext) :
    compactFillerFamilyInstructionEncodedType.Carrier :=
  Sum.inl ctx

def compactFillerFamilyBetaInstruction (beta : Nat) :
    compactFillerFamilyInstructionEncodedType.Carrier :=
  Sum.inr beta

def compactFillerFamilyInstructions (p : CompactFillerFamilyContext) :
    List compactFillerFamilyInstructionEncodedType.Carrier :=
  compactFillerFamilyInitInstruction p ::
    (compactNonAlphaCodesExecutable p).map compactFillerFamilyBetaInstruction

def compactFillerFamilyBetaStep (p : CompactFillerFamilyAcc × Nat) :
    CompactFillerFamilyAcc :=
  let ctx := p.1.1
  let out := p.1.2
  let beta := p.2
  (ctx, out ++
    compactFillerTriplesForBetaExecutable (ctx.1, beta, ctx.2.1, ctx.2.2))

def compactFillerFamilyStep
    (p : CompactFillerFamilyAcc × compactFillerFamilyInstructionEncodedType.Carrier) :
    CompactFillerFamilyAcc :=
  match p.2 with
  | Sum.inl ctx => (ctx, [])
  | Sum.inr beta => compactFillerFamilyBetaStep (p.1, beta)

def compactFillerFamilyFromInstructions
    (xs : List compactFillerFamilyInstructionEncodedType.Carrier) :
    List (Nat × Nat × Nat) :=
  (xs.foldl (fun acc instr => compactFillerFamilyStep (acc, instr))
    compactFillerFamilyInitAcc).2

def compactFillerTriplesExecutable (p : CompactFillerFamilyContext) :
    List (Nat × Nat × Nat) :=
  compactFillerFamilyFromInstructions (compactFillerFamilyInstructions p)

/-! ### Semantics -/

theorem compactFillerFamilyBetaFold_eq_append_flatMap
    (ctx : CompactFillerFamilyContext) (betas : List Nat)
    (out : List (Nat × Nat × Nat)) :
    ((betas.map compactFillerFamilyBetaInstruction).foldl
        (fun acc instr => compactFillerFamilyStep (acc, instr)) (ctx, out)).2 =
      out ++ betas.flatMap (fun beta =>
        compactFillerTriplesForBetaExecutable (ctx.1, beta, ctx.2.1, ctx.2.2)) := by
  induction betas generalizing out with
  | nil =>
      simp
  | cons beta betas ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [compactFillerFamilyBetaInstruction, compactFillerFamilyStep,
        compactFillerFamilyBetaStep]
      have hTail := ih (out ++
        compactFillerTriplesForBetaExecutable (ctx.1, beta, ctx.2.1, ctx.2.2))
      simpa [List.append_assoc] using hTail

theorem compactFillerTriplesExecutable_eq_flatMap
    (p : CompactFillerFamilyContext) :
    compactFillerTriplesExecutable p =
      (compactNonAlphaCodesExecutable p).flatMap (fun beta =>
        compactFillerTriplesForBetaExecutable (p.1, beta, p.2.1, p.2.2)) := by
  change
    (((compactNonAlphaCodesExecutable p).map compactFillerFamilyBetaInstruction).foldl
        (fun acc instr => compactFillerFamilyStep (acc, instr)) (p, [])).2 =
      (compactNonAlphaCodesExecutable p).flatMap (fun beta =>
        compactFillerTriplesForBetaExecutable (p.1, beta, p.2.1, p.2.2))
  simpa using
    compactFillerFamilyBetaFold_eq_append_flatMap p (compactNonAlphaCodesExecutable p) []

theorem compactFillerTriplesExecutable_eq_compactFillerTriples
    (I : ExactCoverInput) (hEvery : compactEveryElementOccurs I) :
    compactFillerTriplesExecutable
        (I.system.universeSize, I.system.sets.length, I.system.sets) =
      compactFillerTriples I := by
  rw [compactFillerTriplesExecutable_eq_flatMap]
  rw [compactNonAlphaCodesExecutable_eq_compactNonAlphaCodes I hEvery]
  unfold compactFillerTriples
  apply List.flatMap_congr
  intro beta _hbeta
  exact compactFillerTriplesForBetaExecutable_eq_compactFillerTriplesForBeta I beta

/-! ### Local size facts for the fold -/

theorem tripleList_flatMap_inputSize_le_length_mul_bound {α : Type}
    (xs : List α) (f : α → List (Nat × Nat × Nat)) (B : Nat)
    (hB : ∀ x ∈ xs, tripleListStructuredEncodedType.inputSize (f x) ≤ B) :
    tripleListStructuredEncodedType.inputSize (xs.flatMap f) ≤ xs.length * B := by
  induction xs with
  | nil =>
      simp [tripleListStructuredEncodedType, EncodedType.inputSize_list_nil]
  | cons x xs ih =>
      have hHead : tripleListStructuredEncodedType.inputSize (f x) ≤ B := hB x (by simp)
      have hTail :
          tripleListStructuredEncodedType.inputSize (xs.flatMap f) ≤ xs.length * B := by
        exact ih (fun y hy => hB y (by simp [hy]))
      have hAppend :
          tripleListStructuredEncodedType.inputSize (f x ++ xs.flatMap f) =
            tripleListStructuredEncodedType.inputSize (f x) +
              tripleListStructuredEncodedType.inputSize (xs.flatMap f) := by
        simpa [tripleListStructuredEncodedType] using
          list_inputSize_append tripleStructuredEncodedType (f x) (xs.flatMap f)
      change
        tripleListStructuredEncodedType.inputSize (f x ++ xs.flatMap f) ≤
          (xs.length + 1) * B
      calc
        tripleListStructuredEncodedType.inputSize (f x ++ xs.flatMap f)
            =
          tripleListStructuredEncodedType.inputSize (f x) +
            tripleListStructuredEncodedType.inputSize (xs.flatMap f) := hAppend
        _ ≤ B + xs.length * B := Nat.add_le_add hHead hTail
        _ = (xs.length + 1) * B := by ring

theorem compactFillerTriplesForBetaExecutable_inputSize_le
    (N universeSize beta setCount : Nat) (sets : List (List Nat))
    (hUniverse : universeSize + 1 ≤ N)
    (hBeta : beta + 1 ≤ N)
    (hSetCount : setCount + 1 ≤ N) :
    tripleListStructuredEncodedType.inputSize
        (compactFillerTriplesForBetaExecutable (universeSize, beta, setCount, sets)) ≤
      100 * (N * (N * (N * N))) + 100 := by
  rw [compactFillerTriplesForBetaExecutable_eq_flatMap]
  let B := 50 * (N * (N * N)) + 50
  have hEach :
      ∀ j ∈ List.range setCount,
        tripleListStructuredEncodedType.inputSize
            (compactFillerTriplesForSourceSetExecutable
              (universeSize, beta, j, SteinerTree.setFamilyGetD (sets, j))) ≤ B := by
    intro j hj
    have hjLt : j < setCount := by simpa using hj
    have hjN : j + 1 ≤ N := by omega
    simpa [B] using
      compactFillerTriplesForSourceSetExecutable_inputSize_le
        N universeSize beta j (SteinerTree.setFamilyGetD (sets, j))
        hUniverse hBeta hjN
  have hFlat :=
    tripleList_flatMap_inputSize_le_length_mul_bound
      (List.range setCount)
      (fun j =>
        compactFillerTriplesForSourceSetExecutable
          (universeSize, beta, j, SteinerTree.setFamilyGetD (sets, j)))
      B hEach
  have hCount : (List.range setCount).length ≤ N := by simp; omega
  have hMul :
      (List.range setCount).length * B ≤ N * B :=
    Nat.mul_le_mul_right B hCount
  have hPoly : N * B ≤ 100 * (N * (N * (N * N))) + 100 := by
    have hN : 1 ≤ N := by omega
    have hN2 : N ≤ N * N := Nat.le_mul_of_pos_right N hN
    have hN3 : N * N ≤ N * (N * N) := Nat.mul_le_mul_left N hN2
    have hN4 : N * (N * N) ≤ N * (N * (N * N)) :=
      Nat.mul_le_mul_left N hN3
    have hNle4 : N ≤ N * (N * (N * N)) := hN2.trans (hN3.trans hN4)
    have hExpand :
        N * B = 50 * (N * (N * (N * N))) + 50 * N := by
      simp [B]
      ring
    rw [hExpand]
    omega
  exact hFlat.trans (hMul.trans hPoly)

/-! ### TM witnesses -/

theorem compactFillerFamilyInitInstruction_tm_polytime :
    TMPolyTimeMap
      compactFillerFamilyContextEncodedType
      compactFillerFamilyInstructionEncodedType
      compactFillerFamilyInitInstruction := by
  simpa [compactFillerFamilyInstructionEncodedType,
    compactFillerFamilyInitInstruction] using
    TMPolyTimeMap.inl compactFillerFamilyContextEncodedType EncodedType.nat

theorem compactFillerFamilyBetaInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactFillerFamilyInstructionEncodedType
      compactFillerFamilyBetaInstruction := by
  simpa [compactFillerFamilyInstructionEncodedType,
    compactFillerFamilyBetaInstruction] using
    TMPolyTimeMap.inr compactFillerFamilyContextEncodedType EncodedType.nat

theorem compactFillerFamilyInstructions_tm_polytime :
    TMPolyTimeMap
      compactFillerFamilyInputEncodedType
      compactFillerFamilyInstructionListEncodedType
      compactFillerFamilyInstructions := by
  let X := compactFillerFamilyInputEncodedType
  have hCtx : TMPolyTimeMap X compactFillerFamilyContextEncodedType (fun p : X.Carrier => p) :=
    TMPolyTimeMap.id X
  have hNonAlpha :
      TMPolyTimeMap X compactPositionCodeListEncodedType compactNonAlphaCodesExecutable := by
    simpa [X, compactFillerFamilyInputEncodedType,
      compactFillerFamilyContextEncodedType] using compactNonAlphaCodesExecutable_tm_polytime
  have hInit :
      TMPolyTimeMap X compactFillerFamilyInstructionEncodedType
        (fun p : X.Carrier => compactFillerFamilyInitInstruction p) := by
    have hComp := TMPolyTimeMap.comp compactFillerFamilyInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hBetaInstructions :
      TMPolyTimeMap X compactFillerFamilyInstructionListEncodedType
        (fun p : X.Carrier =>
          (compactNonAlphaCodesExecutable p).map compactFillerFamilyBetaInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactFillerFamilyBetaInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hNonAlpha
    simpa [Function.comp, compactFillerFamilyInstructionListEncodedType,
      compactPositionCodeListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactFillerFamilyInstructionEncodedType
          compactFillerFamilyInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactFillerFamilyInitInstruction p,
            (compactNonAlphaCodesExecutable p).map compactFillerFamilyBetaInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hBetaInstructions
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons compactFillerFamilyInstructionEncodedType)
      hConsInput
  simpa [Function.comp, compactFillerFamilyInstructions,
    compactFillerFamilyInstructionListEncodedType, X] using hCons

theorem compactFillerFamilyStepLeft_tm_polytime :
    TMPolyTimeMap
      compactFillerFamilyContextEncodedType
      compactFillerFamilyAccEncodedType
      (fun ctx : CompactFillerFamilyContext =>
        (ctx, ([] : List (Nat × Nat × Nat)))) := by
  have hCtx := TMPolyTimeMap.id compactFillerFamilyContextEncodedType
  have hEmpty :
      TMPolyTimeMap compactFillerFamilyContextEncodedType tripleListStructuredEncodedType
        (fun _ : CompactFillerFamilyContext => ([] : List (Nat × Nat × Nat))) :=
    TMPolyTimeMap.const compactFillerFamilyContextEncodedType tripleListStructuredEncodedType []
  simpa [compactFillerFamilyAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hEmpty

theorem compactFillerFamilyBetaStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactFillerFamilyAccEncodedType EncodedType.nat)
      compactFillerFamilyAccEncodedType
      compactFillerFamilyBetaStep := by
  let X := EncodedType.prod compactFillerFamilyAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactFillerFamilyAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactFillerFamilyAccEncodedType EncodedType.nat
  have hBeta : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactFillerFamilyAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X compactFillerFamilyContextEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst compactFillerFamilyContextEncodedType
      tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactFillerFamilyAccEncodedType, X] using hComp
  have hOut : TMPolyTimeMap X tripleListStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd compactFillerFamilyContextEncodedType
      tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactFillerFamilyAccEncodedType, X] using hComp
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, compactFillerFamilyContextEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
        (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, compactFillerFamilyContextEncodedType, X] using hComp
  have hSetCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hFamilyInput :
      TMPolyTimeMap X compactFillerBetaFamilyInputEncodedType
        (fun p : X.Carrier => (p.1.1.1, p.2, p.1.1.2.1, p.1.1.2.2)) := by
    have hSetPayload :
        TMPolyTimeMap X (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
          (fun p : X.Carrier => (p.1.1.2.1, p.1.1.2.2)) :=
      TMPolyTimeMap.prod_mk hSetCount hSets
    have hTail :
        TMPolyTimeMap X
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType))
          (fun p : X.Carrier => (p.2, (p.1.1.2.1, p.1.1.2.2))) :=
      TMPolyTimeMap.prod_mk hBeta hSetPayload
    simpa [compactFillerBetaFamilyInputEncodedType,
      compactFillerBetaFamilyContextEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse hTail
  have hBlock :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier =>
          compactFillerTriplesForBetaExecutable
            (p.1.1.1, p.2, p.1.1.2.1, p.1.1.2.2)) := by
    have hComp := TMPolyTimeMap.comp
      compactFillerTriplesForBetaExecutable_tm_polytime hFamilyInput
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show List (Nat × Nat × Nat) from p.1.2),
            compactFillerTriplesForBetaExecutable
              (p.1.1.1, p.2, p.1.1.2.1, p.1.1.2.2))) :=
    TMPolyTimeMap.prod_mk hOut hBlock
  have hAppend :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat × Nat) from p.1.2) ++
            compactFillerTriplesForBetaExecutable
              (p.1.1.1, p.2, p.1.1.2.1, p.1.1.2.2)) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append tripleStructuredEncodedType) hAppendInput
    simpa [Function.comp, tripleListStructuredEncodedType, X] using hComp
  have hPair := TMPolyTimeMap.prod_mk hCtx hAppend
  simpa [compactFillerFamilyBetaStep, compactFillerFamilyAccEncodedType, X] using hPair

theorem compactFillerFamilyStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactFillerFamilyAccEncodedType
        compactFillerFamilyInstructionEncodedType)
      compactFillerFamilyAccEncodedType
      compactFillerFamilyStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      compactFillerFamilyAccEncodedType compactFillerFamilyContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim compactFillerFamilyStepLeft_tm_polytime
      compactFillerFamilyBetaStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def compactFillerFamilyFoldInv
    (N : Nat) (acc : compactFillerFamilyAccEncodedType.Carrier) : Prop :=
  acc = compactFillerFamilyInitAcc ∨
    ((show Nat from acc.1.1) + 1 ≤ N ∧
      (show Nat from acc.1.2.1) + 1 ≤ N ∧
      setFamilyStructuredEncodedType.inputSize
        (show List (List Nat) from acc.1.2.2) ≤ N)

theorem compactFillerFamilyInitAcc_bound
    (xs : List compactFillerFamilyInstructionEncodedType.Carrier) :
    compactFillerFamilyFoldInv
        (compactFillerFamilyInstructionListEncodedType.inputSize xs)
        compactFillerFamilyInitAcc ∧
      compactFillerFamilyAccEncodedType.inputSize compactFillerFamilyInitAcc ≤
        (Polynomial.C 10).eval
          (compactFillerFamilyInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · have hNilTriples :
        tripleStructuredEncodedType.list.inputSize ([] : List (Nat × Nat × Nat)) = 0 :=
      EncodedType.inputSize_list_nil tripleStructuredEncodedType
    have hNilSets :
        setStructuredEncodedType.list.inputSize ([] : List (List Nat)) = 0 :=
      EncodedType.inputSize_list_nil setStructuredEncodedType
    simp [compactFillerFamilyInitAcc, compactFillerFamilyAccEncodedType,
      compactFillerFamilyContextEncodedType, compactPositionFamilyContextEncodedType,
      tripleListStructuredEncodedType, setFamilyStructuredEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat, hNilTriples, hNilSets]

theorem compactFillerFamilyStep_growth
    (source : List compactFillerFamilyInstructionEncodedType.Carrier)
    (acc : compactFillerFamilyAccEncodedType.Carrier)
    (instr : compactFillerFamilyInstructionEncodedType.Carrier)
    (hInv :
      compactFillerFamilyFoldInv
        (compactFillerFamilyInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactFillerFamilyInstructionEncodedType.inputSize instr ≤
        compactFillerFamilyInstructionListEncodedType.inputSize source) :
    compactFillerFamilyFoldInv
        (compactFillerFamilyInstructionListEncodedType.inputSize source)
        (compactFillerFamilyStep (acc, instr)) ∧
      compactFillerFamilyAccEncodedType.inputSize
          (compactFillerFamilyStep (acc, instr)) ≤
        compactFillerFamilyAccEncodedType.inputSize acc +
          (Polynomial.C 100 *
              (Polynomial.X * (Polynomial.X * (Polynomial.X * Polynomial.X))) +
            Polynomial.C 100).eval
            (compactFillerFamilyInstructionListEncodedType.inputSize source) := by
  let N := compactFillerFamilyInstructionListEncodedType.inputSize source
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
          compactFillerFamilyContextEncodedType.inputSize
              (newUniverse, newSetCount, newSets) + 1 ≤ N := by
        simpa [N, compactFillerFamilyInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hInstr
      have hNewUniverse : newUniverse + 1 ≤ N := by
        simp [compactFillerFamilyContextEncodedType, compactPositionFamilyContextEncodedType,
          EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCtx
        omega
      have hNewSetCount : newSetCount + 1 ≤ N := by
        simp [compactFillerFamilyContextEncodedType, compactPositionFamilyContextEncodedType,
          EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCtx
        omega
      have hNewSets : setFamilyStructuredEncodedType.inputSize newSets ≤ N := by
        simp [compactFillerFamilyContextEncodedType, compactPositionFamilyContextEncodedType,
          EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCtx
        omega
      constructor
      · exact Or.inr ⟨hNewUniverse, hNewSetCount, hNewSets⟩
      · have hNilTriples :
            tripleStructuredEncodedType.list.inputSize ([] : List (Nat × Nat × Nat)) = 0 :=
          EncodedType.inputSize_list_nil tripleStructuredEncodedType
        have hNewAcc :
            compactFillerFamilyAccEncodedType.inputSize
                ((newUniverse, newSetCount, newSets),
                  ([] : List (Nat × Nat × Nat))) ≤ N := by
          simpa [compactFillerFamilyAccEncodedType,
            compactFillerFamilyContextEncodedType, compactPositionFamilyContextEncodedType,
            tripleListStructuredEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_nat, hNilTriples] using hCtx
        have hPolyN :
            N ≤ compactFillerFamilyAccEncodedType.inputSize
                ((universeSize, setCount, sets), out) +
              (Polynomial.C 100 *
                  (Polynomial.X * (Polynomial.X * (Polynomial.X * Polynomial.X))) +
                Polynomial.C 100).eval N := by
          have hBase :
              N ≤
                (Polynomial.C 100 *
                    (Polynomial.X * (Polynomial.X * (Polynomial.X * Polynomial.X))) +
                  Polynomial.C 100).eval N := by
            have hN : 1 ≤ N := by omega
            have hN2 : N ≤ N * N := Nat.le_mul_of_pos_right N hN
            have hN3 : N * N ≤ N * (N * N) := Nat.mul_le_mul_left N hN2
            have hN4 : N * (N * N) ≤ N * (N * (N * N)) :=
              Nat.mul_le_mul_left N hN3
            have hNle4 : N ≤ N * (N * (N * N)) := hN2.trans (hN3.trans hN4)
            simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
            omega
          exact hBase.trans (Nat.le_add_left _ _)
        simpa [compactFillerFamilyStep, N] using
          hNewAcc.trans (by simpa [N] using hPolyN)
  | inr beta =>
      change Nat at beta
      have hBeta : beta + 1 ≤ N := by
        have hTagged : beta + 1 < N := by
          simpa [N, compactFillerFamilyInstructionEncodedType, EncodedType.inputSize,
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
      let block := compactFillerTriplesForBetaExecutable (universeSize, beta, setCount, sets)
      have hBlock :
          tripleListStructuredEncodedType.inputSize block ≤
            100 * (N * (N * (N * N))) + 100 := by
        simpa [block] using
          compactFillerTriplesForBetaExecutable_inputSize_le
            N universeSize beta setCount sets hBounds.1 hBeta hBounds.2.1
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
            tripleListStructuredEncodedType.inputSize out +
              (100 * (N * (N * (N * N))) + 100) := by
        rw [hAppendSize]
        exact Nat.add_le_add_left hBlock _
      constructor
      · exact Or.inr hBounds
      · change
          compactFillerFamilyAccEncodedType.inputSize
              ((universeSize, setCount, sets),
                (show List (Nat × Nat × Nat) from out) ++ block) ≤
            compactFillerFamilyAccEncodedType.inputSize
                ((universeSize, setCount, sets), out) +
              (Polynomial.C 100 *
                  (Polynomial.X * (Polynomial.X * (Polynomial.X * Polynomial.X))) +
                Polynomial.C 100).eval N
        simp [compactFillerFamilyAccEncodedType, compactFillerFamilyContextEncodedType,
          compactPositionFamilyContextEncodedType, EncodedType.inputSize_prod,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hAppendLe ⊢
        omega

theorem compactFillerFamilyFold_tm_polytime :
    TMPolyTimeMap
      compactFillerFamilyInstructionListEncodedType
      compactFillerFamilyAccEncodedType
      (fun xs : List compactFillerFamilyInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactFillerFamilyStep (acc, instr))
          compactFillerFamilyInitAcc) := by
  rcases compactFillerFamilyStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactFillerFamilyInstructionEncodedType compactFillerFamilyAccEncodedType
      compactFillerFamilyStep compactFillerFamilyInitAcc hStep
      (Polynomial.C 10)
      (Polynomial.C 100 *
          (Polynomial.X * (Polynomial.X * (Polynomial.X * Polynomial.X))) +
        Polynomial.C 100)
      compactFillerFamilyFoldInv ?_ ?_
  · intro xs
    exact compactFillerFamilyInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactFillerFamilyStep_growth source acc instr hInv hInstr

theorem compactFillerFamilyFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactFillerFamilyInstructionListEncodedType
      tripleListStructuredEncodedType
      compactFillerFamilyFromInstructions := by
  have hFold := compactFillerFamilyFold_tm_polytime
  have hSnd :=
    TMPolyTimeMap.snd compactFillerFamilyContextEncodedType tripleListStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, compactFillerFamilyFromInstructions,
    compactFillerFamilyAccEncodedType] using hComp

theorem compactFillerTriplesExecutable_tm_polytime :
    TMPolyTimeMap
      compactFillerFamilyInputEncodedType
      tripleListStructuredEncodedType
      compactFillerTriplesExecutable := by
  have hComp :=
    TMPolyTimeMap.comp compactFillerFamilyFromInstructions_tm_polytime
      compactFillerFamilyInstructions_tm_polytime
  simpa [Function.comp, compactFillerTriplesExecutable] using hComp

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
