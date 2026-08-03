/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.CoverBlocks
import ComplexityReduction.Karp21.SteinerTreeStructuredTM.Lookup

/-!
Family-level cover-triple assembly for the compact
Exact-Cover-to-3-Dimensional-Matching route.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactCoverFamilyContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)

def compactCoverFamilyAccEncodedType : EncodedType :=
  EncodedType.prod compactCoverFamilyContextEncodedType tripleListStructuredEncodedType

def compactCoverFamilyInstructionEncodedType : EncodedType :=
  EncodedType.sum compactCoverFamilyContextEncodedType EncodedType.nat

def compactCoverFamilyInstructionListEncodedType : EncodedType :=
  EncodedType.list compactCoverFamilyInstructionEncodedType

def compactCoverFamilyInputEncodedType : EncodedType :=
  compactCoverFamilyContextEncodedType

abbrev CompactCoverFamilyContext := Nat × Nat × List (List Nat)
abbrev CompactCoverFamilyAcc := CompactCoverFamilyContext × List (Nat × Nat × Nat)

def compactCoverFamilyInitAcc : CompactCoverFamilyAcc :=
  ((0, (0, [])), [])

def compactCoverFamilyInitInstruction (ctx : CompactCoverFamilyContext) :
    compactCoverFamilyInstructionEncodedType.Carrier :=
  Sum.inl ctx

def compactCoverFamilyIndexInstruction (j : Nat) :
    compactCoverFamilyInstructionEncodedType.Carrier :=
  Sum.inr j

def compactCoverFamilyInstructions (p : CompactCoverFamilyContext) :
    List compactCoverFamilyInstructionEncodedType.Carrier :=
  compactCoverFamilyInitInstruction p ::
    (List.range p.2.1).map compactCoverFamilyIndexInstruction

def compactCoverFamilyIndexStep (p : CompactCoverFamilyAcc × Nat) :
    CompactCoverFamilyAcc :=
  let ctx := p.1.1
  let out := p.1.2
  let j := p.2
  let S := SteinerTree.setFamilyGetD (ctx.2.2, j)
  (ctx, out ++ compactCoverTriplesForSourceSetExecutable (ctx.1, ctx.2.2, j, S))

def compactCoverFamilyStep
    (p : CompactCoverFamilyAcc × compactCoverFamilyInstructionEncodedType.Carrier) :
    CompactCoverFamilyAcc :=
  match p.2 with
  | Sum.inl ctx => (ctx, [])
  | Sum.inr j => compactCoverFamilyIndexStep (p.1, j)

def compactCoverFamilyFromInstructions
    (xs : List compactCoverFamilyInstructionEncodedType.Carrier) :
    List (Nat × Nat × Nat) :=
  (xs.foldl (fun acc instr => compactCoverFamilyStep (acc, instr))
    compactCoverFamilyInitAcc).2

def compactCoverTriplesExecutable (p : CompactCoverFamilyContext) :
    List (Nat × Nat × Nat) :=
  compactCoverFamilyFromInstructions (compactCoverFamilyInstructions p)

/-! ### Semantics -/

theorem compactCoverFamilyIndexFold_eq_append_flatMap
    (ctx : CompactCoverFamilyContext) (xs : List Nat) (out : List (Nat × Nat × Nat)) :
    ((xs.map compactCoverFamilyIndexInstruction).foldl
        (fun acc instr => compactCoverFamilyStep (acc, instr)) (ctx, out)).2 =
      out ++ xs.flatMap (fun j =>
        compactCoverTriplesForSourceSetExecutable
          (ctx.1, ctx.2.2, j, SteinerTree.setFamilyGetD (ctx.2.2, j))) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons j js ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [compactCoverFamilyIndexInstruction, compactCoverFamilyStep,
        compactCoverFamilyIndexStep]
      have hTail := ih (out ++
        compactCoverTriplesForSourceSetExecutable
          (ctx.1, ctx.2.2, j, SteinerTree.setFamilyGetD (ctx.2.2, j)))
      simpa [List.append_assoc] using hTail

theorem compactCoverTriplesExecutable_eq_flatMap
    (p : CompactCoverFamilyContext) :
    compactCoverTriplesExecutable p =
      (List.range p.2.1).flatMap (fun j =>
        compactCoverTriplesForSourceSetExecutable
          (p.1, p.2.2, j, SteinerTree.setFamilyGetD (p.2.2, j))) := by
  change
    (((List.range p.2.1).map compactCoverFamilyIndexInstruction).foldl
        (fun acc instr => compactCoverFamilyStep (acc, instr)) (p, [])).2 =
      (List.range p.2.1).flatMap (fun j =>
        compactCoverTriplesForSourceSetExecutable
          (p.1, p.2.2, j, SteinerTree.setFamilyGetD (p.2.2, j)))
  simpa using compactCoverFamilyIndexFold_eq_append_flatMap p (List.range p.2.1) []

theorem compactCoverTriplesExecutable_eq_compactCoverTriples_tail (I : ExactCoverInput) :
    compactCoverTriplesExecutable
        (I.system.universeSize, I.system.sets.length, I.system.sets) =
      (List.range I.system.sets.length).flatMap (compactCoverTriplesForSet I) := by
  rw [compactCoverTriplesExecutable_eq_flatMap]
  apply List.flatMap_congr
  intro j hj
  have hjLt : j < I.system.sets.length := by
    simpa using hj
  have hGet :
      SteinerTree.setFamilyGetD (I.system.sets, j) = compactSourceSetAt I j := by
    rfl
  rw [hGet]
  exact compactCoverTriplesForSourceSetExecutable_eq_compactCoverTriplesForSet
    (I := I) hjLt

theorem compactCoverTriplesExecutable_eq_compactCoverTriples (I : ExactCoverInput) :
    compactCoverTriplesExecutable
        (I.system.universeSize, I.system.sets.length, I.system.sets) =
      compactCoverTriples I := by
  simpa [compactCoverTriples] using compactCoverTriplesExecutable_eq_compactCoverTriples_tail I

/-! ### Local size facts for the fold -/

theorem mem_compactSupportExecutable_lt {bound : Nat} {S : List Nat} {x : Nat}
    (hx : x ∈ compactSupportExecutable (bound, S)) :
    x < bound := by
  rw [compactSupportExecutable_eq_filter] at hx
  simp only [List.mem_filter, List.mem_range] at hx
  exact hx.1

theorem compactSupportExecutable_length_le (bound : Nat) (S : List Nat) :
    (compactSupportExecutable (bound, S)).length ≤ bound := by
  rw [compactSupportExecutable_eq_filter]
  exact (List.length_filter_le _ _).trans_eq (by simp)

theorem compactCoverTriplesForSourceSetExecutable_inputSize_le
    (N universeSize : Nat) (sets : List (List Nat)) (j : Nat) (S : List Nat)
    (hUniverse : universeSize + 1 ≤ N)
    (hSets : setFamilyStructuredEncodedType.inputSize sets ≤ N)
    (hj : j + 1 ≤ N) :
    tripleListStructuredEncodedType.inputSize
        (compactCoverTriplesForSourceSetExecutable (universeSize, sets, j, S)) ≤
      200 * (N * (N * (N * N))) + 200 := by
  let block := compactCoverTriplesForSourceSetExecutable (universeSize, sets, j, S)
  have hLen : block.length ≤ N := by
    have hSupport := compactSupportExecutable_length_le universeSize S
    dsimp [block]
    rw [compactCoverTriplesForSourceSetExecutable_eq_map]
    simp
    omega
  have hEach :
      ∀ t ∈ block, tripleStructuredEncodedType.inputSize t ≤ 100 * (N * (N * N)) := by
    intro t ht
    dsimp [block] at ht
    rw [compactCoverTriplesForSourceSetExecutable_eq_map] at ht
    simp only [List.mem_map] at ht
    rcases ht with ⟨x, hx, rfl⟩
    have hxLt := mem_compactSupportExecutable_lt hx
    have hxN : x + 2 ≤ N := by omega
    exact compactCoverTripleFromData_inputSize_le N universeSize sets j x
      hUniverse hSets hj hxN
  have hList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      tripleStructuredEncodedType block (100 * (N * (N * N))) hEach
  have hPoly :
      block.length * (100 * (N * (N * N)) + 1) ≤
        200 * (N * (N * (N * N))) + 200 := by
    have hN : 1 ≤ N := by omega
    have hLenBound :
        block.length * (100 * (N * (N * N)) + 1) ≤
          N * (100 * (N * (N * N)) + 1) :=
      Nat.mul_le_mul_right _ hLen
    have hBase :
        N * (100 * (N * (N * N)) + 1) ≤
          200 * (N * (N * (N * N))) + 200 := by
      have hN2 : N ≤ N * N := Nat.le_mul_of_pos_right N hN
      have hN3 : N * N ≤ N * (N * N) := Nat.mul_le_mul_left N hN2
      have hN4 : N * (N * N) ≤ N * (N * (N * N)) :=
        Nat.mul_le_mul_left N hN3
      have hNle4 : N ≤ N * (N * (N * N)) := hN2.trans (hN3.trans hN4)
      calc
        N * (100 * (N * (N * N)) + 1)
            = 100 * (N * (N * (N * N))) + N := by ring
        _ ≤ 200 * (N * (N * (N * N))) + 200 := by omega
    exact hLenBound.trans hBase
  exact hList.trans hPoly

/-! ### TM witnesses -/

theorem compactCoverFamilyInitInstruction_tm_polytime :
    TMPolyTimeMap
      compactCoverFamilyContextEncodedType
      compactCoverFamilyInstructionEncodedType
      compactCoverFamilyInitInstruction := by
  simpa [compactCoverFamilyInstructionEncodedType, compactCoverFamilyInitInstruction] using
    TMPolyTimeMap.inl compactCoverFamilyContextEncodedType EncodedType.nat

theorem compactCoverFamilyIndexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactCoverFamilyInstructionEncodedType
      compactCoverFamilyIndexInstruction := by
  simpa [compactCoverFamilyInstructionEncodedType, compactCoverFamilyIndexInstruction] using
    TMPolyTimeMap.inr compactCoverFamilyContextEncodedType EncodedType.nat

theorem compactCoverFamilyInstructions_tm_polytime :
    TMPolyTimeMap
      compactCoverFamilyInputEncodedType
      compactCoverFamilyInstructionListEncodedType
      compactCoverFamilyInstructions := by
  let X := compactCoverFamilyInputEncodedType
  have hCtx : TMPolyTimeMap X compactCoverFamilyContextEncodedType (fun p : X.Carrier => p) :=
    TMPolyTimeMap.id X
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
        (fun p : X.Carrier => p.2) := by
    simpa [X, compactCoverFamilyInputEncodedType, compactCoverFamilyContextEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
  have hSetCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hInit :
      TMPolyTimeMap X compactCoverFamilyInstructionEncodedType
        (fun p : X.Carrier => compactCoverFamilyInitInstruction p) := by
    have hComp := TMPolyTimeMap.comp compactCoverFamilyInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => List.range p.2.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hSetCount
    simpa [Function.comp, X] using hComp
  have hIndexInstructions :
      TMPolyTimeMap X compactCoverFamilyInstructionListEncodedType
        (fun p : X.Carrier => (List.range p.2.1).map compactCoverFamilyIndexInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactCoverFamilyIndexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, compactCoverFamilyInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactCoverFamilyInstructionEncodedType
          compactCoverFamilyInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactCoverFamilyInitInstruction p,
            (List.range p.2.1).map compactCoverFamilyIndexInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hIndexInstructions
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons compactCoverFamilyInstructionEncodedType)
      hConsInput
  simpa [Function.comp, compactCoverFamilyInstructions,
    compactCoverFamilyInstructionListEncodedType, X] using hCons

theorem compactCoverFamilyStepLeft_tm_polytime :
    TMPolyTimeMap
      compactCoverFamilyContextEncodedType
      compactCoverFamilyAccEncodedType
      (fun ctx : CompactCoverFamilyContext => (ctx, ([] : List (Nat × Nat × Nat)))) := by
  have hCtx := TMPolyTimeMap.id compactCoverFamilyContextEncodedType
  have hEmpty :
      TMPolyTimeMap compactCoverFamilyContextEncodedType tripleListStructuredEncodedType
        (fun _ : CompactCoverFamilyContext => ([] : List (Nat × Nat × Nat))) :=
    TMPolyTimeMap.const compactCoverFamilyContextEncodedType tripleListStructuredEncodedType []
  simpa [compactCoverFamilyAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hEmpty

theorem compactCoverFamilyIndexStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactCoverFamilyAccEncodedType EncodedType.nat)
      compactCoverFamilyAccEncodedType
      compactCoverFamilyIndexStep := by
  let X := EncodedType.prod compactCoverFamilyAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactCoverFamilyAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactCoverFamilyAccEncodedType EncodedType.nat
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactCoverFamilyAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X compactCoverFamilyContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst compactCoverFamilyContextEncodedType tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactCoverFamilyAccEncodedType, X] using hComp
  have hOut : TMPolyTimeMap X tripleListStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd compactCoverFamilyContextEncodedType tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactCoverFamilyAccEncodedType, X] using hComp
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, compactCoverFamilyContextEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
        (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, compactCoverFamilyContextEncodedType, X] using hComp
  have hSetCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
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
      TMPolyTimeMap X compactCoverBlockInputEncodedType
        (fun p : X.Carrier =>
          (p.1.1.1, p.1.1.2.2, p.2, SteinerTree.setFamilyGetD (p.1.1.2.2, p.2))) := by
    have hInner :
        TMPolyTimeMap X (EncodedType.prod EncodedType.nat setStructuredEncodedType)
          (fun p : X.Carrier => (p.2, SteinerTree.setFamilyGetD (p.1.1.2.2, p.2))) :=
      TMPolyTimeMap.prod_mk hJ hSet
    simpa [compactCoverBlockInputEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse (TMPolyTimeMap.prod_mk hSets hInner)
  have hBlock :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier =>
          compactCoverTriplesForSourceSetExecutable
            (p.1.1.1, p.1.1.2.2, p.2, SteinerTree.setFamilyGetD (p.1.1.2.2, p.2))) := by
    have hComp := TMPolyTimeMap.comp
      compactCoverTriplesForSourceSetExecutable_tm_polytime hBlockInput
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show List (Nat × Nat × Nat) from p.1.2),
            compactCoverTriplesForSourceSetExecutable
              (p.1.1.1, p.1.1.2.2, p.2,
                SteinerTree.setFamilyGetD (p.1.1.2.2, p.2)))) :=
    TMPolyTimeMap.prod_mk hOut hBlock
  have hAppend :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat × Nat) from p.1.2) ++
            compactCoverTriplesForSourceSetExecutable
              (p.1.1.1, p.1.1.2.2, p.2,
                SteinerTree.setFamilyGetD (p.1.1.2.2, p.2))) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append tripleStructuredEncodedType) hAppendInput
    simpa [Function.comp, tripleListStructuredEncodedType, X] using hComp
  have hPair := TMPolyTimeMap.prod_mk hCtx hAppend
  simpa [compactCoverFamilyIndexStep, compactCoverFamilyAccEncodedType, X] using hPair

theorem compactCoverFamilyStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactCoverFamilyAccEncodedType compactCoverFamilyInstructionEncodedType)
      compactCoverFamilyAccEncodedType
      compactCoverFamilyStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      compactCoverFamilyAccEncodedType compactCoverFamilyContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim compactCoverFamilyStepLeft_tm_polytime
      compactCoverFamilyIndexStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def compactCoverFamilyFoldInv
    (N : Nat) (acc : compactCoverFamilyAccEncodedType.Carrier) : Prop :=
  acc = compactCoverFamilyInitAcc ∨
    ((show Nat from acc.1.1) + 1 ≤ N ∧
      (show Nat from acc.1.2.1) + 1 ≤ N ∧
      setFamilyStructuredEncodedType.inputSize (show List (List Nat) from acc.1.2.2) ≤ N)

theorem compactCoverFamilyInitAcc_bound
    (xs : List compactCoverFamilyInstructionEncodedType.Carrier) :
    compactCoverFamilyFoldInv (compactCoverFamilyInstructionListEncodedType.inputSize xs)
        compactCoverFamilyInitAcc ∧
      compactCoverFamilyAccEncodedType.inputSize compactCoverFamilyInitAcc ≤
        (Polynomial.C 10).eval (compactCoverFamilyInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · have hNilTriples :
        tripleStructuredEncodedType.list.inputSize ([] : List (Nat × Nat × Nat)) = 0 :=
      EncodedType.inputSize_list_nil tripleStructuredEncodedType
    have hNilSets :
        setStructuredEncodedType.list.inputSize ([] : List (List Nat)) = 0 :=
      EncodedType.inputSize_list_nil setStructuredEncodedType
    simp [compactCoverFamilyInitAcc, compactCoverFamilyAccEncodedType,
      compactCoverFamilyContextEncodedType, tripleListStructuredEncodedType,
      setFamilyStructuredEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat, hNilTriples, hNilSets]

theorem compactCoverFamilyStep_growth
    (source : List compactCoverFamilyInstructionEncodedType.Carrier)
    (acc : compactCoverFamilyAccEncodedType.Carrier)
    (instr : compactCoverFamilyInstructionEncodedType.Carrier)
    (hInv :
      compactCoverFamilyFoldInv
        (compactCoverFamilyInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactCoverFamilyInstructionEncodedType.inputSize instr ≤
        compactCoverFamilyInstructionListEncodedType.inputSize source) :
    compactCoverFamilyFoldInv
        (compactCoverFamilyInstructionListEncodedType.inputSize source)
        (compactCoverFamilyStep (acc, instr)) ∧
      compactCoverFamilyAccEncodedType.inputSize (compactCoverFamilyStep (acc, instr)) ≤
        compactCoverFamilyAccEncodedType.inputSize acc +
          (Polynomial.C 200 *
              (Polynomial.X * (Polynomial.X * (Polynomial.X * Polynomial.X))) +
            Polynomial.C 200).eval
            (compactCoverFamilyInstructionListEncodedType.inputSize source) := by
  let N := compactCoverFamilyInstructionListEncodedType.inputSize source
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
          compactCoverFamilyContextEncodedType.inputSize
              (newUniverse, newSetCount, newSets) + 1 ≤ N := by
        simpa [N, compactCoverFamilyInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hInstr
      have hNewUniverse : newUniverse + 1 ≤ N := by
        simp [compactCoverFamilyContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewSetCount : newSetCount + 1 ≤ N := by
        simp [compactCoverFamilyContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewSets : setFamilyStructuredEncodedType.inputSize newSets ≤ N := by
        simp [compactCoverFamilyContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      constructor
      · exact Or.inr ⟨hNewUniverse, hNewSetCount, hNewSets⟩
      · have hNilTriples :
            tripleStructuredEncodedType.list.inputSize ([] : List (Nat × Nat × Nat)) = 0 :=
          EncodedType.inputSize_list_nil tripleStructuredEncodedType
        have hNewAcc :
            compactCoverFamilyAccEncodedType.inputSize
                ((newUniverse, newSetCount, newSets), ([] : List (Nat × Nat × Nat))) ≤ N := by
          simpa [compactCoverFamilyAccEncodedType, compactCoverFamilyContextEncodedType,
            tripleListStructuredEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_nat, hNilTriples] using hCtx
        have hPolyN :
            N ≤ compactCoverFamilyAccEncodedType.inputSize ((universeSize, setCount, sets), out) +
              (Polynomial.C 200 *
                  (Polynomial.X * (Polynomial.X * (Polynomial.X * Polynomial.X))) +
                Polynomial.C 200).eval N := by
          have hBase :
              N ≤
                (Polynomial.C 200 *
                    (Polynomial.X * (Polynomial.X * (Polynomial.X * Polynomial.X))) +
                  Polynomial.C 200).eval N := by
            have hN : 1 ≤ N := by omega
            have hN2 : N ≤ N * N := Nat.le_mul_of_pos_right N hN
            have hN3 : N * N ≤ N * (N * N) := Nat.mul_le_mul_left N hN2
            have hN4 : N * (N * N) ≤ N * (N * (N * N)) :=
              Nat.mul_le_mul_left N hN3
            have hNle4 : N ≤ N * (N * (N * N)) := hN2.trans (hN3.trans hN4)
            simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
            omega
          exact hBase.trans (Nat.le_add_left _ _)
        simpa [compactCoverFamilyStep, N] using hNewAcc.trans (by simpa [N] using hPolyN)
  | inr j =>
      change Nat at j
      have hj : j + 1 ≤ N := by
        have hjTagged : j + 1 < N := by
          simpa [N, compactCoverFamilyInstructionEncodedType, EncodedType.inputSize,
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
      let block := compactCoverTriplesForSourceSetExecutable (universeSize, sets, j, S)
      have hBlock :
          tripleListStructuredEncodedType.inputSize block ≤
            200 * (N * (N * (N * N))) + 200 := by
        simpa [block, S] using
          compactCoverTriplesForSourceSetExecutable_inputSize_le
            N universeSize sets j S hBounds.1 hBounds.2.2 hj
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
              (200 * (N * (N * (N * N))) + 200) := by
        rw [hAppendSize]
        exact Nat.add_le_add_left hBlock _
      constructor
      · exact Or.inr hBounds
      · change
          compactCoverFamilyAccEncodedType.inputSize
              ((universeSize, setCount, sets),
                (show List (Nat × Nat × Nat) from out) ++ block) ≤
            compactCoverFamilyAccEncodedType.inputSize ((universeSize, setCount, sets), out) +
              (Polynomial.C 200 *
                  (Polynomial.X * (Polynomial.X * (Polynomial.X * Polynomial.X))) +
                Polynomial.C 200).eval N
        simp [compactCoverFamilyAccEncodedType, EncodedType.inputSize_prod,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hAppendLe ⊢
        omega

theorem compactCoverFamilyFold_tm_polytime :
    TMPolyTimeMap
      compactCoverFamilyInstructionListEncodedType
      compactCoverFamilyAccEncodedType
      (fun xs : List compactCoverFamilyInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactCoverFamilyStep (acc, instr))
          compactCoverFamilyInitAcc) := by
  rcases compactCoverFamilyStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactCoverFamilyInstructionEncodedType compactCoverFamilyAccEncodedType
      compactCoverFamilyStep compactCoverFamilyInitAcc hStep
      (Polynomial.C 10)
      (Polynomial.C 200 *
          (Polynomial.X * (Polynomial.X * (Polynomial.X * Polynomial.X))) +
        Polynomial.C 200)
      compactCoverFamilyFoldInv ?_ ?_
  · intro xs
    exact compactCoverFamilyInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactCoverFamilyStep_growth source acc instr hInv hInstr

theorem compactCoverFamilyFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactCoverFamilyInstructionListEncodedType
      tripleListStructuredEncodedType
      compactCoverFamilyFromInstructions := by
  have hFold := compactCoverFamilyFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd compactCoverFamilyContextEncodedType tripleListStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, compactCoverFamilyFromInstructions,
    compactCoverFamilyAccEncodedType] using hComp

theorem compactCoverTriplesExecutable_tm_polytime :
    TMPolyTimeMap
      compactCoverFamilyInputEncodedType
      tripleListStructuredEncodedType
      compactCoverTriplesExecutable := by
  have hComp :=
    TMPolyTimeMap.comp compactCoverFamilyFromInstructions_tm_polytime
      compactCoverFamilyInstructions_tm_polytime
  simpa [Function.comp, compactCoverTriplesExecutable] using hComp

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
