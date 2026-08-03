import ComplexityReduction.Karp21.ExactCover.StructuredTM.ChoiceBlock

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Executable row generator for block-input triples `(I, (left, right))`.

Both choice blocks and filler blocks consume the same tuple shape:
`ChromaticNumberInput × (Nat × Nat)`.  This module builds one row
`[(I,(left,0)), ..., (I,(left,rightCount-1))]` by a checked instruction fold.
-/

def colorDefaultChromaticInput : ChromaticNumberInput where
  graph := { vertices := 0, edges := [], directed := false }
  colors := 0

def colorBlockInputEncodedType : EncodedType :=
  colorChoiceCodeInputEncodedType

def colorBlockInputListEncodedType : EncodedType :=
  EncodedType.list colorBlockInputEncodedType

def colorBlockInputRowContextEncodedType : EncodedType :=
  colorBlockInputEncodedType

abbrev ColorBlockInputRowContext := ChromaticNumberInput × (Nat × Nat)

def colorBlockInputRowInstructionEncodedType : EncodedType :=
  EncodedType.sum colorBlockInputRowContextEncodedType EncodedType.nat

def colorBlockInputRowInstructionListEncodedType : EncodedType :=
  EncodedType.list colorBlockInputRowInstructionEncodedType

def colorBlockInputRowAccEncodedType : EncodedType :=
  EncodedType.prod colorBlockInputRowContextEncodedType colorBlockInputListEncodedType

def colorBlockInputRowZeroContext : ColorBlockInputRowContext :=
  (colorDefaultChromaticInput, (0, 0))

def colorBlockInputRowInitAcc : colorBlockInputRowAccEncodedType.Carrier :=
  (colorBlockInputRowZeroContext, [])

def colorBlockInputRowInitInstruction
    (ctx : ColorBlockInputRowContext) :
    colorBlockInputRowInstructionEncodedType.Carrier :=
  Sum.inl ctx

def colorBlockInputRowIndexInstruction
    (right : Nat) : colorBlockInputRowInstructionEncodedType.Carrier :=
  Sum.inr right

def colorBlockInputRowInstructions
    (ctx : ColorBlockInputRowContext) :
    List colorBlockInputRowInstructionEncodedType.Carrier :=
  colorBlockInputRowInitInstruction ctx ::
    (List.range ctx.2.2).map colorBlockInputRowIndexInstruction

def colorBlockInputOfRowContext
    (ctx : ColorBlockInputRowContext) (right : Nat) :
    colorBlockInputEncodedType.Carrier :=
  (ctx.1, (ctx.2.1, right))

def colorBlockInputRowStep
    (p : colorBlockInputRowAccEncodedType.Carrier ×
      colorBlockInputRowInstructionEncodedType.Carrier) :
    colorBlockInputRowAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl ctx => (ctx, [])
  | Sum.inr right =>
      (p.1.1, (show List colorBlockInputEncodedType.Carrier from p.1.2) ++
        [colorBlockInputOfRowContext p.1.1 right])

def colorBlockInputRowFromInstructions
    (xs : List colorBlockInputRowInstructionEncodedType.Carrier) :
    List colorBlockInputEncodedType.Carrier :=
  (xs.foldl (fun acc instr => colorBlockInputRowStep (acc, instr))
    colorBlockInputRowInitAcc).2

def colorBlockInputRowExecutable
    (ctx : ColorBlockInputRowContext) :
    List colorBlockInputEncodedType.Carrier :=
  colorBlockInputRowFromInstructions (colorBlockInputRowInstructions ctx)

/-! ### Semantics -/

theorem colorBlockInputRowIndexFold_eq_append_map
    (ctx : ColorBlockInputRowContext) (xs : List Nat)
    (out : List colorBlockInputEncodedType.Carrier) :
    ((xs.map colorBlockInputRowIndexInstruction).foldl
        (fun acc instr => colorBlockInputRowStep (acc, instr)) (ctx, out)).2 =
      out ++ xs.map (colorBlockInputOfRowContext ctx) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons right rest ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [colorBlockInputRowIndexInstruction, colorBlockInputRowStep]
      have hTail := ih (out ++ [colorBlockInputOfRowContext ctx right])
      simpa [List.append_assoc] using hTail

theorem colorBlockInputRowExecutable_eq_map
    (ctx : ColorBlockInputRowContext) :
    colorBlockInputRowExecutable ctx =
      (List.range ctx.2.2).map (colorBlockInputOfRowContext ctx) := by
  change
    (((List.range ctx.2.2).map colorBlockInputRowIndexInstruction).foldl
        (fun acc instr => colorBlockInputRowStep (acc, instr)) (ctx, [])).2 =
      (List.range ctx.2.2).map (colorBlockInputOfRowContext ctx)
  simpa using colorBlockInputRowIndexFold_eq_append_map ctx (List.range ctx.2.2) []

/-! ### TM witnesses -/

theorem colorBlockInputRowInitInstruction_tm_polytime :
    TMPolyTimeMap
      colorBlockInputRowContextEncodedType
      colorBlockInputRowInstructionEncodedType
      colorBlockInputRowInitInstruction := by
  simpa [colorBlockInputRowInstructionEncodedType, colorBlockInputRowInitInstruction] using
    TMPolyTimeMap.inl colorBlockInputRowContextEncodedType EncodedType.nat

theorem colorBlockInputRowIndexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      colorBlockInputRowInstructionEncodedType
      colorBlockInputRowIndexInstruction := by
  simpa [colorBlockInputRowInstructionEncodedType, colorBlockInputRowIndexInstruction] using
    TMPolyTimeMap.inr colorBlockInputRowContextEncodedType EncodedType.nat

theorem colorBlockInputRowInstructions_tm_polytime :
    TMPolyTimeMap
      colorBlockInputRowContextEncodedType
      colorBlockInputRowInstructionListEncodedType
      colorBlockInputRowInstructions := by
  let X := colorBlockInputRowContextEncodedType
  have hCtx : TMPolyTimeMap X X (fun ctx : X.Carrier => ctx) := TMPolyTimeMap.id X
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun ctx : X.Carrier => ctx.2) := by
    simpa [X, colorBlockInputRowContextEncodedType, colorBlockInputEncodedType,
      colorChoiceCodeInputEncodedType] using
      TMPolyTimeMap.snd chromaticNumberStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hRightCount : TMPolyTimeMap X EncodedType.nat (fun ctx : X.Carrier => ctx.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hInit :
      TMPolyTimeMap X colorBlockInputRowInstructionEncodedType
        (fun ctx : X.Carrier => colorBlockInputRowInitInstruction ctx) := by
    have hComp := TMPolyTimeMap.comp colorBlockInputRowInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun ctx : X.Carrier => List.range ctx.2.2) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hRightCount
    simpa [Function.comp, X] using hComp
  have hIndexInstructions :
      TMPolyTimeMap X colorBlockInputRowInstructionListEncodedType
        (fun ctx : X.Carrier =>
          (List.range ctx.2.2).map colorBlockInputRowIndexInstruction) := by
    have hMap := TMPolyTimeMap.list_map colorBlockInputRowIndexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, colorBlockInputRowInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod colorBlockInputRowInstructionEncodedType
          colorBlockInputRowInstructionListEncodedType)
        (fun ctx : X.Carrier =>
          (colorBlockInputRowInitInstruction ctx,
            (List.range ctx.2.2).map colorBlockInputRowIndexInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hIndexInstructions
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons colorBlockInputRowInstructionEncodedType)
      hConsInput
  simpa [Function.comp, colorBlockInputRowInstructions,
    colorBlockInputRowInstructionListEncodedType, X] using hCons

theorem colorBlockInputRowStepLeft_tm_polytime :
    TMPolyTimeMap
      colorBlockInputRowContextEncodedType
      colorBlockInputRowAccEncodedType
      (fun ctx : ColorBlockInputRowContext =>
        (ctx, ([] : List colorBlockInputEncodedType.Carrier))) := by
  have hCtx := TMPolyTimeMap.id colorBlockInputRowContextEncodedType
  have hEmpty :
      TMPolyTimeMap colorBlockInputRowContextEncodedType colorBlockInputListEncodedType
        (fun _ : ColorBlockInputRowContext =>
          ([] : List colorBlockInputEncodedType.Carrier)) :=
    TMPolyTimeMap.const colorBlockInputRowContextEncodedType colorBlockInputListEncodedType []
  simpa [colorBlockInputRowAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hEmpty

theorem colorBlockInputRowStepRight_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod colorBlockInputRowAccEncodedType EncodedType.nat)
      colorBlockInputRowAccEncodedType
      (fun p : colorBlockInputRowAccEncodedType.Carrier × Nat =>
        (p.1.1, (show List colorBlockInputEncodedType.Carrier from p.1.2) ++
          [colorBlockInputOfRowContext p.1.1 p.2])) := by
  let X := EncodedType.prod colorBlockInputRowAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X colorBlockInputRowAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst colorBlockInputRowAccEncodedType EncodedType.nat
  have hRight : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd colorBlockInputRowAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X colorBlockInputRowContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst colorBlockInputRowContextEncodedType
      colorBlockInputListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, colorBlockInputRowAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X colorBlockInputListEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd colorBlockInputRowContextEncodedType
      colorBlockInputListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, colorBlockInputRowAccEncodedType, X] using hComp
  have hSource :
      TMPolyTimeMap X chromaticNumberStructuredEncodedType (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst chromaticNumberStructuredEncodedType
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, colorBlockInputRowContextEncodedType, colorBlockInputEncodedType,
      colorChoiceCodeInputEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd chromaticNumberStructuredEncodedType
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, colorBlockInputRowContextEncodedType, colorBlockInputEncodedType,
      colorChoiceCodeInputEncodedType, X] using hComp
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.1.1.2.1, p.2)) :=
    TMPolyTimeMap.prod_mk hLeft hRight
  have hElem :
      TMPolyTimeMap X colorBlockInputEncodedType
        (fun p : X.Carrier => colorBlockInputOfRowContext p.1.1 p.2) := by
    simpa [colorBlockInputOfRowContext, colorBlockInputEncodedType,
      colorChoiceCodeInputEncodedType] using TMPolyTimeMap.prod_mk hSource hPair
  have hSingleton :
      TMPolyTimeMap X colorBlockInputListEncodedType
        (fun p : X.Carrier => [colorBlockInputOfRowContext p.1.1 p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton colorBlockInputEncodedType) hElem
    simpa [Function.comp, colorBlockInputListEncodedType] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod colorBlockInputListEncodedType colorBlockInputListEncodedType)
        (fun p : X.Carrier =>
          ((show List colorBlockInputEncodedType.Carrier from p.1.2),
            [colorBlockInputOfRowContext p.1.1 p.2])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X colorBlockInputListEncodedType
        (fun p : X.Carrier =>
          (show List colorBlockInputEncodedType.Carrier from p.1.2) ++
            [colorBlockInputOfRowContext p.1.1 p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append colorBlockInputEncodedType) hAppendInput
    simpa [Function.comp, colorBlockInputListEncodedType, X] using hComp
  simpa [colorBlockInputRowAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hAppend

theorem colorBlockInputRowStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod colorBlockInputRowAccEncodedType colorBlockInputRowInstructionEncodedType)
      colorBlockInputRowAccEncodedType
      colorBlockInputRowStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      colorBlockInputRowAccEncodedType colorBlockInputRowContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim colorBlockInputRowStepLeft_tm_polytime
      colorBlockInputRowStepRight_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def colorBlockInputRowFoldInv (N : Nat)
    (acc : colorBlockInputRowAccEncodedType.Carrier) : Prop :=
  acc = colorBlockInputRowInitAcc ∨
    acc.1 = colorBlockInputRowZeroContext ∨
    colorBlockInputRowContextEncodedType.inputSize acc.1 ≤ N

noncomputable def colorBlockInputRowFoldBase : Polynomial Nat := Polynomial.C 100

noncomputable def colorBlockInputRowFoldGrow : Polynomial Nat :=
  Polynomial.C 20 * Polynomial.X + Polynomial.C 200

@[simp] theorem colorBlockInputRowFoldGrow_eval (N : Nat) :
    colorBlockInputRowFoldGrow.eval N = 20 * N + 200 := by
  simp [colorBlockInputRowFoldGrow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

theorem colorBlockInputRowInitAcc_bound
    (xs : List colorBlockInputRowInstructionEncodedType.Carrier) :
    colorBlockInputRowFoldInv (colorBlockInputRowInstructionListEncodedType.inputSize xs)
        colorBlockInputRowInitAcc ∧
      colorBlockInputRowAccEncodedType.inputSize colorBlockInputRowInitAcc ≤
        colorBlockInputRowFoldBase.eval
          (colorBlockInputRowInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [colorBlockInputRowFoldBase]
    native_decide

theorem colorBlockInputOfRowContext_inputSize_le
    {N : Nat} {ctx : ColorBlockInputRowContext} {right : Nat}
    (hCtx : colorBlockInputRowContextEncodedType.inputSize ctx ≤ N)
    (hRight : EncodedType.nat.inputSize right ≤ N) :
    colorBlockInputEncodedType.inputSize (colorBlockInputOfRowContext ctx right) ≤
      4 * N + 10 := by
  rcases ctx with ⟨I, ⟨left, rightCount⟩⟩
  simp [colorBlockInputOfRowContext, colorBlockInputEncodedType,
    colorBlockInputRowContextEncodedType, colorChoiceCodeInputEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCtx hRight ⊢
  omega

theorem colorBlockInputOfZeroRowContext_inputSize_le
    {N right : Nat} (hRight : EncodedType.nat.inputSize right ≤ N) :
    colorBlockInputEncodedType.inputSize
        (colorBlockInputOfRowContext colorBlockInputRowZeroContext right) ≤
      4 * N + 10 := by
  have hZeroSource :
      chromaticNumberStructuredEncodedType.inputSize colorDefaultChromaticInput ≤ 10 := by
    native_decide
  simp [colorBlockInputOfRowContext, colorBlockInputRowZeroContext,
    colorBlockInputEncodedType, colorChoiceCodeInputEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hRight ⊢
  omega

theorem colorBlockInputRowStep_growth
    (source : List colorBlockInputRowInstructionEncodedType.Carrier)
    (acc : colorBlockInputRowAccEncodedType.Carrier)
    (instr : colorBlockInputRowInstructionEncodedType.Carrier)
    (hInv :
      colorBlockInputRowFoldInv
        (colorBlockInputRowInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      colorBlockInputRowInstructionEncodedType.inputSize instr ≤
        colorBlockInputRowInstructionListEncodedType.inputSize source) :
    colorBlockInputRowFoldInv
        (colorBlockInputRowInstructionListEncodedType.inputSize source)
        (colorBlockInputRowStep (acc, instr)) ∧
      colorBlockInputRowAccEncodedType.inputSize (colorBlockInputRowStep (acc, instr)) ≤
        colorBlockInputRowAccEncodedType.inputSize acc +
          colorBlockInputRowFoldGrow.eval
            (colorBlockInputRowInstructionListEncodedType.inputSize source) := by
  let N := colorBlockInputRowInstructionListEncodedType.inputSize source
  rcases acc with ⟨ctx, out⟩
  cases instr with
  | inl newCtx =>
      have hNewCtx : colorBlockInputRowContextEncodedType.inputSize newCtx ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, colorBlockInputRowInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum] using hInstr)
      constructor
      · exact Or.inr (Or.inr hNewCtx)
      · have hNewAcc :
            colorBlockInputRowAccEncodedType.inputSize
                (newCtx, ([] : List colorBlockInputEncodedType.Carrier)) ≤ N + 1 := by
          simp [colorBlockInputRowAccEncodedType, EncodedType.inputSize_prod,
            colorBlockInputListEncodedType, EncodedType.inputSize_list_nil]
          omega
        have hPoly :
            N + 1 ≤ colorBlockInputRowAccEncodedType.inputSize (ctx, out) +
              colorBlockInputRowFoldGrow.eval N := by
          rw [colorBlockInputRowFoldGrow_eval]
          omega
        simpa [colorBlockInputRowStep, N] using hNewAcc.trans hPoly
  | inr right =>
      have hRight : EncodedType.nat.inputSize right ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, colorBlockInputRowInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum] using hInstr)
      have hElem :
          colorBlockInputEncodedType.inputSize (colorBlockInputOfRowContext ctx right) ≤
            4 * N + 10 := by
        rcases hInv with hInit | hRest
        · injection hInit with hCtxEq _hOut
          rw [hCtxEq]
          exact colorBlockInputOfZeroRowContext_inputSize_le (N := N) hRight
        · rcases hRest with hZero | hCtx
          · have hCtxZero : ctx = colorBlockInputRowZeroContext := by
              simpa using hZero
            rw [hCtxZero]
            exact colorBlockInputOfZeroRowContext_inputSize_le (N := N) hRight
          · exact colorBlockInputOfRowContext_inputSize_le hCtx hRight
      have hSingleton :
          colorBlockInputListEncodedType.inputSize [colorBlockInputOfRowContext ctx right] ≤
            4 * N + 12 := by
        simp [colorBlockInputListEncodedType, EncodedType.inputSize_list_cons,
          EncodedType.inputSize_list_nil] at hElem ⊢
        omega
      have hAppend :
          colorBlockInputListEncodedType.inputSize
              ((show List colorBlockInputEncodedType.Carrier from out) ++
                [colorBlockInputOfRowContext ctx right]) =
            colorBlockInputListEncodedType.inputSize out +
              colorBlockInputListEncodedType.inputSize [colorBlockInputOfRowContext ctx right] := by
        simpa [colorBlockInputListEncodedType] using
          list_inputSize_append colorBlockInputEncodedType out [colorBlockInputOfRowContext ctx right]
      constructor
      ·
        rcases hInv with hInit | hRest
        · injection hInit with hCtxEq _hOut
          exact Or.inr (Or.inl hCtxEq)
        · exact Or.inr hRest
      · change
          colorBlockInputRowAccEncodedType.inputSize
              (ctx, (show List colorBlockInputEncodedType.Carrier from out) ++
                [colorBlockInputOfRowContext ctx right]) ≤
            colorBlockInputRowAccEncodedType.inputSize (ctx, out) +
              colorBlockInputRowFoldGrow.eval N
        simp [colorBlockInputRowAccEncodedType, EncodedType.inputSize_prod] at hAppend ⊢
        rw [hAppend]
        omega

theorem colorBlockInputRowFold_tm_polytime :
    TMPolyTimeMap
      colorBlockInputRowInstructionListEncodedType
      colorBlockInputRowAccEncodedType
      (fun xs : List colorBlockInputRowInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => colorBlockInputRowStep (acc, instr))
          colorBlockInputRowInitAcc) := by
  rcases colorBlockInputRowStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      colorBlockInputRowInstructionEncodedType colorBlockInputRowAccEncodedType
      colorBlockInputRowStep colorBlockInputRowInitAcc hStep
      colorBlockInputRowFoldBase colorBlockInputRowFoldGrow colorBlockInputRowFoldInv ?_ ?_
  · intro xs
    exact colorBlockInputRowInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact colorBlockInputRowStep_growth source acc instr hInv hInstr

theorem colorBlockInputRowFromInstructions_tm_polytime :
    TMPolyTimeMap
      colorBlockInputRowInstructionListEncodedType
      colorBlockInputListEncodedType
      colorBlockInputRowFromInstructions := by
  have hFold := colorBlockInputRowFold_tm_polytime
  have hOut := TMPolyTimeMap.snd colorBlockInputRowContextEncodedType colorBlockInputListEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, colorBlockInputRowFromInstructions,
    colorBlockInputRowAccEncodedType] using hComp

theorem colorBlockInputRowExecutable_tm_polytime :
    TMPolyTimeMap
      colorBlockInputRowContextEncodedType
      colorBlockInputListEncodedType
      colorBlockInputRowExecutable := by
  have hComp :=
    TMPolyTimeMap.comp colorBlockInputRowFromInstructions_tm_polytime
      colorBlockInputRowInstructions_tm_polytime
  simpa [Function.comp, colorBlockInputRowExecutable] using hComp

theorem colorBlockInputRowExecutable_inputSize_le
    {N : Nat} {ctx : ColorBlockInputRowContext}
    (hCtx : colorBlockInputRowContextEncodedType.inputSize ctx ≤ N) :
    colorBlockInputListEncodedType.inputSize (colorBlockInputRowExecutable ctx) ≤
      (N + 1) * (4 * N + 12) := by
  rw [colorBlockInputRowExecutable_eq_map]
  let row :=
    (List.range ctx.2.2).map (colorBlockInputOfRowContext ctx)
  have hRightCount : ctx.2.2 ≤ N := by
    rcases ctx with ⟨I, ⟨left, rightCount⟩⟩
    simp [colorBlockInputRowContextEncodedType, colorBlockInputEncodedType,
      colorChoiceCodeInputEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat] at hCtx
    change rightCount ≤ N
    omega
  have hLen : row.length ≤ N + 1 := by
    dsimp [row]
    simp
    omega
  have hEach :
      ∀ x ∈ row, colorBlockInputEncodedType.inputSize x ≤ 4 * N + 10 := by
    intro x hx
    dsimp [row] at hx
    rcases List.mem_map.mp hx with ⟨right, hRightMem, rfl⟩
    have hRightLt : right < ctx.2.2 := by
      simpa using List.mem_range.mp hRightMem
    have hRightSize : EncodedType.nat.inputSize right ≤ N := by
      simp [EncodedType.inputSize_nat]
      omega
    exact colorBlockInputOfRowContext_inputSize_le hCtx hRightSize
  have hList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      colorBlockInputEncodedType row (4 * N + 10) hEach
  calc
    colorBlockInputListEncodedType.inputSize row
        ≤ row.length * (4 * N + 10 + 1) := by
          simpa [colorBlockInputListEncodedType] using hList
    _ ≤ (N + 1) * (4 * N + 12) :=
          Nat.mul_le_mul hLen (by omega)

end ExactCover
end Karp21
end ComplexityReduction
