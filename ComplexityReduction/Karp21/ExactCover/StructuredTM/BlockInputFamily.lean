import ComplexityReduction.Karp21.ExactCover.StructuredTM.BlockInputs

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Executable rectangular family generator for block-input tuples.

Given `(I, (leftCount, rightCount))`, this emits the row-major list
`(List.range leftCount).flatMap fun left =>
  (List.range rightCount).map fun right => (I, (left, right))`.
-/

def colorBlockInputFamilyInstructionEncodedType : EncodedType :=
  EncodedType.sum colorBlockInputRowContextEncodedType EncodedType.nat

def colorBlockInputFamilyInstructionListEncodedType : EncodedType :=
  EncodedType.list colorBlockInputFamilyInstructionEncodedType

def colorBlockInputFamilyAccEncodedType : EncodedType :=
  EncodedType.prod colorBlockInputRowContextEncodedType colorBlockInputListEncodedType

def colorBlockInputFamilyInitAcc : colorBlockInputFamilyAccEncodedType.Carrier :=
  (colorBlockInputRowZeroContext, [])

def colorBlockInputFamilyInitInstruction
    (ctx : ColorBlockInputRowContext) :
    colorBlockInputFamilyInstructionEncodedType.Carrier :=
  Sum.inl ctx

def colorBlockInputFamilyIndexInstruction
    (left : Nat) : colorBlockInputFamilyInstructionEncodedType.Carrier :=
  Sum.inr left

def colorBlockInputFamilyInstructions
    (ctx : ColorBlockInputRowContext) :
    List colorBlockInputFamilyInstructionEncodedType.Carrier :=
  colorBlockInputFamilyInitInstruction ctx ::
    (List.range ctx.2.1).map colorBlockInputFamilyIndexInstruction

def colorBlockInputFamilyRowContext
    (ctx : ColorBlockInputRowContext) (left : Nat) : ColorBlockInputRowContext :=
  (ctx.1, (left, ctx.2.2))

def colorBlockInputFamilyStep
    (p : colorBlockInputFamilyAccEncodedType.Carrier ×
      colorBlockInputFamilyInstructionEncodedType.Carrier) :
    colorBlockInputFamilyAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl ctx => (ctx, [])
  | Sum.inr left =>
      (p.1.1, (show List colorBlockInputEncodedType.Carrier from p.1.2) ++
        colorBlockInputRowExecutable (colorBlockInputFamilyRowContext p.1.1 left))

def colorBlockInputFamilyFromInstructions
    (xs : List colorBlockInputFamilyInstructionEncodedType.Carrier) :
    List colorBlockInputEncodedType.Carrier :=
  (xs.foldl (fun acc instr => colorBlockInputFamilyStep (acc, instr))
    colorBlockInputFamilyInitAcc).2

def colorBlockInputsExecutable
    (ctx : ColorBlockInputRowContext) :
    List colorBlockInputEncodedType.Carrier :=
  colorBlockInputFamilyFromInstructions (colorBlockInputFamilyInstructions ctx)

/-! ### Semantics -/

theorem colorBlockInputFamilyIndexFold_eq_append_flatMap
    (ctx : ColorBlockInputRowContext) (xs : List Nat)
    (out : List colorBlockInputEncodedType.Carrier) :
    ((xs.map colorBlockInputFamilyIndexInstruction).foldl
        (fun acc instr => colorBlockInputFamilyStep (acc, instr)) (ctx, out)).2 =
      out ++ xs.flatMap (fun left =>
        colorBlockInputRowExecutable (colorBlockInputFamilyRowContext ctx left)) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons left rest ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [colorBlockInputFamilyIndexInstruction, colorBlockInputFamilyStep]
      have hTail := ih (out ++
        colorBlockInputRowExecutable (colorBlockInputFamilyRowContext ctx left))
      simpa [List.append_assoc] using hTail

theorem colorBlockInputsExecutable_eq_flatMap_rows
    (ctx : ColorBlockInputRowContext) :
    colorBlockInputsExecutable ctx =
      (List.range ctx.2.1).flatMap (fun left =>
        colorBlockInputRowExecutable (colorBlockInputFamilyRowContext ctx left)) := by
  change
    (((List.range ctx.2.1).map colorBlockInputFamilyIndexInstruction).foldl
        (fun acc instr => colorBlockInputFamilyStep (acc, instr)) (ctx, [])).2 =
      (List.range ctx.2.1).flatMap (fun left =>
        colorBlockInputRowExecutable (colorBlockInputFamilyRowContext ctx left))
  simpa using colorBlockInputFamilyIndexFold_eq_append_flatMap ctx (List.range ctx.2.1) []

theorem colorBlockInputsExecutable_eq_flatMap
    (ctx : ColorBlockInputRowContext) :
    colorBlockInputsExecutable ctx =
      (List.range ctx.2.1).flatMap (fun left =>
        (List.range ctx.2.2).map fun right => (ctx.1, (left, right))) := by
  rw [colorBlockInputsExecutable_eq_flatMap_rows]
  apply List.flatMap_congr
  intro left _hleft
  rw [colorBlockInputRowExecutable_eq_map]
  apply List.map_congr_left
  intro right _hright
  rfl

/-! ### TM witnesses -/

theorem colorBlockInputFamilyInitInstruction_tm_polytime :
    TMPolyTimeMap
      colorBlockInputRowContextEncodedType
      colorBlockInputFamilyInstructionEncodedType
      colorBlockInputFamilyInitInstruction := by
  simpa [colorBlockInputFamilyInstructionEncodedType,
    colorBlockInputFamilyInitInstruction] using
    TMPolyTimeMap.inl colorBlockInputRowContextEncodedType EncodedType.nat

theorem colorBlockInputFamilyIndexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      colorBlockInputFamilyInstructionEncodedType
      colorBlockInputFamilyIndexInstruction := by
  simpa [colorBlockInputFamilyInstructionEncodedType,
    colorBlockInputFamilyIndexInstruction] using
    TMPolyTimeMap.inr colorBlockInputRowContextEncodedType EncodedType.nat

theorem colorBlockInputFamilyInstructions_tm_polytime :
    TMPolyTimeMap
      colorBlockInputRowContextEncodedType
      colorBlockInputFamilyInstructionListEncodedType
      colorBlockInputFamilyInstructions := by
  let X := colorBlockInputRowContextEncodedType
  have hCtx : TMPolyTimeMap X X (fun ctx : X.Carrier => ctx) := TMPolyTimeMap.id X
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun ctx : X.Carrier => ctx.2) := by
    simpa [X, colorBlockInputRowContextEncodedType, colorBlockInputEncodedType,
      colorChoiceCodeInputEncodedType] using
      TMPolyTimeMap.snd chromaticNumberStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hLeftCount : TMPolyTimeMap X EncodedType.nat (fun ctx : X.Carrier => ctx.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hInit :
      TMPolyTimeMap X colorBlockInputFamilyInstructionEncodedType
        (fun ctx : X.Carrier => colorBlockInputFamilyInitInstruction ctx) := by
    have hComp := TMPolyTimeMap.comp colorBlockInputFamilyInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun ctx : X.Carrier => List.range ctx.2.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hLeftCount
    simpa [Function.comp, X] using hComp
  have hIndexInstructions :
      TMPolyTimeMap X colorBlockInputFamilyInstructionListEncodedType
        (fun ctx : X.Carrier =>
          (List.range ctx.2.1).map colorBlockInputFamilyIndexInstruction) := by
    have hMap := TMPolyTimeMap.list_map colorBlockInputFamilyIndexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, colorBlockInputFamilyInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod colorBlockInputFamilyInstructionEncodedType
          colorBlockInputFamilyInstructionListEncodedType)
        (fun ctx : X.Carrier =>
          (colorBlockInputFamilyInitInstruction ctx,
            (List.range ctx.2.1).map colorBlockInputFamilyIndexInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hIndexInstructions
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons colorBlockInputFamilyInstructionEncodedType)
      hConsInput
  simpa [Function.comp, colorBlockInputFamilyInstructions,
    colorBlockInputFamilyInstructionListEncodedType, X] using hCons

theorem colorBlockInputFamilyStepLeft_tm_polytime :
    TMPolyTimeMap
      colorBlockInputRowContextEncodedType
      colorBlockInputFamilyAccEncodedType
      (fun ctx : ColorBlockInputRowContext =>
        (ctx, ([] : List colorBlockInputEncodedType.Carrier))) := by
  have hCtx := TMPolyTimeMap.id colorBlockInputRowContextEncodedType
  have hEmpty :
      TMPolyTimeMap colorBlockInputRowContextEncodedType colorBlockInputListEncodedType
        (fun _ : ColorBlockInputRowContext =>
          ([] : List colorBlockInputEncodedType.Carrier)) :=
    TMPolyTimeMap.const colorBlockInputRowContextEncodedType colorBlockInputListEncodedType []
  simpa [colorBlockInputFamilyAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hEmpty

theorem colorBlockInputFamilyStepRight_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod colorBlockInputFamilyAccEncodedType EncodedType.nat)
      colorBlockInputFamilyAccEncodedType
      (fun p : colorBlockInputFamilyAccEncodedType.Carrier × Nat =>
        (p.1.1, (show List colorBlockInputEncodedType.Carrier from p.1.2) ++
          colorBlockInputRowExecutable (colorBlockInputFamilyRowContext p.1.1 p.2))) := by
  let X := EncodedType.prod colorBlockInputFamilyAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X colorBlockInputFamilyAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst colorBlockInputFamilyAccEncodedType EncodedType.nat
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd colorBlockInputFamilyAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X colorBlockInputRowContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst colorBlockInputRowContextEncodedType
      colorBlockInputListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, colorBlockInputFamilyAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X colorBlockInputListEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd colorBlockInputRowContextEncodedType
      colorBlockInputListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, colorBlockInputFamilyAccEncodedType, X] using hComp
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
  have hRightCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2, p.1.1.2.2)) :=
    TMPolyTimeMap.prod_mk hLeft hRightCount
  have hRowCtx :
      TMPolyTimeMap X colorBlockInputRowContextEncodedType
        (fun p : X.Carrier => colorBlockInputFamilyRowContext p.1.1 p.2) := by
    simpa [colorBlockInputFamilyRowContext, colorBlockInputRowContextEncodedType,
      colorBlockInputEncodedType, colorChoiceCodeInputEncodedType] using
      TMPolyTimeMap.prod_mk hSource hPair
  have hRow :
      TMPolyTimeMap X colorBlockInputListEncodedType
        (fun p : X.Carrier =>
          colorBlockInputRowExecutable (colorBlockInputFamilyRowContext p.1.1 p.2)) := by
    have hComp := TMPolyTimeMap.comp colorBlockInputRowExecutable_tm_polytime hRowCtx
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod colorBlockInputListEncodedType colorBlockInputListEncodedType)
        (fun p : X.Carrier =>
          ((show List colorBlockInputEncodedType.Carrier from p.1.2),
            colorBlockInputRowExecutable (colorBlockInputFamilyRowContext p.1.1 p.2))) :=
    TMPolyTimeMap.prod_mk hOut hRow
  have hAppend :
      TMPolyTimeMap X colorBlockInputListEncodedType
        (fun p : X.Carrier =>
          (show List colorBlockInputEncodedType.Carrier from p.1.2) ++
            colorBlockInputRowExecutable (colorBlockInputFamilyRowContext p.1.1 p.2)) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append colorBlockInputEncodedType) hAppendInput
    simpa [Function.comp, colorBlockInputListEncodedType, X] using hComp
  simpa [colorBlockInputFamilyAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hAppend

theorem colorBlockInputFamilyStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod colorBlockInputFamilyAccEncodedType
        colorBlockInputFamilyInstructionEncodedType)
      colorBlockInputFamilyAccEncodedType
      colorBlockInputFamilyStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      colorBlockInputFamilyAccEncodedType colorBlockInputRowContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim colorBlockInputFamilyStepLeft_tm_polytime
      colorBlockInputFamilyStepRight_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def colorBlockInputFamilyFoldInv (N : Nat)
    (acc : colorBlockInputFamilyAccEncodedType.Carrier) : Prop :=
  acc = colorBlockInputFamilyInitAcc ∨
    acc.1 = colorBlockInputRowZeroContext ∨
    colorBlockInputRowContextEncodedType.inputSize acc.1 ≤ N

noncomputable def colorBlockInputFamilyFoldBase : Polynomial Nat := Polynomial.C 100

noncomputable def colorBlockInputFamilyFoldGrow : Polynomial Nat :=
  Polynomial.C 1000 * (Polynomial.X * Polynomial.X) + Polynomial.C 10000

@[simp] theorem colorBlockInputFamilyFoldGrow_eval (N : Nat) :
    colorBlockInputFamilyFoldGrow.eval N = 1000 * (N * N) + 10000 := by
  simp [colorBlockInputFamilyFoldGrow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

theorem colorBlockInputFamilyInitAcc_bound
    (xs : List colorBlockInputFamilyInstructionEncodedType.Carrier) :
    colorBlockInputFamilyFoldInv
        (colorBlockInputFamilyInstructionListEncodedType.inputSize xs)
        colorBlockInputFamilyInitAcc ∧
      colorBlockInputFamilyAccEncodedType.inputSize colorBlockInputFamilyInitAcc ≤
        colorBlockInputFamilyFoldBase.eval
          (colorBlockInputFamilyInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [colorBlockInputFamilyFoldBase]
    native_decide

theorem colorBlockInputFamilyRowContext_inputSize_le
    {N : Nat} {ctx : ColorBlockInputRowContext} {left : Nat}
    (hCtx : colorBlockInputRowContextEncodedType.inputSize ctx ≤ N)
    (hLeft : EncodedType.nat.inputSize left ≤ N) :
    colorBlockInputRowContextEncodedType.inputSize
        (colorBlockInputFamilyRowContext ctx left) ≤
      2 * N + 20 := by
  rcases ctx with ⟨I, ⟨leftCount, rightCount⟩⟩
  simp [colorBlockInputFamilyRowContext, colorBlockInputRowContextEncodedType,
    colorBlockInputEncodedType, colorChoiceCodeInputEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat] at hCtx hLeft ⊢
  omega

theorem colorBlockInputFamilyZeroRowContext_inputSize_le
    {N left : Nat} (hLeft : EncodedType.nat.inputSize left ≤ N) :
    colorBlockInputRowContextEncodedType.inputSize
        (colorBlockInputFamilyRowContext colorBlockInputRowZeroContext left) ≤
      2 * N + 20 := by
  have hZeroSource :
      chromaticNumberStructuredEncodedType.inputSize colorDefaultChromaticInput ≤ 10 := by
    native_decide
  simp [colorBlockInputFamilyRowContext, colorBlockInputRowZeroContext,
    colorBlockInputRowContextEncodedType, colorBlockInputEncodedType,
    colorChoiceCodeInputEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat] at hLeft ⊢
  omega

theorem colorBlockInputFamilyStep_growth
    (source : List colorBlockInputFamilyInstructionEncodedType.Carrier)
    (acc : colorBlockInputFamilyAccEncodedType.Carrier)
    (instr : colorBlockInputFamilyInstructionEncodedType.Carrier)
    (hInv :
      colorBlockInputFamilyFoldInv
        (colorBlockInputFamilyInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      colorBlockInputFamilyInstructionEncodedType.inputSize instr ≤
        colorBlockInputFamilyInstructionListEncodedType.inputSize source) :
    colorBlockInputFamilyFoldInv
        (colorBlockInputFamilyInstructionListEncodedType.inputSize source)
        (colorBlockInputFamilyStep (acc, instr)) ∧
      colorBlockInputFamilyAccEncodedType.inputSize (colorBlockInputFamilyStep (acc, instr)) ≤
        colorBlockInputFamilyAccEncodedType.inputSize acc +
          colorBlockInputFamilyFoldGrow.eval
            (colorBlockInputFamilyInstructionListEncodedType.inputSize source) := by
  let N := colorBlockInputFamilyInstructionListEncodedType.inputSize source
  rcases acc with ⟨ctx, out⟩
  cases instr with
  | inl newCtx =>
      have hNewCtx : colorBlockInputRowContextEncodedType.inputSize newCtx ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, colorBlockInputFamilyInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum] using hInstr)
      constructor
      · exact Or.inr (Or.inr hNewCtx)
      · have hNewAcc :
            colorBlockInputFamilyAccEncodedType.inputSize
                (newCtx, ([] : List colorBlockInputEncodedType.Carrier)) ≤ N + 1 := by
          simp [colorBlockInputFamilyAccEncodedType, EncodedType.inputSize_prod,
            colorBlockInputListEncodedType, EncodedType.inputSize_list_nil]
          omega
        have hPoly :
            N + 1 ≤ colorBlockInputFamilyAccEncodedType.inputSize (ctx, out) +
              colorBlockInputFamilyFoldGrow.eval N := by
          rw [colorBlockInputFamilyFoldGrow_eval]
          have hN : 0 ≤ N := Nat.zero_le N
          have hAcc : 0 ≤ colorBlockInputFamilyAccEncodedType.inputSize (ctx, out) :=
            Nat.zero_le _
          nlinarith
        simpa [colorBlockInputFamilyStep, N] using hNewAcc.trans hPoly
  | inr left =>
      have hLeft : EncodedType.nat.inputSize left ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, colorBlockInputFamilyInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum] using hInstr)
      have hRowCtx :
          colorBlockInputRowContextEncodedType.inputSize
              (colorBlockInputFamilyRowContext ctx left) ≤ 2 * N + 20 := by
        rcases hInv with hInit | hRest
        · injection hInit with hCtxEq _hOut
          rw [hCtxEq]
          exact colorBlockInputFamilyZeroRowContext_inputSize_le (N := N) hLeft
        · rcases hRest with hZero | hCtx
          · have hCtxZero : ctx = colorBlockInputRowZeroContext := by
              simpa using hZero
            rw [hCtxZero]
            exact colorBlockInputFamilyZeroRowContext_inputSize_le (N := N) hLeft
          · exact colorBlockInputFamilyRowContext_inputSize_le hCtx hLeft
      have hRowBase :=
        colorBlockInputRowExecutable_inputSize_le
          (N := 2 * N + 20) (ctx := colorBlockInputFamilyRowContext ctx left) hRowCtx
      have hRow :
          colorBlockInputListEncodedType.inputSize
              (colorBlockInputRowExecutable (colorBlockInputFamilyRowContext ctx left)) ≤
            1000 * (N * N) + 9000 := by
        have hN : 0 ≤ N := Nat.zero_le N
        nlinarith [hRowBase, hN]
      have hAppend :
          colorBlockInputListEncodedType.inputSize
              ((show List colorBlockInputEncodedType.Carrier from out) ++
                colorBlockInputRowExecutable (colorBlockInputFamilyRowContext ctx left)) =
            colorBlockInputListEncodedType.inputSize out +
              colorBlockInputListEncodedType.inputSize
                (colorBlockInputRowExecutable (colorBlockInputFamilyRowContext ctx left)) := by
        simpa [colorBlockInputListEncodedType] using
          list_inputSize_append colorBlockInputEncodedType out
            (colorBlockInputRowExecutable (colorBlockInputFamilyRowContext ctx left))
      constructor
      ·
        rcases hInv with hInit | hRest
        · injection hInit with hCtxEq _hOut
          exact Or.inr (Or.inl hCtxEq)
        · exact Or.inr hRest
      · change
          colorBlockInputFamilyAccEncodedType.inputSize
              (ctx, (show List colorBlockInputEncodedType.Carrier from out) ++
                colorBlockInputRowExecutable (colorBlockInputFamilyRowContext ctx left)) ≤
            colorBlockInputFamilyAccEncodedType.inputSize (ctx, out) +
              colorBlockInputFamilyFoldGrow.eval N
        simp [colorBlockInputFamilyAccEncodedType, EncodedType.inputSize_prod] at hAppend ⊢
        rw [hAppend]
        omega

theorem colorBlockInputFamilyFold_tm_polytime :
    TMPolyTimeMap
      colorBlockInputFamilyInstructionListEncodedType
      colorBlockInputFamilyAccEncodedType
      (fun xs : List colorBlockInputFamilyInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => colorBlockInputFamilyStep (acc, instr))
          colorBlockInputFamilyInitAcc) := by
  rcases colorBlockInputFamilyStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      colorBlockInputFamilyInstructionEncodedType colorBlockInputFamilyAccEncodedType
      colorBlockInputFamilyStep colorBlockInputFamilyInitAcc hStep
      colorBlockInputFamilyFoldBase colorBlockInputFamilyFoldGrow colorBlockInputFamilyFoldInv ?_ ?_
  · intro xs
    exact colorBlockInputFamilyInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact colorBlockInputFamilyStep_growth source acc instr hInv hInstr

theorem colorBlockInputFamilyFromInstructions_tm_polytime :
    TMPolyTimeMap
      colorBlockInputFamilyInstructionListEncodedType
      colorBlockInputListEncodedType
      colorBlockInputFamilyFromInstructions := by
  have hFold := colorBlockInputFamilyFold_tm_polytime
  have hOut := TMPolyTimeMap.snd colorBlockInputRowContextEncodedType colorBlockInputListEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, colorBlockInputFamilyFromInstructions,
    colorBlockInputFamilyAccEncodedType] using hComp

theorem colorBlockInputsExecutable_tm_polytime :
    TMPolyTimeMap
      colorBlockInputRowContextEncodedType
      colorBlockInputListEncodedType
      colorBlockInputsExecutable := by
  have hComp :=
    TMPolyTimeMap.comp colorBlockInputFamilyFromInstructions_tm_polytime
      colorBlockInputFamilyInstructions_tm_polytime
  simpa [Function.comp, colorBlockInputsExecutable] using hComp

end ExactCover
end Karp21
end ComplexityReduction
