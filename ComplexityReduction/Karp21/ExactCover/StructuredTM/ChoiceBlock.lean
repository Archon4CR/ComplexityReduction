import ComplexityReduction.Karp21.ExactCover.StructuredTM
import ComplexityReduction.Karp21.Partition.StructuredTM.ProductSumChoice
import ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Direct TM-backed single-block construction for the compact
Chromatic-Number-to-Exact-Cover route.

This module turns one vertex/color choice block into an executable finite
alphabet fold over the already checked incident-edge index list.  The edge/color
marker uses the closed form proved in `EdgeCode`.
-/

def colorChoiceCodeContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat))

abbrev ColorChoiceCodeContext := Nat × (Nat × (Nat × Nat))

def colorChoiceCodeInstructionEncodedType : EncodedType :=
  EncodedType.sum colorChoiceCodeContextEncodedType EncodedType.nat

def colorChoiceCodeInstructionListEncodedType : EncodedType :=
  EncodedType.list colorChoiceCodeInstructionEncodedType

def colorChoiceCodeAccEncodedType : EncodedType :=
  EncodedType.prod colorChoiceCodeContextEncodedType setStructuredEncodedType

def colorChoiceCodeInputEncodedType : EncodedType :=
  EncodedType.prod chromaticNumberStructuredEncodedType
    (EncodedType.prod EncodedType.nat EncodedType.nat)

def colorChoiceCodeContextOfInput
    (p : ChromaticNumberInput × (Nat × Nat)) : ColorChoiceCodeContext :=
  (p.1.graph.vertices, (p.1.colors, (p.2.1, p.2.2)))

def colorChoiceCodeInitInstruction
    (ctx : ColorChoiceCodeContext) : colorChoiceCodeInstructionEncodedType.Carrier :=
  Sum.inl ctx

def colorChoiceCodeIndexInstruction
    (i : Nat) : colorChoiceCodeInstructionEncodedType.Carrier :=
  Sum.inr i

def colorChoiceCodeInstructions
    (p : ChromaticNumberInput × (Nat × Nat)) :
    List colorChoiceCodeInstructionEncodedType.Carrier :=
  colorChoiceCodeInitInstruction (colorChoiceCodeContextOfInput p) ::
    (colorIncidentEdgeIndices p.1 p.2.1).map colorChoiceCodeIndexInstruction

def colorChoiceCodeInitAcc : colorChoiceCodeAccEncodedType.Carrier :=
  (((0 : Nat), ((0 : Nat), ((0 : Nat), (0 : Nat)))), ([] : List Nat))

def colorChoiceCodeFromContext (ctx : ColorChoiceCodeContext) (i : Nat) : Nat :=
  ctx.1 + i * ctx.2.1 + ctx.2.2.2

def colorChoiceCodeStep
    (p : colorChoiceCodeAccEncodedType.Carrier ×
      colorChoiceCodeInstructionEncodedType.Carrier) :
    colorChoiceCodeAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl ctx => (ctx, [ctx.2.2.1])
  | Sum.inr i => (p.1.1, (show List Nat from p.1.2) ++ [colorChoiceCodeFromContext p.1.1 i])

def colorChoiceCodeFromInstructions
    (xs : List colorChoiceCodeInstructionEncodedType.Carrier) : List Nat :=
  (xs.foldl (fun acc instr => colorChoiceCodeStep (acc, instr))
    colorChoiceCodeInitAcc).2

def colorChoiceBlockExecutable (p : ChromaticNumberInput × (Nat × Nat)) : List Nat :=
  colorChoiceCodeFromInstructions (colorChoiceCodeInstructions p)

def colorChoiceBlockFast (I : ChromaticNumberInput) (v c : Nat) : List Nat :=
  colorChoiceBlockExecutable (I, (v, c))

/-! ### Semantics -/

theorem colorChoiceCodeIndexFold_eq_append_map
    (ctx : ColorChoiceCodeContext) (xs out : List Nat) :
    ((xs.map colorChoiceCodeIndexInstruction).foldl
        (fun acc instr => colorChoiceCodeStep (acc, instr)) (ctx, out)).2 =
      out ++ xs.map (colorChoiceCodeFromContext ctx) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons i is ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [colorChoiceCodeIndexInstruction, colorChoiceCodeStep]
      have hTail := ih (out ++ [colorChoiceCodeFromContext ctx i])
      simpa [List.append_assoc] using hTail

theorem colorChoiceBlockExecutable_eq_fast_codes
    (I : ChromaticNumberInput) (v c : Nat) :
    colorChoiceBlockExecutable (I, (v, c)) =
      colorVertexCode I v ::
        (colorIncidentEdgeIndices I v).map (fun i => colorEdgeCodeFast I i c) := by
  change
    (((colorIncidentEdgeIndices I v).map colorChoiceCodeIndexInstruction).foldl
        (fun acc instr => colorChoiceCodeStep (acc, instr))
        (colorChoiceCodeContextOfInput (I, (v, c)), [v])).2 =
      colorVertexCode I v ::
        (colorIncidentEdgeIndices I v).map (fun i => colorEdgeCodeFast I i c)
  rw [colorChoiceCodeIndexFold_eq_append_map]
  change
    [v] ++ List.map (fun i => I.graph.vertices + i * I.colors + c)
        (colorIncidentEdgeIndices I v) =
      v :: List.map (fun i => I.graph.vertices + i * I.colors + c)
        (colorIncidentEdgeIndices I v)
  rw [List.singleton_append]

theorem colorChoiceBlockFast_eq_colorChoiceBlock
    {I : ChromaticNumberInput} {v c : Nat} (hc : c < I.colors) :
    colorChoiceBlockFast I v c = colorChoiceBlock I v c := by
  rw [colorChoiceBlockFast, colorChoiceBlockExecutable_eq_fast_codes]
  simp [colorChoiceBlock, colorVertexCode]
  intro i hi
  have hiEdges : i < I.graph.edges.length :=
    (mem_colorIncidentEdgeIndices_iff I v i).1 hi |>.1
  exact colorEdgeCodeFast_eq_colorEdgeCode hiEdges hc

/-! ### TM witnesses -/

theorem colorChoiceCodeContextOfInput_tm_polytime :
    TMPolyTimeMap
      colorChoiceCodeInputEncodedType
      colorChoiceCodeContextEncodedType
      colorChoiceCodeContextOfInput := by
  let X := colorChoiceCodeInputEncodedType
  have hSource :
      TMPolyTimeMap X chromaticNumberStructuredEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, colorChoiceCodeInputEncodedType] using
      TMPolyTimeMap.fst chromaticNumberStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => p.2) := by
    simpa [X, colorChoiceCodeInputEncodedType] using
      TMPolyTimeMap.snd chromaticNumberStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hVertex :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hColor :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType (fun p : X.Carrier => p.1.graph) := by
    have hComp := TMPolyTimeMap.comp chromaticNumberGraphTMBackedMap.tm_polytime hSource
    simpa [Function.comp, X] using hComp
  have hVertices :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hColors :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.colors) := by
    have hComp := TMPolyTimeMap.comp chromaticNumberColorsTMBackedMap.tm_polytime hSource
    simpa [Function.comp, X] using hComp
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : X.Carrier => (p.1.colors, (p.2.1, p.2.2))) := by
    simpa using TMPolyTimeMap.prod_mk hColors (TMPolyTimeMap.prod_mk hVertex hColor)
  have hOut := TMPolyTimeMap.prod_mk hVertices hTail
  simpa [colorChoiceCodeContextOfInput, colorChoiceCodeContextEncodedType, X] using hOut

theorem colorChoiceCodeInitInstruction_tm_polytime :
    TMPolyTimeMap
      colorChoiceCodeContextEncodedType
      colorChoiceCodeInstructionEncodedType
      colorChoiceCodeInitInstruction := by
  simpa [colorChoiceCodeInstructionEncodedType, colorChoiceCodeInitInstruction] using
    TMPolyTimeMap.inl colorChoiceCodeContextEncodedType EncodedType.nat

theorem colorChoiceCodeIndexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      colorChoiceCodeInstructionEncodedType
      colorChoiceCodeIndexInstruction := by
  simpa [colorChoiceCodeInstructionEncodedType, colorChoiceCodeIndexInstruction] using
    TMPolyTimeMap.inr colorChoiceCodeContextEncodedType EncodedType.nat

theorem colorChoiceCodeInstructions_tm_polytime :
    TMPolyTimeMap
      colorChoiceCodeInputEncodedType
      colorChoiceCodeInstructionListEncodedType
      colorChoiceCodeInstructions := by
  let X := colorChoiceCodeInputEncodedType
  have hSource :
      TMPolyTimeMap X chromaticNumberStructuredEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, colorChoiceCodeInputEncodedType] using
      TMPolyTimeMap.fst chromaticNumberStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => p.2) := by
    simpa [X, colorChoiceCodeInputEncodedType] using
      TMPolyTimeMap.snd chromaticNumberStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hVertex :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hIncidentInput :
      TMPolyTimeMap X colorIncidentInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.1)) := by
    simpa [colorIncidentInputEncodedType] using TMPolyTimeMap.prod_mk hSource hVertex
  have hIncident :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => colorIncidentEdgeIndices p.1 p.2.1) := by
    have hComp := TMPolyTimeMap.comp colorIncidentEdgeIndices_tm_polytime hIncidentInput
    simpa [Function.comp, X] using hComp
  have hCtx :
      TMPolyTimeMap X colorChoiceCodeContextEncodedType colorChoiceCodeContextOfInput :=
    colorChoiceCodeContextOfInput_tm_polytime
  have hInit :
      TMPolyTimeMap X colorChoiceCodeInstructionEncodedType
        (fun p : X.Carrier => colorChoiceCodeInitInstruction (colorChoiceCodeContextOfInput p)) := by
    have hComp := TMPolyTimeMap.comp colorChoiceCodeInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X colorChoiceCodeInstructionListEncodedType
        (fun p : X.Carrier =>
          [colorChoiceCodeInitInstruction (colorChoiceCodeContextOfInput p)]) := by
    have hComp :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton colorChoiceCodeInstructionEncodedType) hInit
    simpa [Function.comp, colorChoiceCodeInstructionListEncodedType, X] using hComp
  have hIndexInstructions :
      TMPolyTimeMap X colorChoiceCodeInstructionListEncodedType
        (fun p : X.Carrier =>
          (colorIncidentEdgeIndices p.1 p.2.1).map colorChoiceCodeIndexInstruction) := by
    have hMap := TMPolyTimeMap.list_map colorChoiceCodeIndexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hIncident
    simpa [Function.comp, colorChoiceCodeInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod colorChoiceCodeInstructionListEncodedType
          colorChoiceCodeInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([colorChoiceCodeInitInstruction (colorChoiceCodeContextOfInput p)],
            (colorIncidentEdgeIndices p.1 p.2.1).map colorChoiceCodeIndexInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hIndexInstructions
  have hAppend :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_append colorChoiceCodeInstructionEncodedType)
      hAppendInput
  simpa [Function.comp, colorChoiceCodeInstructions,
    colorChoiceCodeInstructionListEncodedType, X] using hAppend

theorem colorChoiceCodeStepLeft_tm_polytime :
    TMPolyTimeMap
      colorChoiceCodeContextEncodedType
      colorChoiceCodeAccEncodedType
      (fun ctx : ColorChoiceCodeContext => (ctx, [ctx.2.2.1])) := by
  let X := colorChoiceCodeContextEncodedType
  have hCtx : TMPolyTimeMap X X (fun ctx : X.Carrier => ctx) := TMPolyTimeMap.id X
  have hVertex : TMPolyTimeMap X EncodedType.nat (fun ctx : X.Carrier => ctx.2.2.1) := by
    have hTail := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat))
    have hTailComp := TMPolyTimeMap.comp hTail (TMPolyTimeMap.id X)
    have hInnerFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hInnerPair :
        TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
          (fun ctx : X.Carrier => ctx.2.2) := by
      have hSnd := TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat)
      have hComp := TMPolyTimeMap.comp hSnd hTailComp
      simpa [Function.comp, X, colorChoiceCodeContextEncodedType] using hComp
    have hComp := TMPolyTimeMap.comp hInnerFst hInnerPair
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X setStructuredEncodedType
        (fun ctx : X.Carrier => [ctx.2.2.1]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hVertex
    simpa [Function.comp, setStructuredEncodedType] using hComp
  simpa [colorChoiceCodeAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hSingleton

theorem colorChoiceCodeStepRight_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod colorChoiceCodeAccEncodedType EncodedType.nat)
      colorChoiceCodeAccEncodedType
      (fun p : colorChoiceCodeAccEncodedType.Carrier × Nat =>
        (p.1.1, (show List Nat from p.1.2) ++ [colorChoiceCodeFromContext p.1.1 p.2])) := by
  let X := EncodedType.prod colorChoiceCodeAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X colorChoiceCodeAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst colorChoiceCodeAccEncodedType EncodedType.nat
  have hIndex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd colorChoiceCodeAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X colorChoiceCodeContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst colorChoiceCodeContextEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, colorChoiceCodeAccEncodedType, X] using hComp
  have hOut : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd colorChoiceCodeContextEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, colorChoiceCodeAccEncodedType, X] using hComp
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat))
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, colorChoiceCodeContextEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat))
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, colorChoiceCodeContextEncodedType, X] using hComp
  have hColors : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hColorPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => p.1.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hColor : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hColorPayload
    simpa [Function.comp, X] using hComp
  have hMulInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => ((show Nat from p.2), (show Nat from p.1.1.2.1))) :=
    TMPolyTimeMap.prod_mk hIndex hColors
  have hMul :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => (show Nat from p.2) * (show Nat from p.1.1.2.1)) := by
    have hComp := TMPolyTimeMap.comp GenericNatTM.natMul_tm_polytime hMulInput
    simpa [Function.comp, X] using hComp
  have hFirstAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : X.Carrier =>
          ((show Nat from p.1.1.1), (show Nat from p.2) * (show Nat from p.1.1.2.1))) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk hVertices hMul
  have hFirstAdd :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier =>
          (show Nat from p.1.1.1) + (show Nat from p.2) * (show Nat from p.1.1.2.1)) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hFirstAddInput
    simpa [Function.comp, natAddInputEncodedType, X] using hComp
  have hSecondAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : X.Carrier =>
          ((show Nat from p.1.1.1) + (show Nat from p.2) * (show Nat from p.1.1.2.1),
            (show Nat from p.1.1.2.2.2))) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk hFirstAdd hColor
  have hCode :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => colorChoiceCodeFromContext p.1.1 p.2) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hSecondAddInput
    simpa [Function.comp, natAddInputEncodedType, colorChoiceCodeFromContext, X] using hComp
  have hSingleton :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : X.Carrier => [colorChoiceCodeFromContext p.1.1 p.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hCode
    simpa [Function.comp, setStructuredEncodedType] using hComp
  have hAppendInput :
      TMPolyTimeMap X (EncodedType.prod setStructuredEncodedType setStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show List Nat from p.1.2), [colorChoiceCodeFromContext p.1.1 p.2])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : X.Carrier =>
          (show List Nat from p.1.2) ++ [colorChoiceCodeFromContext p.1.1 p.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat) hAppendInput
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  simpa [colorChoiceCodeAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hAppend

theorem colorChoiceCodeStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod colorChoiceCodeAccEncodedType colorChoiceCodeInstructionEncodedType)
      colorChoiceCodeAccEncodedType
      colorChoiceCodeStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      colorChoiceCodeAccEncodedType colorChoiceCodeContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim colorChoiceCodeStepLeft_tm_polytime
      colorChoiceCodeStepRight_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def colorChoiceCodeFoldInv (N : Nat)
    (acc : colorChoiceCodeAccEncodedType.Carrier) : Prop :=
  acc = colorChoiceCodeInitAcc ∨
    acc.1 = (((0 : Nat), ((0 : Nat), ((0 : Nat), (0 : Nat))))) ∨
    colorChoiceCodeContextEncodedType.inputSize acc.1 ≤ N

noncomputable def colorChoiceCodeFoldBase : Polynomial Nat := Polynomial.C 20

noncomputable def colorChoiceCodeFoldGrow : Polynomial Nat :=
  Polynomial.C 20 * (Polynomial.X * Polynomial.X) + Polynomial.C 100

@[simp] theorem colorChoiceCodeFoldGrow_eval (N : Nat) :
    colorChoiceCodeFoldGrow.eval N = 20 * (N * N) + 100 := by
  simp [colorChoiceCodeFoldGrow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

theorem colorChoiceCodeInitAcc_bound
    (xs : List colorChoiceCodeInstructionEncodedType.Carrier) :
    colorChoiceCodeFoldInv (colorChoiceCodeInstructionListEncodedType.inputSize xs)
        colorChoiceCodeInitAcc ∧
      colorChoiceCodeAccEncodedType.inputSize colorChoiceCodeInitAcc ≤
        colorChoiceCodeFoldBase.eval (colorChoiceCodeInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [colorChoiceCodeInitAcc, colorChoiceCodeAccEncodedType,
      colorChoiceCodeContextEncodedType, colorChoiceCodeFoldBase,
      setStructuredEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat]
    native_decide

theorem colorChoiceCodeFromContext_inputSize_le
    {N : Nat} {ctx : ColorChoiceCodeContext} {i : Nat}
    (hCtx : colorChoiceCodeContextEncodedType.inputSize ctx ≤ N)
    (hi : EncodedType.nat.inputSize i ≤ N) :
    EncodedType.nat.inputSize (colorChoiceCodeFromContext ctx i) ≤
      20 * (N * N) + 50 := by
  rcases ctx with ⟨vertices, ⟨colors, ⟨v, c⟩⟩⟩
  simp [colorChoiceCodeContextEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat] at hCtx hi ⊢
  have hN : 1 ≤ N := by omega
  have hVerticesN : vertices ≤ N := by omega
  have hColorsN : colors ≤ N := by omega
  have hColorN : c ≤ N := by omega
  have hiN : i ≤ N := by omega
  have hMul : i * colors ≤ N * N := Nat.mul_le_mul hiN hColorsN
  change vertices + i * colors + c ≤ 20 * (N * N) + 49
  calc
    vertices + i * colors + c ≤ N + N * N + N := by omega
    _ ≤ 20 * (N * N) + 49 := by
      nlinarith [sq_nonneg (N : Int), hN]

theorem colorChoiceCodeStep_growth
    (source : List colorChoiceCodeInstructionEncodedType.Carrier)
    (acc : colorChoiceCodeAccEncodedType.Carrier)
    (instr : colorChoiceCodeInstructionEncodedType.Carrier)
    (hInv :
      colorChoiceCodeFoldInv
        (colorChoiceCodeInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      colorChoiceCodeInstructionEncodedType.inputSize instr ≤
        colorChoiceCodeInstructionListEncodedType.inputSize source) :
    colorChoiceCodeFoldInv
        (colorChoiceCodeInstructionListEncodedType.inputSize source)
        (colorChoiceCodeStep (acc, instr)) ∧
      colorChoiceCodeAccEncodedType.inputSize (colorChoiceCodeStep (acc, instr)) ≤
        colorChoiceCodeAccEncodedType.inputSize acc +
          colorChoiceCodeFoldGrow.eval
            (colorChoiceCodeInstructionListEncodedType.inputSize source) := by
  let N := colorChoiceCodeInstructionListEncodedType.inputSize source
  rcases acc with ⟨ctx, out⟩
  cases instr with
  | inl newCtx =>
      have hNewCtx : colorChoiceCodeContextEncodedType.inputSize newCtx ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, colorChoiceCodeInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum] using hInstr)
      constructor
      · exact Or.inr (Or.inr hNewCtx)
      · have hVertexSize :
            setStructuredEncodedType.inputSize [newCtx.2.2.1] ≤ N + 3 := by
          have hV : EncodedType.nat.inputSize newCtx.2.2.1 ≤ N := by
            rcases newCtx with ⟨vertices, ⟨colors, ⟨v, c⟩⟩⟩
            simp [colorChoiceCodeContextEncodedType, EncodedType.inputSize_prod,
              EncodedType.inputSize_nat] at hNewCtx ⊢
            omega
          simp [setStructuredEncodedType, EncodedType.inputSize_list_cons,
            EncodedType.inputSize_list_nil, EncodedType.inputSize_nat] at hV ⊢
          omega
        have hNewAcc :
            colorChoiceCodeAccEncodedType.inputSize (newCtx, [newCtx.2.2.1]) ≤
              2 * N + 4 := by
          simp [colorChoiceCodeAccEncodedType, EncodedType.inputSize_prod]
          omega
        have hPoly :
            2 * N + 4 ≤ colorChoiceCodeAccEncodedType.inputSize (ctx, out) +
              colorChoiceCodeFoldGrow.eval N := by
          simp [colorChoiceCodeFoldGrow]
          have hBase : 2 * N + 4 ≤ 20 * (N * N) + 100 := by
            nlinarith [sq_nonneg (N : Int)]
          omega
        simpa [colorChoiceCodeStep, N] using hNewAcc.trans hPoly
  | inr i =>
      have hi : EncodedType.nat.inputSize i ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, colorChoiceCodeInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum] using hInstr)
      have hCode :
          EncodedType.nat.inputSize (colorChoiceCodeFromContext ctx i) ≤
            20 * (N * N) + 50 := by
        rcases hInv with hInit | hRest
        · injection hInit with hCtxEq _hOut
          rw [hCtxEq]
          simp [colorChoiceCodeFromContext, EncodedType.inputSize_nat]
        · rcases hRest with hZeroCtx | hCtx
          · have hCtxZero :
                ctx = (((0 : Nat), ((0 : Nat), ((0 : Nat), (0 : Nat))))) := by
              simpa using hZeroCtx
            rw [hCtxZero]
            simp [colorChoiceCodeFromContext, EncodedType.inputSize_nat]
          · exact
              colorChoiceCodeFromContext_inputSize_le (N := N) (ctx := ctx) (i := i)
                hCtx hi
      have hSingleton :
          setStructuredEncodedType.inputSize [colorChoiceCodeFromContext ctx i] ≤
            20 * (N * N) + 52 := by
        simp [setStructuredEncodedType, EncodedType.inputSize_list_cons,
          EncodedType.inputSize_list_nil] at hCode ⊢
        omega
      have hAppend :
          setStructuredEncodedType.inputSize
              ((show List Nat from out) ++ [colorChoiceCodeFromContext ctx i]) =
            setStructuredEncodedType.inputSize out +
              setStructuredEncodedType.inputSize [colorChoiceCodeFromContext ctx i] := by
        simpa [setStructuredEncodedType] using
          list_inputSize_append EncodedType.nat out [colorChoiceCodeFromContext ctx i]
      constructor
      ·
        rcases hInv with hInit | hRest
        · injection hInit with hCtxEq _hOut
          exact Or.inr (Or.inl hCtxEq)
        · exact Or.inr hRest
      · change
          colorChoiceCodeAccEncodedType.inputSize
              (ctx, (show List Nat from out) ++ [colorChoiceCodeFromContext ctx i]) ≤
            colorChoiceCodeAccEncodedType.inputSize (ctx, out) +
              colorChoiceCodeFoldGrow.eval N
        simp [colorChoiceCodeAccEncodedType, EncodedType.inputSize_prod] at hAppend ⊢
        rw [hAppend]
        omega

theorem colorChoiceCodeFold_tm_polytime :
    TMPolyTimeMap
      colorChoiceCodeInstructionListEncodedType
      colorChoiceCodeAccEncodedType
      (fun xs : List colorChoiceCodeInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => colorChoiceCodeStep (acc, instr))
          colorChoiceCodeInitAcc) := by
  rcases colorChoiceCodeStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      colorChoiceCodeInstructionEncodedType colorChoiceCodeAccEncodedType
      colorChoiceCodeStep colorChoiceCodeInitAcc hStep
      colorChoiceCodeFoldBase colorChoiceCodeFoldGrow colorChoiceCodeFoldInv ?_ ?_
  · intro xs
    exact colorChoiceCodeInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact colorChoiceCodeStep_growth source acc instr hInv hInstr

theorem colorChoiceCodeFromInstructions_tm_polytime :
    TMPolyTimeMap
      colorChoiceCodeInstructionListEncodedType
      setStructuredEncodedType
      colorChoiceCodeFromInstructions := by
  have hFold := colorChoiceCodeFold_tm_polytime
  have hOut := TMPolyTimeMap.snd colorChoiceCodeContextEncodedType setStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, colorChoiceCodeFromInstructions, colorChoiceCodeAccEncodedType] using hComp

theorem colorChoiceBlockExecutable_tm_polytime :
    TMPolyTimeMap
      colorChoiceCodeInputEncodedType
      setStructuredEncodedType
      colorChoiceBlockExecutable := by
  have hComp :=
    TMPolyTimeMap.comp colorChoiceCodeFromInstructions_tm_polytime
      colorChoiceCodeInstructions_tm_polytime
  simpa [Function.comp, colorChoiceBlockExecutable] using hComp

end ExactCover
end Karp21
end ComplexityReduction
