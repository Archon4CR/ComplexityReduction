import ComplexityReduction.Bridges.CostedToTM.Programs.Base

namespace ComplexityReduction
namespace TM2Programs

open Turing.TM2.Stmt

/-!
Finite-state transducer for raw symbol streams with a bounded finite output
block per input symbol.
-/

inductive RawBlockMapStack where
  | input
  | output
  | temp
  deriving DecidableEq, Fintype

abbrev rawBlockMapAlphabet (α β : Type) : RawBlockMapStack → Type
  | RawBlockMapStack.input => α
  | RawBlockMapStack.output => β
  | RawBlockMapStack.temp => β

noncomputable def rawBlockMapMaxLen {α β : Type} [Fintype α]
    (block : α → List β) : Nat :=
  Finset.univ.sup fun a => (block a).length

theorem rawBlockMap_length_le_max {α β : Type} [Fintype α]
    (block : α → List β) (a : α) :
    (block a).length ≤ rawBlockMapMaxLen block := by
  classical
  exact Finset.le_sup (f := fun a => (block a).length) (Finset.mem_univ a)

inductive RawBlockMapLabel (α β : Type) (maxLen : Nat) where
  | readInput
  | pushTemp (a : α) (i : Fin maxLen)
  | moveTemp
  | pushOutput (b : β)
  deriving DecidableEq, Fintype

def rawBlockMapStateIsInput {α β : Type} : Option (α ⊕ β) → Bool
  | some (Sum.inl _) => true
  | _ => false

def rawBlockMapStateIsOutput {α β : Type} : Option (α ⊕ β) → Bool
  | some (Sum.inr _) => true
  | _ => false

noncomputable def rawBlockMapFirstLabel {α β : Type} [Fintype α]
    (block : α → List β) (a : α) :
    RawBlockMapLabel α β (rawBlockMapMaxLen block) := by
  classical
  by_cases h : 0 < (block a).length
  · have hMax : 0 < rawBlockMapMaxLen block :=
      h.trans_le (rawBlockMap_length_le_max block a)
    exact RawBlockMapLabel.pushTemp a ⟨0, hMax⟩
  · exact RawBlockMapLabel.readInput

noncomputable def rawBlockMapNextLabel {α β : Type} [Fintype α]
    (block : α → List β) (a : α) (i : Fin (rawBlockMapMaxLen block)) :
    RawBlockMapLabel α β (rawBlockMapMaxLen block) := by
  classical
  by_cases h : i.val + 1 < (block a).length
  · have hMax : i.val + 1 < rawBlockMapMaxLen block :=
      h.trans_le (rawBlockMap_length_le_max block a)
    exact RawBlockMapLabel.pushTemp a ⟨i.val + 1, hMax⟩
  · exact RawBlockMapLabel.readInput

noncomputable def rawBlockMapMachine (α β : Type) [Fintype α] [Fintype β]
    (block : α → List β) : Turing.FinTM2 where
  K := RawBlockMapStack
  k₀ := RawBlockMapStack.input
  k₁ := RawBlockMapStack.output
  Γ := rawBlockMapAlphabet α β
  Λ := RawBlockMapLabel α β (rawBlockMapMaxLen block)
  main := RawBlockMapLabel.readInput
  σ := Option (α ⊕ β)
  initialState := none
  Γk₀Fin := by
    dsimp [rawBlockMapAlphabet]
    infer_instance
  m
    | RawBlockMapLabel.readInput =>
        pop RawBlockMapStack.input (fun _ head => head.map Sum.inl)
          (branch rawBlockMapStateIsInput
            (goto fun state =>
              match state with
              | some (Sum.inl a) => rawBlockMapFirstLabel block a
              | _ => RawBlockMapLabel.readInput)
            (goto fun _ => RawBlockMapLabel.moveTemp))
    | RawBlockMapLabel.pushTemp a i =>
        if h : i.val < (block a).length then
          push RawBlockMapStack.temp (fun _ => (block a)[i.val]'h)
            (goto fun _ => rawBlockMapNextLabel block a i)
        else
          goto fun _ => RawBlockMapLabel.readInput
    | RawBlockMapLabel.moveTemp =>
        pop RawBlockMapStack.temp (fun _ head => head.map Sum.inr)
          (branch rawBlockMapStateIsOutput
            (goto fun state =>
              match state with
              | some (Sum.inr b) => RawBlockMapLabel.pushOutput b
              | _ => RawBlockMapLabel.moveTemp)
            (load (fun _ => none) halt))
    | RawBlockMapLabel.pushOutput b =>
        push RawBlockMapStack.output (fun _ => b)
          (goto fun _ => RawBlockMapLabel.moveTemp)

noncomputable def rawBlockMapCfg (α β : Type) [Fintype α] [Fintype β]
    (block : α → List β) (label : RawBlockMapLabel α β (rawBlockMapMaxLen block))
    (state : Option (α ⊕ β)) (input : List α) (output temp : List β) :
    (rawBlockMapMachine α β block).Cfg where
  l := some label
  var := state
  stk
    | RawBlockMapStack.input => input
    | RawBlockMapStack.output => output
    | RawBlockMapStack.temp => temp

noncomputable def rawBlockMapHalt (α β : Type) [Fintype α] [Fintype β]
    (block : α → List β) (output : List β) :
    (rawBlockMapMachine α β block).Cfg where
  l := none
  var := none
  stk
    | RawBlockMapStack.input => []
    | RawBlockMapStack.output => output
    | RawBlockMapStack.temp => []

@[simp]
theorem initList_rawBlockMapMachine (α β : Type) [Fintype α] [Fintype β]
    (block : α → List β) (input : List α) :
    Turing.initList (rawBlockMapMachine α β block) input =
      rawBlockMapCfg α β block RawBlockMapLabel.readInput none input [] [] := by
  simp [rawBlockMapMachine, rawBlockMapCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

@[simp]
theorem haltList_rawBlockMapMachine (α β : Type) [Fintype α] [Fintype β]
    (block : α → List β) (output : List β) :
    Turing.haltList (rawBlockMapMachine α β block) output =
      rawBlockMapHalt α β block output := by
  simp [rawBlockMapMachine, rawBlockMapHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

end TM2Programs
end ComplexityReduction
