/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.FillerTriples
import ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold

/-!
Executable filler-triple blocks for one source set in the compact
Exact-Cover-to-3-Dimensional-Matching route.

The runner scans a support list once.  It emits adjacent triples as soon as the
successor is known, remembers the first and previous support elements, and a
finalizer closes the cycle from the last element back to the first.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

def compactFillerBlockContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat EncodedType.nat)

def compactFillerBlockAccEncodedType : EncodedType :=
  EncodedType.prod compactFillerBlockContextEncodedType
    (EncodedType.prod EncodedType.bool
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))

def compactFillerBlockInstructionEncodedType : EncodedType :=
  EncodedType.sum compactFillerBlockContextEncodedType EncodedType.nat

def compactFillerBlockInstructionListEncodedType : EncodedType :=
  EncodedType.list compactFillerBlockInstructionEncodedType

def compactFillerBlockInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat setStructuredEncodedType))

abbrev CompactFillerBlockContext := Nat × Nat × Nat
abbrev CompactFillerBlockAcc :=
  CompactFillerBlockContext × Bool × Nat × Nat × List (Nat × Nat × Nat)

def compactFillerBlockInitAcc : CompactFillerBlockAcc :=
  ((0, 0, 0), false, 0, 0, [])

def compactFillerBlockInitInstruction (ctx : CompactFillerBlockContext) :
    compactFillerBlockInstructionEncodedType.Carrier :=
  Sum.inl ctx

def compactFillerBlockElementInstruction (x : Nat) :
    compactFillerBlockInstructionEncodedType.Carrier :=
  Sum.inr x

def compactFillerBlockInstructions
    (p : Nat × Nat × Nat × List Nat) :
    List compactFillerBlockInstructionEncodedType.Carrier :=
  compactFillerBlockInitInstruction (p.1, p.2.1, p.2.2.1) ::
    (compactSupportExecutable (p.1, p.2.2.2)).map compactFillerBlockElementInstruction

def compactFillerBlockAppendTriple (p : CompactFillerBlockAcc × Nat) :
    List (Nat × Nat × Nat) :=
  let ctx := p.1.1
  let prev := p.1.2.2.2.1
  let out := p.1.2.2.2.2
  let x := p.2
  out ++ [compactFillerTripleFromData (ctx.1, ctx.2.1, ctx.2.2, prev, x)]

def compactFillerBlockElementStep (p : CompactFillerBlockAcc × Nat) :
    CompactFillerBlockAcc :=
  let ctx := p.1.1
  let seen := p.1.2.1
  let first := p.1.2.2.1
  let x := p.2
  if seen then
    (ctx, true, first, x, compactFillerBlockAppendTriple p)
  else
    (ctx, true, x, x, p.1.2.2.2.2)

def compactFillerBlockStep
    (p : CompactFillerBlockAcc × compactFillerBlockInstructionEncodedType.Carrier) :
    CompactFillerBlockAcc :=
  match p.2 with
  | Sum.inl ctx => (ctx, false, 0, 0, [])
  | Sum.inr x => compactFillerBlockElementStep (p.1, x)

def compactFillerBlockClosingTriple (acc : CompactFillerBlockAcc) :
    Nat × Nat × Nat :=
  let ctx := acc.1
  let first := acc.2.2.1
  let prev := acc.2.2.2.1
  compactFillerTripleFromData (ctx.1, ctx.2.1, ctx.2.2, prev, first)

def compactFillerBlockFinalize (acc : CompactFillerBlockAcc) :
    List (Nat × Nat × Nat) :=
  if acc.2.1 then
    acc.2.2.2.2 ++ [compactFillerBlockClosingTriple acc]
  else
    acc.2.2.2.2

def compactFillerBlockFoldAcc
    (xs : List compactFillerBlockInstructionEncodedType.Carrier) :
    CompactFillerBlockAcc :=
  xs.foldl (fun acc instr => compactFillerBlockStep (acc, instr))
    compactFillerBlockInitAcc

def compactFillerBlockFromInstructions
    (xs : List compactFillerBlockInstructionEncodedType.Carrier) :
    List (Nat × Nat × Nat) :=
  compactFillerBlockFinalize (compactFillerBlockFoldAcc xs)

def compactFillerTriplesForSourceSetExecutable
    (p : Nat × Nat × Nat × List Nat) :
    List (Nat × Nat × Nat) :=
  compactFillerBlockFromInstructions (compactFillerBlockInstructions p)

/-! ### TM certificates for one source-set filler block -/

theorem compactFillerBlockInitInstruction_tm_polytime :
    TMPolyTimeMap
      compactFillerBlockContextEncodedType
      compactFillerBlockInstructionEncodedType
      compactFillerBlockInitInstruction := by
  simpa [compactFillerBlockInstructionEncodedType, compactFillerBlockInitInstruction] using
    TMPolyTimeMap.inl compactFillerBlockContextEncodedType EncodedType.nat

theorem compactFillerBlockElementInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactFillerBlockInstructionEncodedType
      compactFillerBlockElementInstruction := by
  simpa [compactFillerBlockInstructionEncodedType,
    compactFillerBlockElementInstruction] using
    TMPolyTimeMap.inr compactFillerBlockContextEncodedType EncodedType.nat

theorem compactFillerBlockInstructions_tm_polytime :
    TMPolyTimeMap
      compactFillerBlockInputEncodedType
      compactFillerBlockInstructionListEncodedType
      compactFillerBlockInstructions := by
  let X := compactFillerBlockInputEncodedType
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, compactFillerBlockInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat setStructuredEncodedType))
  have hPayload :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat setStructuredEncodedType))
        (fun p : X.Carrier => p.2) := by
    simpa [X, compactFillerBlockInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat setStructuredEncodedType))
  have hBeta : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat setStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hInner :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setStructuredEncodedType)
        (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
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
      TMPolyTimeMap X compactFillerBlockContextEncodedType
        (fun p : X.Carrier => (p.1, p.2.1, p.2.2.1)) := by
    simpa [compactFillerBlockContextEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse (TMPolyTimeMap.prod_mk hBeta hJ)
  have hInit :
      TMPolyTimeMap X compactFillerBlockInstructionEncodedType
        (fun p : X.Carrier => compactFillerBlockInitInstruction (p.1, p.2.1, p.2.2.1)) := by
    have hComp := TMPolyTimeMap.comp compactFillerBlockInitInstruction_tm_polytime hCtx
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
      TMPolyTimeMap X compactFillerBlockInstructionListEncodedType
        (fun p : X.Carrier =>
          (compactSupportExecutable (p.1, p.2.2.2)).map
            compactFillerBlockElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactFillerBlockElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hSupport
    simpa [Function.comp, compactFillerBlockInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactFillerBlockInstructionEncodedType
          compactFillerBlockInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactFillerBlockInitInstruction (p.1, p.2.1, p.2.2.1),
            (compactSupportExecutable (p.1, p.2.2.2)).map
              compactFillerBlockElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMapped
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons compactFillerBlockInstructionEncodedType) hConsInput
  simpa [Function.comp, compactFillerBlockInstructions,
    compactFillerBlockInstructionListEncodedType, X] using hCons

theorem compactFillerBlockStepLeft_tm_polytime :
    TMPolyTimeMap
      compactFillerBlockContextEncodedType
      compactFillerBlockAccEncodedType
      (fun ctx : CompactFillerBlockContext =>
        (ctx, false, (0 : Nat), (0 : Nat), ([] : List (Nat × Nat × Nat)))) := by
  have hCtx := TMPolyTimeMap.id compactFillerBlockContextEncodedType
  have hFalse :
      TMPolyTimeMap compactFillerBlockContextEncodedType EncodedType.bool
        (fun _ : CompactFillerBlockContext => false) :=
    TMPolyTimeMap.const compactFillerBlockContextEncodedType EncodedType.bool false
  have hZero :
      TMPolyTimeMap compactFillerBlockContextEncodedType EncodedType.nat
        (fun _ : CompactFillerBlockContext => (0 : Nat)) :=
    TMPolyTimeMap.const compactFillerBlockContextEncodedType EncodedType.nat
      (show EncodedType.nat.Carrier from (0 : Nat))
  have hEmpty :
      TMPolyTimeMap compactFillerBlockContextEncodedType tripleListStructuredEncodedType
        (fun _ : CompactFillerBlockContext => ([] : List (Nat × Nat × Nat))) :=
    TMPolyTimeMap.const compactFillerBlockContextEncodedType tripleListStructuredEncodedType []
  have hPrevOut :
      TMPolyTimeMap compactFillerBlockContextEncodedType
        (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)
        (fun _ : CompactFillerBlockContext => ((0 : Nat), ([] : List (Nat × Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hZero hEmpty
  have hFirstTail :
      TMPolyTimeMap compactFillerBlockContextEncodedType
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType))
        (fun _ : CompactFillerBlockContext =>
          ((0 : Nat), ((0 : Nat), ([] : List (Nat × Nat × Nat))))) :=
    TMPolyTimeMap.prod_mk hZero hPrevOut
  have hSeenTail :
      TMPolyTimeMap compactFillerBlockContextEncodedType
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))
        (fun _ : CompactFillerBlockContext =>
          (false, ((0 : Nat), ((0 : Nat), ([] : List (Nat × Nat × Nat)))))) :=
    TMPolyTimeMap.prod_mk hFalse hFirstTail
  simpa [compactFillerBlockAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hSeenTail

theorem compactFillerBlockAppendTriple_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactFillerBlockAccEncodedType EncodedType.nat)
      tripleListStructuredEncodedType
      compactFillerBlockAppendTriple := by
  let X := EncodedType.prod compactFillerBlockAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactFillerBlockAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactFillerBlockAccEncodedType EncodedType.nat
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactFillerBlockAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X compactFillerBlockContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst compactFillerBlockContextEncodedType
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactFillerBlockAccEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))
        (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd compactFillerBlockContextEncodedType
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactFillerBlockAccEncodedType, X] using hComp
  have hFirstPayload :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType))
        (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hPrevOut :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)
        (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hFirstPayload
    simpa [Function.comp, X] using hComp
  have hPrev : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPrevOut
    simpa [Function.comp, X] using hComp
  have hOut :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier => p.1.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPrevOut
    simpa [Function.comp, X] using hComp
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, compactFillerBlockContextEncodedType, X] using hComp
  have hCtxTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, compactFillerBlockContextEncodedType, X] using hComp
  have hBeta : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hCtxTail
    simpa [Function.comp, X] using hComp
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hCtxTail
    simpa [Function.comp, X] using hComp
  have hTripleInput :
      TMPolyTimeMap X compactFillerTripleFromDataInputEncodedType
        (fun p : X.Carrier => (p.1.1.1, p.1.1.2.1, p.1.1.2.2, p.1.2.2.2.1, p.2)) := by
    simpa [compactFillerTripleFromDataInputEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse
        (TMPolyTimeMap.prod_mk hBeta
          (TMPolyTimeMap.prod_mk hJ (TMPolyTimeMap.prod_mk hPrev hX)))
  have hTriple :
      TMPolyTimeMap X tripleStructuredEncodedType
        (fun p : X.Carrier =>
          compactFillerTripleFromData
            (p.1.1.1, p.1.1.2.1, p.1.1.2.2, p.1.2.2.2.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp compactFillerTripleFromData_tm_polytime hTripleInput
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier =>
          [compactFillerTripleFromData
            (p.1.1.1, p.1.1.2.1, p.1.1.2.2, p.1.2.2.2.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton tripleStructuredEncodedType) hTriple
    simpa [Function.comp, tripleListStructuredEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show List (Nat × Nat × Nat) from p.1.2.2.2.2),
            [compactFillerTripleFromData
              (p.1.1.1, p.1.1.2.1, p.1.1.2.2, p.1.2.2.2.1, p.2)])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append tripleStructuredEncodedType) hAppendInput
  simpa [Function.comp, compactFillerBlockAppendTriple,
    tripleListStructuredEncodedType, X] using hAppend

theorem compactFillerBlockElementStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactFillerBlockAccEncodedType EncodedType.nat)
      compactFillerBlockAccEncodedType
      compactFillerBlockElementStep := by
  let X := EncodedType.prod compactFillerBlockAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactFillerBlockAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactFillerBlockAccEncodedType EncodedType.nat
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactFillerBlockAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X compactFillerBlockContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst compactFillerBlockContextEncodedType
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactFillerBlockAccEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))
        (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd compactFillerBlockContextEncodedType
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactFillerBlockAccEncodedType, X] using hComp
  have hSeen : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hFirstPayload :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType))
        (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hFirst : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hFirstPayload
    simpa [Function.comp, X] using hComp
  have hPrevOut :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)
        (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hFirstPayload
    simpa [Function.comp, X] using hComp
  have hOut :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier => p.1.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPrevOut
    simpa [Function.comp, X] using hComp
  have hTrue :
      TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFalseBranchTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType))
        (fun p : X.Carrier => (p.2, p.2, p.1.2.2.2.2)) := by
    have hPrevOutNew :
        TMPolyTimeMap X (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)
          (fun p : X.Carrier => (p.2, p.1.2.2.2.2)) :=
      TMPolyTimeMap.prod_mk hX hOut
    exact TMPolyTimeMap.prod_mk hX hPrevOutNew
  have hFalseBranchSeenTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))
        (fun p : X.Carrier => (true, (p.2, p.2, p.1.2.2.2.2))) :=
    TMPolyTimeMap.prod_mk hTrue hFalseBranchTail
  have hFalseBranch :
      TMPolyTimeMap X compactFillerBlockAccEncodedType
        (fun p : X.Carrier => (p.1.1, true, p.2, p.2, p.1.2.2.2.2)) :=
    TMPolyTimeMap.prod_mk hCtx hFalseBranchSeenTail
  have hAppend := compactFillerBlockAppendTriple_tm_polytime
  have hTrueBranchTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType))
        (fun p : X.Carrier => (p.1.2.2.1, p.2, compactFillerBlockAppendTriple p)) := by
    have hPrevOutNew :
        TMPolyTimeMap X (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)
          (fun p : X.Carrier => (p.2, compactFillerBlockAppendTriple p)) :=
      TMPolyTimeMap.prod_mk hX hAppend
    exact TMPolyTimeMap.prod_mk hFirst hPrevOutNew
  have hTrueBranchSeenTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))
        (fun p : X.Carrier => (true, (p.1.2.2.1, p.2, compactFillerBlockAppendTriple p))) :=
    TMPolyTimeMap.prod_mk hTrue hTrueBranchTail
  have hTrueBranch :
      TMPolyTimeMap X compactFillerBlockAccEncodedType
        (fun p : X.Carrier => (p.1.1, true, p.1.2.2.1, p.2,
          compactFillerBlockAppendTriple p)) :=
    TMPolyTimeMap.prod_mk hCtx hTrueBranchSeenTail
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.1.2.1, p)) :=
    TMPolyTimeMap.prod_mk hSeen (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) compactFillerBlockAccEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => (p.2.1.1, true, p.2.1.2.2.1, p.2.2,
              compactFillerBlockAppendTriple p.2)
          | false => (p.2.1.1, true, p.2.2, p.2.2, p.2.1.2.2.2.2)) :=
    graphBoolProduct_dispatch_tm_polytime X compactFillerBlockAccEncodedType
      (fFalse := fun p : X.Carrier => (p.1.1, true, p.2, p.2, p.1.2.2.2.2))
      (fTrue := fun p : X.Carrier =>
        (p.1.1, true, p.1.2.2.1, p.2, compactFillerBlockAppendTriple p))
      hFalseBranch hTrueBranch
  have hComp := TMPolyTimeMap.comp hBranch hBranchInput
  convert hComp using 1
  funext p
  cases h : p.1.2.1
  · simp [Function.comp, compactFillerBlockElementStep, h]
    rfl
  · simp [Function.comp, compactFillerBlockElementStep, h]
    rfl

theorem compactFillerBlockStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactFillerBlockAccEncodedType compactFillerBlockInstructionEncodedType)
      compactFillerBlockAccEncodedType
      compactFillerBlockStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      compactFillerBlockAccEncodedType compactFillerBlockContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim compactFillerBlockStepLeft_tm_polytime
      compactFillerBlockElementStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def compactFillerBlockFoldInv
    (N : Nat) (acc : compactFillerBlockAccEncodedType.Carrier) : Prop :=
  acc = compactFillerBlockInitAcc ∨
    ((show Nat from acc.1.1) + 1 ≤ N ∧
      (show Nat from acc.1.2.1) + 1 ≤ N ∧
      (show Nat from acc.1.2.2) + 1 ≤ N ∧
      (show Nat from acc.2.2.1) + 1 ≤ N ∧
      (show Nat from acc.2.2.2.1) + 1 ≤ N)

theorem compactFillerBlockInitAcc_bound
    (xs : List compactFillerBlockInstructionEncodedType.Carrier) :
    compactFillerBlockFoldInv (compactFillerBlockInstructionListEncodedType.inputSize xs)
        compactFillerBlockInitAcc ∧
      compactFillerBlockAccEncodedType.inputSize compactFillerBlockInitAcc ≤
        (Polynomial.C 20).eval (compactFillerBlockInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · have hNilTriples :
        tripleStructuredEncodedType.list.inputSize ([] : List (Nat × Nat × Nat)) = 0 :=
      EncodedType.inputSize_list_nil tripleStructuredEncodedType
    simp [compactFillerBlockInitAcc, compactFillerBlockAccEncodedType,
      compactFillerBlockContextEncodedType, tripleListStructuredEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat, EncodedType.inputSize_bool,
      hNilTriples]

theorem compactFillerBlockStep_growth
    (source : List compactFillerBlockInstructionEncodedType.Carrier)
    (acc : compactFillerBlockAccEncodedType.Carrier)
    (instr : compactFillerBlockInstructionEncodedType.Carrier)
    (hInv :
      compactFillerBlockFoldInv
        (compactFillerBlockInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactFillerBlockInstructionEncodedType.inputSize instr ≤
        compactFillerBlockInstructionListEncodedType.inputSize source) :
    compactFillerBlockFoldInv
        (compactFillerBlockInstructionListEncodedType.inputSize source)
        (compactFillerBlockStep (acc, instr)) ∧
      compactFillerBlockAccEncodedType.inputSize (compactFillerBlockStep (acc, instr)) ≤
        compactFillerBlockAccEncodedType.inputSize acc +
          (Polynomial.C 100 * (Polynomial.X * Polynomial.X) + Polynomial.C 100).eval
            (compactFillerBlockInstructionListEncodedType.inputSize source) := by
  let N := compactFillerBlockInstructionListEncodedType.inputSize source
  rcases acc with ⟨ctx, seen, first, prev, out⟩
  rcases ctx with ⟨universeSize, beta, j⟩
  change Nat at universeSize
  change Nat at beta
  change Nat at j
  change Nat at first
  change Nat at prev
  cases instr with
  | inl newCtx =>
      rcases newCtx with ⟨newUniverse, newBeta, newJ⟩
      change Nat at newUniverse
      change Nat at newBeta
      change Nat at newJ
      have hCtx :
          compactFillerBlockContextEncodedType.inputSize (newUniverse, newBeta, newJ) + 1 ≤
            N := by
        simpa [N, compactFillerBlockInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hInstr
      have hNewUniverse : newUniverse + 1 ≤ N := by
        simp [compactFillerBlockContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewBeta : newBeta + 1 ≤ N := by
        simp [compactFillerBlockContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewJ : newJ + 1 ≤ N := by
        simp [compactFillerBlockContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      constructor
      · have hN : 1 ≤ N := by omega
        have hInvNew :
            compactFillerBlockFoldInv N
              ((newUniverse, newBeta, newJ), false, (0 : Nat), (0 : Nat),
                ([] : List (Nat × Nat × Nat))) :=
          Or.inr ⟨hNewUniverse, hNewBeta, hNewJ, by omega, by omega⟩
        simpa [N, compactFillerBlockStep] using hInvNew
      · have hNilTriples :
            tripleStructuredEncodedType.list.inputSize ([] : List (Nat × Nat × Nat)) = 0 :=
          EncodedType.inputSize_list_nil tripleStructuredEncodedType
        simp [compactFillerBlockStep, compactFillerBlockAccEncodedType,
          compactFillerBlockContextEncodedType, tripleListStructuredEncodedType,
          EncodedType.inputSize_prod, EncodedType.inputSize_nat,
          EncodedType.inputSize_bool, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_X, hNilTriples]
        have hN : 1 ≤ N := by omega
        nlinarith [hNewUniverse, hNewBeta, hNewJ, hN, sq_nonneg (N : Int)]
  | inr x =>
      change Nat at x
      have hx : x + 1 ≤ N := by
        have hxTagged : x + 1 < N := by
          simpa [N, compactFillerBlockInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, EncodedType.nat] using hInstr
        omega
      have hBounds :
          universeSize + 1 ≤ N ∧ beta + 1 ≤ N ∧ j + 1 ≤ N ∧
            first + 1 ≤ N ∧ prev + 1 ≤ N := by
        rcases hInv with hInit | hBound
        · injection hInit with hCtxEq hTailEq
          injection hCtxEq with hUniverse hCtxTail
          injection hCtxTail with hBeta hJ
          injection hTailEq with _hSeen hRestEq
          injection hRestEq with hFirst hPrevOutEq
          injection hPrevOutEq with hPrev _hOut
          subst universeSize
          subst beta
          subst j
          subst first
          subst prev
          omega
        · exact hBound
      constructor
      · cases hSeen : seen
        · have hInvNew :
              compactFillerBlockFoldInv N
                ((universeSize, beta, j), true, x, x, out) :=
            Or.inr ⟨hBounds.1, hBounds.2.1, hBounds.2.2.1, hx, hx⟩
          simpa [N, compactFillerBlockStep, compactFillerBlockElementStep, hSeen] using hInvNew
        · have hInvNew :
              compactFillerBlockFoldInv N
                ((universeSize, beta, j), true, first, x,
                  compactFillerBlockAppendTriple
                    (((universeSize, beta, j), seen, first, prev, out), x)) :=
            Or.inr ⟨hBounds.1, hBounds.2.1, hBounds.2.2.1,
              hBounds.2.2.2.1, hx⟩
          simpa [N, compactFillerBlockStep, compactFillerBlockElementStep, hSeen] using hInvNew
      · cases hSeen : seen
        · simp [compactFillerBlockStep, compactFillerBlockElementStep,
            compactFillerBlockAccEncodedType,
            compactFillerBlockContextEncodedType, tripleListStructuredEncodedType,
            EncodedType.inputSize_prod, EncodedType.inputSize_nat,
            EncodedType.inputSize_bool, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_X]
          nlinarith [hBounds.2.2.2.1, hBounds.2.2.2.2, hx, sq_nonneg (N : Int)]
        · let triple := compactFillerTripleFromData (universeSize, beta, j, prev, x)
          have hSingleton :
              tripleListStructuredEncodedType.inputSize [triple] ≤
                10 * (N * N) + 20 := by
            simpa [triple] using
              compactFillerTripleFromData_singleton_inputSize_le
                N universeSize beta j prev x hBounds.1 hBounds.2.1 hBounds.2.2.1
                hBounds.2.2.2.2 hx
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
                tripleListStructuredEncodedType.inputSize out + (10 * (N * N) + 20) := by
            rw [hAppendSize]
            exact Nat.add_le_add_left hSingleton _
          have hAppendLeRaw :
              tripleStructuredEncodedType.list.inputSize
                  ((show List (Nat × Nat × Nat) from out) ++
                    [compactFillerTripleFromData (universeSize, beta, j, prev, x)]) ≤
                tripleStructuredEncodedType.list.inputSize out + (10 * (N * N) + 20) := by
            simpa [tripleListStructuredEncodedType, triple] using hAppendLe
          simp [compactFillerBlockStep, compactFillerBlockElementStep,
            compactFillerBlockAppendTriple, compactFillerBlockAccEncodedType,
            compactFillerBlockContextEncodedType, tripleListStructuredEncodedType,
            EncodedType.inputSize_prod, EncodedType.inputSize_nat,
            EncodedType.inputSize_bool, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_X] at hAppendLeRaw ⊢
          nlinarith [hAppendLeRaw, hBounds.2.2.2.2, hx, sq_nonneg (N : Int)]

theorem compactFillerBlockFoldAcc_tm_polytime :
    TMPolyTimeMap
      compactFillerBlockInstructionListEncodedType
      compactFillerBlockAccEncodedType
      compactFillerBlockFoldAcc := by
  rcases compactFillerBlockStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactFillerBlockInstructionEncodedType compactFillerBlockAccEncodedType
      compactFillerBlockStep compactFillerBlockInitAcc hStep
      (Polynomial.C 20)
      (Polynomial.C 100 * (Polynomial.X * Polynomial.X) + Polynomial.C 100)
      compactFillerBlockFoldInv ?_ ?_
  · intro xs
    exact compactFillerBlockInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactFillerBlockStep_growth source acc instr hInv hInstr

theorem compactFillerBlockClosingTriple_tm_polytime :
    TMPolyTimeMap
      compactFillerBlockAccEncodedType
      tripleStructuredEncodedType
      compactFillerBlockClosingTriple := by
  let X := compactFillerBlockAccEncodedType
  have hCtx : TMPolyTimeMap X compactFillerBlockContextEncodedType (fun acc : X.Carrier => acc.1) := by
    simpa [X] using TMPolyTimeMap.fst compactFillerBlockContextEncodedType
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))
        (fun acc : X.Carrier => acc.2) := by
    simpa [X] using TMPolyTimeMap.snd compactFillerBlockContextEncodedType
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))
  have hFirstPayload :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType))
        (fun acc : X.Carrier => acc.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hFirst : TMPolyTimeMap X EncodedType.nat (fun acc : X.Carrier => acc.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hFirstPayload
    simpa [Function.comp, X] using hComp
  have hPrevOut :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)
        (fun acc : X.Carrier => acc.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hFirstPayload
    simpa [Function.comp, X] using hComp
  have hPrev : TMPolyTimeMap X EncodedType.nat (fun acc : X.Carrier => acc.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPrevOut
    simpa [Function.comp, X] using hComp
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun acc : X.Carrier => acc.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, compactFillerBlockContextEncodedType, X] using hComp
  have hCtxTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun acc : X.Carrier => acc.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, compactFillerBlockContextEncodedType, X] using hComp
  have hBeta : TMPolyTimeMap X EncodedType.nat (fun acc : X.Carrier => acc.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hCtxTail
    simpa [Function.comp, X] using hComp
  have hJ : TMPolyTimeMap X EncodedType.nat (fun acc : X.Carrier => acc.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hCtxTail
    simpa [Function.comp, X] using hComp
  have hTripleInput :
      TMPolyTimeMap X compactFillerTripleFromDataInputEncodedType
        (fun acc : X.Carrier => (acc.1.1, acc.1.2.1, acc.1.2.2,
          acc.2.2.2.1, acc.2.2.1)) := by
    simpa [compactFillerTripleFromDataInputEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse
        (TMPolyTimeMap.prod_mk hBeta
          (TMPolyTimeMap.prod_mk hJ (TMPolyTimeMap.prod_mk hPrev hFirst)))
  have hComp := TMPolyTimeMap.comp compactFillerTripleFromData_tm_polytime hTripleInput
  simpa [Function.comp, compactFillerBlockClosingTriple, X] using hComp

theorem compactFillerBlockFinalize_tm_polytime :
    TMPolyTimeMap
      compactFillerBlockAccEncodedType
      tripleListStructuredEncodedType
      compactFillerBlockFinalize := by
  let X := compactFillerBlockAccEncodedType
  have hAcc : TMPolyTimeMap X X (fun acc : X.Carrier => acc) := TMPolyTimeMap.id X
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))
        (fun acc : X.Carrier => acc.2) := by
    simpa [X] using TMPolyTimeMap.snd compactFillerBlockContextEncodedType
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)))
  have hSeen : TMPolyTimeMap X EncodedType.bool (fun acc : X.Carrier => acc.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hFirstPayload :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType))
        (fun acc : X.Carrier => acc.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hPrevOut :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)
        (fun acc : X.Carrier => acc.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat tripleListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hFirstPayload
    simpa [Function.comp, X] using hComp
  have hOut :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun acc : X.Carrier => acc.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPrevOut
    simpa [Function.comp, X] using hComp
  have hClosing := compactFillerBlockClosingTriple_tm_polytime
  have hSingleton :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun acc : X.Carrier => [compactFillerBlockClosingTriple acc]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton tripleStructuredEncodedType) hClosing
    simpa [Function.comp, tripleListStructuredEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType)
        (fun acc : X.Carrier =>
          ((show List (Nat × Nat × Nat) from acc.2.2.2.2),
            [compactFillerBlockClosingTriple acc])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X tripleListStructuredEncodedType
        (fun acc : X.Carrier =>
          (show List (Nat × Nat × Nat) from acc.2.2.2.2) ++
            [compactFillerBlockClosingTriple acc]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append tripleStructuredEncodedType) hAppendInput
    simpa [Function.comp, tripleListStructuredEncodedType, X] using hComp
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun acc : X.Carrier => (acc.2.1, acc)) :=
    TMPolyTimeMap.prod_mk hSeen hAcc
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) tripleListStructuredEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (show List (Nat × Nat × Nat) from p.2.2.2.2.2) ++
                [compactFillerBlockClosingTriple p.2]
          | false => p.2.2.2.2.2) :=
    graphBoolProduct_dispatch_tm_polytime X tripleListStructuredEncodedType
      (fFalse := fun acc : X.Carrier => (show List (Nat × Nat × Nat) from acc.2.2.2.2))
      (fTrue := fun acc : X.Carrier =>
        (show List (Nat × Nat × Nat) from acc.2.2.2.2) ++
          [compactFillerBlockClosingTriple acc])
      hOut hAppend
  have hComp := TMPolyTimeMap.comp hBranch hBranchInput
  convert hComp using 1
  funext acc
  cases h : acc.2.1
  · simp [Function.comp, compactFillerBlockFinalize, h]
  · simp [Function.comp, compactFillerBlockFinalize, h]

theorem compactFillerBlockFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactFillerBlockInstructionListEncodedType
      tripleListStructuredEncodedType
      compactFillerBlockFromInstructions := by
  have hComp := TMPolyTimeMap.comp compactFillerBlockFinalize_tm_polytime
    compactFillerBlockFoldAcc_tm_polytime
  simpa [Function.comp, compactFillerBlockFromInstructions,
    compactFillerBlockFoldAcc] using hComp

theorem compactFillerTriplesForSourceSetExecutable_tm_polytime :
    TMPolyTimeMap
      compactFillerBlockInputEncodedType
      tripleListStructuredEncodedType
      compactFillerTriplesForSourceSetExecutable := by
  have hComp := TMPolyTimeMap.comp compactFillerBlockFromInstructions_tm_polytime
    compactFillerBlockInstructions_tm_polytime
  simpa [Function.comp, compactFillerTriplesForSourceSetExecutable] using hComp

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
