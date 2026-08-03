/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.Certificates.CostedMap
import ComplexityReduction.CSP.FiniteDomain.Basic
import ComplexityReduction.Core.Reduction

/-!
Primitive-positive representation blocks for finite-domain CSP languages.

The definitions mirror Jeavons-Cohen-Gyssens' derived-relation view: free
variables occupy positions `0, ..., arity - 1`, while all other variables are
existentially supplied auxiliary variables.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace PPDef

/-- Extend a free tuple with a total auxiliary assignment. -/
def extendTupleAssignment {D : Type} {k : Nat} (t : Tuple D k) (aux : Assignment D) :
    Assignment D :=
  fun x => if h : x < k then t ⟨x, h⟩ else aux x

@[simp]
theorem extendTupleAssignment_of_lt {D : Type} {k : Nat} (t : Tuple D k)
    (aux : Assignment D) {x : Nat} (hx : x < k) :
    extendTupleAssignment t aux x = t ⟨x, hx⟩ := by
  simp [extendTupleAssignment, hx]

@[simp]
theorem extendTupleAssignment_of_not_lt {D : Type} {k : Nat} (t : Tuple D k)
    (aux : Assignment D) {x : Nat} (hx : ¬ x < k) :
    extendTupleAssignment t aux x = aux x := by
  simp [extendTupleAssignment, hx]

/-- Splice a source assignment with an auxiliary assignment starting at `base`. -/
def spliceAssignment {D : Type} (base : Nat) (source aux : Assignment D) :
    Assignment D :=
  fun x => if x < base then source x else aux (x - base)

@[simp]
theorem spliceAssignment_of_lt {D : Type} (base : Nat) (source aux : Assignment D)
    {x : Nat} (hx : x < base) :
    spliceAssignment base source aux x = source x := by
  simp [spliceAssignment, hx]

@[simp]
theorem spliceAssignment_base_add {D : Type} (base : Nat) (source aux : Assignment D)
    (x : Nat) :
    spliceAssignment base source aux (base + x) = aux x := by
  have hx : ¬ base + x < base := by omega
  simp [spliceAssignment, hx]

/-- A pp-style representation block over target language `Γ`. -/
structure RelationFormula {D : Type} (Γ : Language D) (arity : Nat) where
  constraints : Formula Γ
  notes : String := ""

/-- A representation block defines `R` when it is satisfiable exactly on tuples in `R`. -/
def RepresentsRelation {D : Type} (Γ : Language D) (R : Rel D)
    (rep : RelationFormula Γ R.arity) : Prop :=
  ∀ t : Tuple D R.arity,
    R.Holds t ↔ ∃ aux : Assignment D,
      Formula.Satisfies rep.constraints (extendTupleAssignment t aux)

/-- A representation for every relation symbol of a source language. -/
structure LanguageRepresentation {D : Type} (Δ Γ : Language D) where
  block : ∀ s : Δ.Symbol, RelationFormula Γ (Δ.relationOf s).arity
  represents : ∀ s : Δ.Symbol, RepresentsRelation Γ (Δ.relationOf s) (block s)
  notes : String := ""

/--
Variable map for instantiating a representation block against one source
constraint. Free variables are substituted by the constraint scope; auxiliary
variables are placed at `auxBase + x`.
-/
def representationBlockVarMap {D : Type} {Δ : Language D} (c : Constraint Δ)
    (auxBase x : Nat) : Nat :=
  if h : x < (Δ.relationOf c.symbol).arity then c.vars ⟨x, h⟩ else auxBase + x

/-- Expand one source constraint through a representation block at `auxBase`. -/
def constraintViaRepresentationAt {D : Type} {Δ Γ : Language D}
    (rep : LanguageRepresentation Δ Γ) (c : Constraint Δ) (auxBase : Nat) :
    Formula Γ :=
  Formula.mapVars
    (representationBlockVarMap c auxBase)
    (rep.block c.symbol).constraints

/-- Recursive formula expansion with one auxiliary block per source constraint. -/
noncomputable def formulaViaRepresentationFrom {D : Type} {Δ Γ : Language D}
    (rep : LanguageRepresentation Δ Γ) (auxBase blockWidth : Nat) :
    Formula Δ → Formula Γ
  | [] => []
  | c :: φ =>
      constraintViaRepresentationAt rep c auxBase ++
        formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ

theorem blockAssignment_eq_extend {D : Type} {Δ : Language D}
    (c : Constraint Δ) (auxBase : Nat)
    (a : Assignment D) :
    (fun x => a (representationBlockVarMap c auxBase x)) =
      extendTupleAssignment (Constraint.assignmentTuple c a)
        (fun x => a (auxBase + x)) := by
  funext x
  by_cases hx : x < (Δ.relationOf c.symbol).arity
  · simp [representationBlockVarMap, extendTupleAssignment, Constraint.assignmentTuple, hx]
  · simp [representationBlockVarMap, extendTupleAssignment, hx]

/-- Soundness of one instantiated representation block. -/
theorem constraintViaRepresentationAt_sound {D : Type} {Δ Γ : Language D}
    (rep : LanguageRepresentation Δ Γ) (c : Constraint Δ) (auxBase : Nat)
    (a : Assignment D)
    (h :
      Formula.Satisfies (constraintViaRepresentationAt rep c auxBase) a) :
    Constraint.Satisfies c a := by
  have hBlock :
      Formula.Satisfies (rep.block c.symbol).constraints
        (fun x => a (representationBlockVarMap c auxBase x)) := by
    simpa [constraintViaRepresentationAt] using h
  have hAssign :=
    blockAssignment_eq_extend c auxBase a
  have hExists :
      ∃ aux : Assignment D,
        Formula.Satisfies (rep.block c.symbol).constraints
          (extendTupleAssignment (Constraint.assignmentTuple c a) aux) := by
    refine ⟨fun x => a (auxBase + x), ?_⟩
    simpa [hAssign] using hBlock
  exact (rep.represents c.symbol (Constraint.assignmentTuple c a)).2 hExists

/-- Completeness of one instantiated representation block when the source scope is fresh. -/
theorem constraintViaRepresentationAt_complete {D : Type} {Δ Γ : Language D}
    (rep : LanguageRepresentation Δ Γ) (c : Constraint Δ) (auxBase : Nat)
    (a : Assignment D)
    (hFresh : ∀ i : Fin (Δ.relationOf c.symbol).arity, c.vars i < auxBase)
    (hSat : Constraint.Satisfies c a) :
    ∃ b : Assignment D,
      (∀ x, x < auxBase → b x = a x) ∧
        Formula.Satisfies (constraintViaRepresentationAt rep c auxBase) b := by
  rcases (rep.represents c.symbol (Constraint.assignmentTuple c a)).1 hSat with
    ⟨aux, hAux⟩
  let b : Assignment D := spliceAssignment auxBase a aux
  refine ⟨b, ?_, ?_⟩
  · intro x hx
    simp [b, hx]
  · have hAssign :
        (fun x => b (representationBlockVarMap c auxBase x)) =
          extendTupleAssignment (Constraint.assignmentTuple c a) aux := by
      funext x
      by_cases hx : x < (Δ.relationOf c.symbol).arity
      · simp [representationBlockVarMap, extendTupleAssignment, Constraint.assignmentTuple,
          b, hFresh ⟨x, hx⟩, hx]
      · simp [representationBlockVarMap, extendTupleAssignment, b, hx]
    simpa [constraintViaRepresentationAt, hAssign] using hAux

/-- Soundness of canonical recursive formula expansion. -/
theorem formulaViaRepresentationFrom_sound {D : Type} {Δ Γ : Language D}
    (rep : LanguageRepresentation Δ Γ) (auxBase blockWidth : Nat)
    (φ : Formula Δ) (a : Assignment D)
    (h : Formula.Satisfies (formulaViaRepresentationFrom rep auxBase blockWidth φ) a) :
    Formula.Satisfies φ a := by
  induction φ generalizing auxBase with
  | nil =>
      simp
  | cons c φ ih =>
      have hAppend :
          Formula.Satisfies (constraintViaRepresentationAt rep c auxBase) a ∧
            Formula.Satisfies
              (formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ) a := by
        simpa [formulaViaRepresentationFrom] using h
      exact (Formula.satisfies_cons c φ a).2
        ⟨constraintViaRepresentationAt_sound rep c auxBase a hAppend.1,
          ih (auxBase := auxBase + blockWidth) hAppend.2⟩

/--
Completeness of canonical recursive formula expansion under explicit freshness
and block-width side conditions.  Source variables must lie below the first
auxiliary base, and every local variable used by a representation block must
fit in the reserved block width.
-/
theorem formulaViaRepresentationFrom_complete {D : Type} {Δ Γ : Language D}
    (rep : LanguageRepresentation Δ Γ) (auxBase blockWidth : Nat)
    (φ : Formula Δ) (a : Assignment D)
    (hSourceFresh :
      ∀ c ∈ φ, ∀ i : Fin (Δ.relationOf c.symbol).arity, c.vars i < auxBase)
    (hBlockBound :
      ∀ s : Δ.Symbol, ∀ d ∈ (rep.block s).constraints,
        ∀ i : Fin (Γ.relationOf d.symbol).arity, d.vars i < blockWidth)
    (hSat : Formula.Satisfies φ a) :
    ∃ b : Assignment D,
      (∀ x, x < auxBase → b x = a x) ∧
        Formula.Satisfies (formulaViaRepresentationFrom rep auxBase blockWidth φ) b := by
  induction φ generalizing auxBase a with
  | nil =>
      refine ⟨a, ?_, ?_⟩
      · intro x hx
        rfl
      · simp [formulaViaRepresentationFrom]
  | cons c φ ih =>
      have hSatCons := (Formula.satisfies_cons c φ a).1 hSat
      have hFreshHead :
          ∀ i : Fin (Δ.relationOf c.symbol).arity, c.vars i < auxBase := by
        intro i
        exact hSourceFresh c (by simp) i
      rcases constraintViaRepresentationAt_complete rep c auxBase a hFreshHead hSatCons.1 with
        ⟨bHead, hbHeadBase, hbHeadBlock⟩
      have hTailSat : Formula.Satisfies φ bHead := by
        refine Formula.satisfies_of_eq_on_vars φ ?_ hSatCons.2
        intro d hd i
        exact hbHeadBase (d.vars i) (hSourceFresh d (List.mem_cons_of_mem c hd) i)
      have hTailFresh :
          ∀ d ∈ φ, ∀ i : Fin (Δ.relationOf d.symbol).arity,
            d.vars i < auxBase + blockWidth := by
        intro d hd i
        have hBelowBase : d.vars i < auxBase :=
          hSourceFresh d (List.mem_cons_of_mem c hd) i
        omega
      rcases ih (auxBase := auxBase + blockWidth) (a := bHead) hTailFresh hTailSat with
        ⟨b, hbBelowTailBase, hbTail⟩
      have hMappedBelowTailBase :
          ∀ d ∈ (rep.block c.symbol).constraints,
            ∀ i : Fin (Γ.relationOf d.symbol).arity,
              representationBlockVarMap c auxBase (d.vars i) < auxBase + blockWidth := by
        intro d hd i
        by_cases hx : d.vars i < (Δ.relationOf c.symbol).arity
        · have hFree : c.vars ⟨d.vars i, hx⟩ < auxBase := hFreshHead ⟨d.vars i, hx⟩
          simp [representationBlockVarMap, hx]
          omega
        · have hLocal : d.vars i < blockWidth := hBlockBound c.symbol d hd i
          simp [representationBlockVarMap, hx]
          omega
      have hbBlock : Formula.Satisfies (constraintViaRepresentationAt rep c auxBase) b := by
        have hBlockLocal :
            Formula.Satisfies (rep.block c.symbol).constraints
              (fun x => bHead (representationBlockVarMap c auxBase x)) := by
          simpa [constraintViaRepresentationAt] using hbHeadBlock
        have hBlockLocal' :
            Formula.Satisfies (rep.block c.symbol).constraints
              (fun x => b (representationBlockVarMap c auxBase x)) := by
          refine Formula.satisfies_of_eq_on_vars (rep.block c.symbol).constraints ?_
            hBlockLocal
          intro d hd i
          exact hbBelowTailBase
            (representationBlockVarMap c auxBase (d.vars i))
            (hMappedBelowTailBase d hd i)
        exact (Formula.mapVars_satisfies_iff
          (representationBlockVarMap c auxBase)
          (rep.block c.symbol).constraints b).2 hBlockLocal'
      refine ⟨b, ?_, ?_⟩
      · intro x hx
        have hxTail : x < auxBase + blockWidth := by omega
        exact (hbBelowTailBase x hxTail).trans (hbHeadBase x hx)
      · have hAppend :
            Formula.Satisfies (constraintViaRepresentationAt rep c auxBase) b ∧
              Formula.Satisfies
                (formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ) b :=
          ⟨hbBlock, hbTail⟩
        simpa [formulaViaRepresentationFrom] using hAppend

/--
Proof-bearing reduction certificate for finite-domain pp-definition expansion.
The canonical expansion map is available above; as in the Boolean library, the
global completeness/cost proof is carried by the concrete application.
-/
structure RepresentationReductionCertificate {D : Type} (Δ Γ : Language D) where
  representation : LanguageRepresentation Δ Γ
  mapFormula : Formula Δ → Formula Γ
  mapFormula_satisfiable_iff :
    ∀ φ : Formula Δ, Formula.Satisfiable (mapFormula φ) ↔ Formula.Satisfiable φ
  reduction :
    KarpReductionM CostedPolyTimeModel (cspDecisionProblem Δ) (cspDecisionProblem Γ)

end PPDef
end FiniteDomain
end CSP
end ComplexityReduction
