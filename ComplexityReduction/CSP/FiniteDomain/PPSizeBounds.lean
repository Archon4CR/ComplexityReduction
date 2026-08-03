/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.CSP.FiniteDomain.PPBounds

/-!
Size bounds for finite-domain pp-definition expansion.

`PPBounds` provides the automatic freshness and block-width choices used by the
semantic pp-expansion theorem.  This module adds conservative syntactic bounds
that route descriptors can cite when a generated reduction needs reusable
length/size metadata.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain

namespace Formula

/-- Maximum syntactic size of a constraint appearing in a formula. -/
def maxConstraintSize {D : Type} {Γ : Language D} : Formula Γ → Nat
  | [] => 0
  | c :: φ => max (Constraint.size c) (maxConstraintSize φ)

@[simp]
theorem maxConstraintSize_nil {D : Type} {Γ : Language D} :
    maxConstraintSize ([] : Formula Γ) = 0 :=
  rfl

@[simp]
theorem maxConstraintSize_cons {D : Type} {Γ : Language D}
    (c : Constraint Γ) (φ : Formula Γ) :
    maxConstraintSize (c :: φ) = max (Constraint.size c) (maxConstraintSize φ) :=
  rfl

/-- Every constraint in a formula is bounded by the formula's maximum constraint size. -/
theorem constraint_size_le_maxConstraintSize_of_mem {D : Type} {Γ : Language D}
    {φ : Formula Γ} {c : Constraint Γ} (hc : c ∈ φ) :
    Constraint.size c ≤ maxConstraintSize φ := by
  induction φ with
  | nil =>
      simp at hc
  | cons d φ ih =>
      rcases List.mem_cons.mp hc with rfl | hcTail
      · simp
      · exact le_trans (ih hcTail) (Nat.le_max_right _ _)

/-- Formula size is at most length times maximum constraint size. -/
theorem size_le_length_mul_maxConstraintSize {D : Type} {Γ : Language D}
    (φ : Formula Γ) :
    Formula.size φ ≤ φ.length * maxConstraintSize φ := by
  induction φ with
  | nil =>
      simp [Formula.size]
  | cons c φ ih =>
      have hTail :
          Formula.size φ ≤ φ.length * max (Constraint.size c) (maxConstraintSize φ) :=
        le_trans ih (Nat.mul_le_mul_left φ.length (Nat.le_max_right _ _))
      calc
        Formula.size (c :: φ)
            = Constraint.size c + Formula.size φ := by
              simp [Formula.size]
        _ ≤ max (Constraint.size c) (maxConstraintSize φ) +
              φ.length * max (Constraint.size c) (maxConstraintSize φ) :=
              Nat.add_le_add (Nat.le_max_left _ _) hTail
        _ = (c :: φ).length * maxConstraintSize (c :: φ) := by
              change
                max (Constraint.size c) (maxConstraintSize φ) +
                    φ.length * max (Constraint.size c) (maxConstraintSize φ) =
                  Nat.succ φ.length * max (Constraint.size c) (maxConstraintSize φ)
              rw [Nat.succ_mul]
              exact Nat.add_comm _ _

end Formula

namespace PPDef

/-- Finite table of all accepting tuples of a relation over a finite domain. -/
noncomputable def relationTable {D : Type} [Fintype D] [DecidableEq D]
    (R : Rel D) : List (Tuple D R.arity) := by
  classical
  exact (Finset.univ.filter fun t : Tuple D R.arity => R.Holds t).toList

/-- The finite relation table contains exactly the accepting tuples. -/
theorem relationTable_complete {D : Type} [Fintype D] [DecidableEq D]
    (R : Rel D) (t : Tuple D R.arity) :
    t ∈ relationTable R ↔ R.Holds t := by
  classical
  simp [relationTable]

/--
Recursive pp expansion increases formula length by at most the number of source
constraints times the largest representation block length.
-/
theorem formulaViaRepresentationFrom_length_le_maxBlockConstraints {D : Type}
    {Δ Γ : Language D} (rep : LanguageRepresentation Δ Γ)
    (auxBase blockWidth : Nat) (φ : Formula Δ) :
    (formulaViaRepresentationFrom rep auxBase blockWidth φ).length ≤
      φ.length * rep.maxBlockConstraints := by
  induction φ generalizing auxBase with
  | nil =>
      simp [formulaViaRepresentationFrom]
  | cons c φ ih =>
      have hBlock := rep.block_constraints_length_le_maxBlockConstraints c.symbol
      have hTail := ih (auxBase := auxBase + blockWidth)
      calc
        (formulaViaRepresentationFrom rep auxBase blockWidth (c :: φ)).length
            =
              (constraintViaRepresentationAt rep c auxBase).length +
                (formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ).length := by
              simp [formulaViaRepresentationFrom]
        _ =
              (rep.block c.symbol).constraints.length +
                (formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ).length := by
              simp [constraintViaRepresentationAt, Formula.mapVars]
        _ ≤ rep.maxBlockConstraints + φ.length * rep.maxBlockConstraints :=
              Nat.add_le_add hBlock hTail
        _ = (c :: φ).length * rep.maxBlockConstraints := by
              change
                rep.maxBlockConstraints + φ.length * rep.maxBlockConstraints =
                  Nat.succ φ.length * rep.maxBlockConstraints
              rw [Nat.succ_mul]
              exact Nat.add_comm _ _

/-- Automatically bounded pp expansion has linear output length in the source formula length. -/
theorem formulaViaRepresentation_length_le {D : Type} {Δ Γ : Language D}
    (rep : LanguageRepresentation Δ Γ) (φ : Formula Δ) :
    (formulaViaRepresentation rep φ).length ≤ φ.length * rep.maxBlockConstraints := by
  simpa [formulaViaRepresentation] using
    formulaViaRepresentationFrom_length_le_maxBlockConstraints rep
      (FiniteSupport.formulaVarBound φ) rep.auxBlockWidth φ

/--
Conservative syntactic size bound for automatically bounded pp expansion.

The first factor is the linear pp-expansion length bound; the second records the
largest syntactic constraint size in the expanded formula.
-/
theorem formulaViaRepresentation_size_le {D : Type} {Δ Γ : Language D}
    (rep : LanguageRepresentation Δ Γ) (φ : Formula Δ) :
    Formula.size (formulaViaRepresentation rep φ) ≤
      (φ.length * rep.maxBlockConstraints) *
        Formula.maxConstraintSize (formulaViaRepresentation rep φ) := by
  exact le_trans (Formula.size_le_length_mul_maxConstraintSize (formulaViaRepresentation rep φ))
    (Nat.mul_le_mul_right
      (Formula.maxConstraintSize (formulaViaRepresentation rep φ))
      (formulaViaRepresentation_length_le rep φ))

/-- Length bound for one-symbol pp-derived language expansion. -/
theorem formulaViaSingleDerivedRepresentation_length_le {D : Type} [Inhabited D]
    (Γ : Language D) {arity : Nat} (block : RelationFormula Γ arity)
    (φ : Formula (singleDerivedLanguage Γ block)) :
    (formulaViaSingleDerivedRepresentation Γ block φ).length ≤
      φ.length * (singleDerivedRepresentation Γ block).maxBlockConstraints := by
  simpa [formulaViaSingleDerivedRepresentation] using
    formulaViaRepresentation_length_le (singleDerivedRepresentation Γ block) φ

/-- Size bound for one-symbol pp-derived language expansion. -/
theorem formulaViaSingleDerivedRepresentation_size_le {D : Type} [Inhabited D]
    (Γ : Language D) {arity : Nat} (block : RelationFormula Γ arity)
    (φ : Formula (singleDerivedLanguage Γ block)) :
    Formula.size (formulaViaSingleDerivedRepresentation Γ block φ) ≤
      (φ.length * (singleDerivedRepresentation Γ block).maxBlockConstraints) *
        Formula.maxConstraintSize (formulaViaSingleDerivedRepresentation Γ block φ) := by
  simpa [formulaViaSingleDerivedRepresentation] using
    formulaViaRepresentation_size_le (singleDerivedRepresentation Γ block) φ

/-- Length bound for finite-family pp-derived language expansion. -/
theorem formulaViaDerivedFamilyRepresentation_length_le {D : Type} [Inhabited D]
    (Γ : Language D) {NewSym : Type} [Fintype NewSym]
    (arityOf : NewSym → Nat)
    (block : ∀ s : NewSym, RelationFormula Γ (arityOf s))
    (φ : Formula (derivedFamilyLanguage Γ arityOf block)) :
    (formulaViaDerivedFamilyRepresentation Γ arityOf block φ).length ≤
      φ.length * (derivedFamilyRepresentation Γ arityOf block).maxBlockConstraints := by
  simpa [formulaViaDerivedFamilyRepresentation] using
    formulaViaRepresentation_length_le (derivedFamilyRepresentation Γ arityOf block) φ

/--
If every base and derived pp block has local variables below `bound`, then the
canonical derived-family auxiliary block width is also below `bound`.
-/
theorem derivedFamilyRepresentation_auxBlockWidth_le {D : Type} [Inhabited D]
    (Γ : Language D) {NewSym : Type} [Fintype NewSym]
    (arityOf : NewSym → Nat)
    (block : ∀ s : NewSym, RelationFormula Γ (arityOf s))
    {bound : Nat}
    (hBase : ∀ s : Γ.Symbol, (atomicRelationFormula Γ s).varBound ≤ bound)
    (hDerived : ∀ s : NewSym, (block s).varBound ≤ bound) :
    (derivedFamilyRepresentation Γ arityOf block).auxBlockWidth ≤ bound := by
  classical
  unfold LanguageRepresentation.auxBlockWidth
  refine Finset.sup_le ?_
  intro s _hs
  cases s with
  | inl base =>
      simpa [LanguageRepresentation.blockVarBound, derivedFamilyRepresentation] using hBase base
  | inr derived =>
      simpa [LanguageRepresentation.blockVarBound, derivedFamilyRepresentation] using
        hDerived derived

/-- Size bound for finite-family pp-derived language expansion. -/
theorem formulaViaDerivedFamilyRepresentation_size_le {D : Type} [Inhabited D]
    (Γ : Language D) {NewSym : Type} [Fintype NewSym]
    (arityOf : NewSym → Nat)
    (block : ∀ s : NewSym, RelationFormula Γ (arityOf s))
    (φ : Formula (derivedFamilyLanguage Γ arityOf block)) :
    Formula.size (formulaViaDerivedFamilyRepresentation Γ arityOf block φ) ≤
      (φ.length * (derivedFamilyRepresentation Γ arityOf block).maxBlockConstraints) *
        Formula.maxConstraintSize (formulaViaDerivedFamilyRepresentation Γ arityOf block φ) := by
  simpa [formulaViaDerivedFamilyRepresentation] using
    formulaViaRepresentation_size_le (derivedFamilyRepresentation Γ arityOf block) φ

end PPDef
end FiniteDomain
end CSP
end ComplexityReduction
