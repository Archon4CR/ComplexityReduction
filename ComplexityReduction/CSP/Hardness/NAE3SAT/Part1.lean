/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Examples.NAE3SAT
import ComplexityReduction.SAT.CNFTo3SATCosted

/-!
Ordinary NAE-3SAT reverse gadget.

This file eliminates the pinning and literal-polarity conveniences used by
`NAE3SATPinned`: the target language is the ordinary singleton NAE-3SAT
language from `ComplexityReduction.CSP.Examples.NAE3SAT`.
-/

namespace ComplexityReduction
namespace CSP
namespace Hardness
namespace NAE3SAT

open SAT

/-- Ordinary NAE-3SAT constraint over three variables. -/
def naeConstraint (x y z : Nat) : Constraint Examples.notAllEqual3Language where
  symbol := Examples.NAE3Symbol.rel
  vars := fun i =>
    match i.val with
    | 0 => x
    | 1 => y
    | _ => z

theorem bool_not_ne_of_ne {x y : Bool} (h : x ≠ y) : (!x) ≠ (!y) := by
  cases x <;> cases y <;> simp_all

theorem naeConstraint_satisfies_iff (x y z : Nat) (a : Assignment) :
    Constraint.Satisfies (naeConstraint x y z) a ↔ a x ≠ a y ∨ a x ≠ a z := by
  change Examples.notAllEqual3Rel.Holds (fun i : Fin Examples.notAllEqual3Rel.arity =>
      a (match i.val with | 0 => x | 1 => y | _ => z)) ↔ a x ≠ a y ∨ a x ≠ a z
  unfold Examples.notAllEqual3Rel StandardRelations.notAllEqual3Rel
    StandardRelations.notAllEqualRel
  rw [BoolRel.holds_ofPredicate_iff]
  constructor
  · rintro ⟨i, j, hij⟩
    fin_cases i <;> fin_cases j <;>
      cases hx : a x <;> cases hy : a y <;> cases hz : a z <;> simp_all
  · intro h
    rcases h with hxy | hxz
    · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by simpa using hxy⟩
    · exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by simpa using hxz⟩

theorem notAllEqual3Rel_complement_iff (t : BoolTuple 3) :
    Examples.notAllEqual3Rel.Holds (fun i => !(t i)) ↔
      Examples.notAllEqual3Rel.Holds t := by
  unfold Examples.notAllEqual3Rel StandardRelations.notAllEqual3Rel
    StandardRelations.notAllEqualRel
  rw [BoolRel.holds_ofPredicate_iff, BoolRel.holds_ofPredicate_iff]
  constructor
  · rintro ⟨i, j, hij⟩
    have hij' : t i ≠ t j := by
      intro hEq
      exact hij (by simp [hEq])
    exact ⟨i, j, hij'⟩
  · rintro ⟨i, j, hij⟩
    exact ⟨i, j, bool_not_ne_of_ne hij⟩

theorem naeConstraint_complement_satisfies_iff (x y z : Nat) (a : Assignment) :
    Constraint.Satisfies (naeConstraint x y z) (fun v => !(a v)) ↔
      Constraint.Satisfies (naeConstraint x y z) a := by
  exact notAllEqual3Rel_complement_iff
    (fun i : Fin 3 => a (match i.val with | 0 => x | 1 => y | _ => z))

theorem formula_complement_satisfies_iff (φ : Formula Examples.notAllEqual3Language)
    (a : Assignment) :
    Formula.Satisfies φ (fun v => !(a v)) ↔ Formula.Satisfies φ a := by
  constructor
  · intro h c hc
    rcases c with ⟨s, vars⟩
    cases s
    change Examples.notAllEqual3Rel.Holds (fun i => a (vars i))
    have hc' := h ⟨Examples.NAE3Symbol.rel, vars⟩ hc
    change Examples.notAllEqual3Rel.Holds (fun i => !(a (vars i))) at hc'
    exact (notAllEqual3Rel_complement_iff (fun i => a (vars i))).1 hc'
  · intro h c hc
    rcases c with ⟨s, vars⟩
    cases s
    change Examples.notAllEqual3Rel.Holds (fun i => !(a (vars i)))
    have hc' := h ⟨Examples.NAE3Symbol.rel, vars⟩ hc
    change Examples.notAllEqual3Rel.Holds (fun i => a (vars i)) at hc'
    exact (notAllEqual3Rel_complement_iff (fun i => a (vars i))).2 hc'

/-- First fresh variable used as the global false anchor. -/
def falseVar (φ : ThreeCNF) : Nat :=
  CNF.varBound φ.clauses

/-- Second fresh variable used as the global true anchor. -/
def trueVar (φ : ThreeCNF) : Nat :=
  falseVar φ + 1

/-- Dedicated variable representing the negation of source variable `x`. -/
def negVar (φ : ThreeCNF) (x : Nat) : Nat :=
  falseVar φ + 2 + x

/-- First local auxiliary variable for clause `i`. -/
def auxBase (φ : ThreeCNF) : Nat :=
  falseVar φ + 2 + falseVar φ

def auxVar (φ : ThreeCNF) (i : Nat) : Nat :=
  auxBase φ + 2 * i

def auxNegVar (φ : ThreeCNF) (i : Nat) : Nat :=
  auxBase φ + 2 * i + 1

/-- Anchor forcing the two global constants to be different. -/
def anchorConstraint (φ : ThreeCNF) : Constraint Examples.notAllEqual3Language :=
  naeConstraint (falseVar φ) (trueVar φ) (trueVar φ)

/-- Ordinary NAE constraints forcing `nx` to be the complement of `x`. -/
def complementPairConstraints (x nx falseVar trueVar : Nat) :
    Formula Examples.notAllEqual3Language :=
  [naeConstraint x nx falseVar, naeConstraint x nx trueVar]

def sourceComplementConstraintsAux (φ : ThreeCNF) : Nat → Formula Examples.notAllEqual3Language
  | 0 => []
  | n + 1 => complementPairConstraints n (negVar φ n) (falseVar φ) (trueVar φ) ++
      sourceComplementConstraintsAux φ n

def sourceComplementConstraints (φ : ThreeCNF) : Formula Examples.notAllEqual3Language :=
  sourceComplementConstraintsAux φ (falseVar φ)

def litVar (φ : ThreeCNF) (l : Literal) : Nat :=
  if l.neg then negVar φ l.var else l.var

theorem anchorConstraint_satisfies_iff (φ : ThreeCNF) (a : Assignment) :
    Constraint.Satisfies (anchorConstraint φ) a ↔ a (falseVar φ) ≠ a (trueVar φ) := by
  rw [anchorConstraint, naeConstraint_satisfies_iff]
  simp

theorem normalize_formula_of_anchor {φ : ThreeCNF}
    {ψ : Formula Examples.notAllEqual3Language} {a : Assignment}
    (h : Formula.Satisfies (anchorConstraint φ :: ψ) a) :
    ∃ b : Assignment, b (falseVar φ) = false ∧ b (trueVar φ) = true ∧
      Formula.Satisfies (anchorConstraint φ :: ψ) b := by
  have hAnchor : Constraint.Satisfies (anchorConstraint φ) a :=
    h _ (by simp)
  have hdiff : a (falseVar φ) ≠ a (trueVar φ) :=
    (anchorConstraint_satisfies_iff φ a).1 hAnchor
  by_cases hf : a (falseVar φ) = false
  · refine ⟨a, hf, ?_, h⟩
    · cases ht : a (trueVar φ) <;> simp_all
  · let b : Assignment := fun v => !(a v)
    have hfalse : b (falseVar φ) = false := by
      simp [b]
      cases hfv : a (falseVar φ) <;> simp_all
    have htrue : b (trueVar φ) = true := by
      simp [b]
      cases htv : a (trueVar φ) <;> cases hfv : a (falseVar φ) <;> simp_all
    refine ⟨b, hfalse, htrue, ?_⟩
    exact (formula_complement_satisfies_iff (anchorConstraint φ :: ψ) a).2 h

theorem complementPair_project {x nx f t : Nat} {a : Assignment}
    (hF : a f = false) (hT : a t = true)
    (h : Formula.Satisfies (complementPairConstraints x nx f t) a) :
    a nx = !(a x) := by
  have h₁ : Constraint.Satisfies (naeConstraint x nx f) a := by
    exact h _ (by simp [complementPairConstraints])
  have h₂ : Constraint.Satisfies (naeConstraint x nx t) a := by
    exact h _ (by simp [complementPairConstraints])
  have hnae₁ := (naeConstraint_satisfies_iff x nx f a).1 h₁
  have hnae₂ := (naeConstraint_satisfies_iff x nx t a).1 h₂
  have hnae₁' : a x ≠ a nx ∨ a x ≠ false := by simpa [hF] using hnae₁
  have hnae₂' : a x ≠ a nx ∨ a x ≠ true := by simpa [hT] using hnae₂
  cases hx : a x <;> cases hnx : a nx <;>
    simp [hx, hnx] at hnae₁' hnae₂' ⊢

theorem complementPair_extend {x nx f t : Nat} {a : Assignment}
    (hF : a f = false) (hT : a t = true) (hNX : a nx = !(a x)) :
    Formula.Satisfies (complementPairConstraints x nx f t) a := by
  intro c hc
  rcases List.mem_cons.mp hc with h₁ | htail
  · subst c
    exact (naeConstraint_satisfies_iff x nx f a).2 (by
      cases hx : a x <;> cases hnx : a nx <;> simp [hF, hx, hnx] at hNX ⊢)
  · have h₂ : c = naeConstraint x nx t := by simpa [complementPairConstraints] using htail
    subst c
    exact (naeConstraint_satisfies_iff x nx t a).2 (by
      cases hx : a x <;> cases hnx : a nx <;> simp [hT, hx, hnx] at hNX ⊢)

theorem sourceComplementConstraintsAux_project {φ : ThreeCNF} {a : Assignment}
    (hF : a (falseVar φ) = false) (hT : a (trueVar φ) = true)
    {n : Nat}
    (h : Formula.Satisfies (sourceComplementConstraintsAux φ n) a) :
    ∀ x, x < n → a (negVar φ x) = !(a x) := by
  match n with
  | 0 =>
      intro x hx
      cases hx
  | Nat.succ k =>
      have htail : Formula.Satisfies (sourceComplementConstraintsAux φ k) a := by
        intro c hc
        exact h c (by
          exact List.mem_append.mpr (Or.inr hc))
      have hhead :
          Formula.Satisfies
            (complementPairConstraints k (negVar φ k) (falseVar φ) (trueVar φ)) a := by
        intro c hc
        exact h c (by
          exact List.mem_append.mpr (Or.inl hc))
      intro x hx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hxlt | rfl
      · exact sourceComplementConstraintsAux_project hF hT htail x hxlt
      · exact complementPair_project hF hT hhead

theorem sourceComplementConstraintsAux_extend {φ : ThreeCNF} {a : Assignment}
    (hF : a (falseVar φ) = false) (hT : a (trueVar φ) = true)
    {n : Nat} (hNeg : ∀ x, x < n → a (negVar φ x) = !(a x)) :
    Formula.Satisfies (sourceComplementConstraintsAux φ n) a := by
  induction n with
  | zero =>
      intro c hc
      cases hc
  | succ n ih =>
      intro c hc
      rcases List.mem_append.mp (by simpa [sourceComplementConstraintsAux] using hc) with hhead | htail
      · exact complementPair_extend hF hT (hNeg n (Nat.lt_succ_self n)) c hhead
      · exact ih (by intro x hx; exact hNeg x (Nat.lt_trans hx (Nat.lt_succ_self n))) c htail

theorem litVar_eval_eq {φ : ThreeCNF} {a : Assignment}
    (hNeg : ∀ x, x < falseVar φ → a (negVar φ x) = !(a x))
    {l : Literal} (hl : l.var < falseVar φ) :
    a (litVar φ l) = l.eval a := by
  cases l with
  | mk v neg =>
      cases neg <;> simp [litVar, Literal.eval, hNeg v hl]

def clauseAuxValue (a : Assignment) (φ : ThreeCNF) : Clause → Bool
  | l₁ :: l₂ :: _ => !((a (litVar φ l₁)) || (a (litVar φ l₂)))
  | _ => false

def sourceClauseAuxValue (a : Assignment) : Clause → Bool
  | l₁ :: l₂ :: _ => !((l₁.eval a) || (l₂.eval a))
  | _ => false

def clauseToFormula (φ : ThreeCNF) (i : Nat) : Clause → Formula Examples.notAllEqual3Language
  | [] =>
      [naeConstraint (falseVar φ) (falseVar φ) (falseVar φ)]
  | [l₁] =>
      [naeConstraint (litVar φ l₁) (falseVar φ) (falseVar φ)]
  | [l₁, l₂] =>
      [naeConstraint (litVar φ l₁) (litVar φ l₂) (falseVar φ)]
  | l₁ :: l₂ :: l₃ :: _ =>
      complementPairConstraints (auxVar φ i) (auxNegVar φ i) (falseVar φ) (trueVar φ) ++
      [ naeConstraint (litVar φ l₁) (litVar φ l₂) (auxVar φ i)
      , naeConstraint (auxNegVar φ i) (litVar φ l₃) (falseVar φ)
      ]

def clausesToFormulaAux (φ : ThreeCNF) : Nat → CNF → Formula Examples.notAllEqual3Language
  | _, [] => []
  | i, c :: cs => clauseToFormula φ i c ++ clausesToFormulaAux φ (i + 1) cs

def threeCNFToNAE3Formula (φ : ThreeCNF) : Formula Examples.notAllEqual3Language :=
  anchorConstraint φ :: sourceComplementConstraints φ ++ clausesToFormulaAux φ 0 φ.clauses

theorem naeUnit_project (x : Bool) :
    (x ≠ false ∨ x ≠ false) → x = true := by
  cases x <;> simp

theorem naeBinary_project (x y : Bool) :
    (x ≠ y ∨ x ≠ false) → x = true ∨ y = true := by
  cases x <;> cases y <;> simp

theorem naeTernary_project (x y z aux : Bool) :
    (x ≠ y ∨ x ≠ aux) → (!aux ≠ z ∨ !aux ≠ false) →
      x = true ∨ y = true ∨ z = true := by
  cases x <;> cases y <;> cases z <;> cases aux <;> simp

theorem naeUnit_extend (x : Bool) :
    x = true → x ≠ false ∨ x ≠ false := by
  cases x <;> simp

theorem naeBinary_extend (x y : Bool) :
    x = true ∨ y = true → x ≠ y ∨ x ≠ false := by
  cases x <;> cases y <;> simp

theorem naeTernary_first_extend (x y : Bool) :
    x ≠ y ∨ x ≠ !((x || y)) := by
  cases x <;> cases y <;> simp

theorem naeTernary_second_extend (x y z : Bool) :
    x = true ∨ y = true ∨ z = true →
      !(!((x || y))) ≠ z ∨ !(!((x || y))) ≠ false := by
  cases x <;> cases y <;> cases z <;> simp

theorem naeTernary_second_extend' (x y z : Bool) :
    x = true ∨ y = true ∨ z = true →
      !(x || y) = z ∨ (x = false → y = true) := by
  cases x <;> cases y <;> cases z <;> simp

theorem clauseToFormula_project {φ : ThreeCNF} {c : Clause} (hlen : c.length ≤ 3)
    {i : Nat} {a : Assignment}
    (hF : a (falseVar φ) = false)
    (hT : a (trueVar φ) = true)
    (hLit : ∀ l ∈ c, a (litVar φ l) = l.eval a)
    (h : Formula.Satisfies (clauseToFormula φ i c) a) :
    Clause.Satisfies c a := by
  cases c with
  | nil =>
      have hc :
          Constraint.Satisfies
            (naeConstraint (falseVar φ) (falseVar φ) (falseVar φ)) a := by
        exact h _ (by simp [clauseToFormula])
      have hnae := (naeConstraint_satisfies_iff (falseVar φ) (falseVar φ) (falseVar φ) a).1 hc
      simp [hF] at hnae
  | cons l₁ rest =>
      cases rest with
      | nil =>
          have hc :
              Constraint.Satisfies
                (naeConstraint (litVar φ l₁) (falseVar φ) (falseVar φ)) a := by
            exact h _ (by simp [clauseToFormula])
          have hnae := (naeConstraint_satisfies_iff (litVar φ l₁)
            (falseVar φ) (falseVar φ) a).1 hc
          have hl : l₁.eval a = true := by
            have hLit₁ := hLit l₁ (by simp)
            exact by
              have hnae' : a (litVar φ l₁) ≠ false ∨ a (litVar φ l₁) ≠ false := by
                simpa [hF] using hnae
              simpa [hLit₁] using naeUnit_project (a (litVar φ l₁)) hnae'
          exact ⟨l₁, by simp, hl⟩
      | cons l₂ rest₂ =>
          cases rest₂ with
          | nil =>
              have hc :
                  Constraint.Satisfies
                    (naeConstraint (litVar φ l₁) (litVar φ l₂) (falseVar φ)) a := by
                exact h _ (by simp [clauseToFormula])
              have hnae := (naeConstraint_satisfies_iff (litVar φ l₁)
                (litVar φ l₂) (falseVar φ) a).1 hc
              have hLit₁ := hLit l₁ (by simp)
              have hLit₂ := hLit l₂ (by simp)
              rcases naeBinary_project (a (litVar φ l₁)) (a (litVar φ l₂))
                (by simpa [hF] using hnae) with h₁ | h₂
              · exact ⟨l₁, by simp, by simpa [hLit₁] using h₁⟩
              · exact ⟨l₂, by simp, by simpa [hLit₂] using h₂⟩
          | cons l₃ rest₃ =>
              cases rest₃ with
              | nil =>
                  have hfirst :
                      Constraint.Satisfies
                        (naeConstraint (litVar φ l₁) (litVar φ l₂) (auxVar φ i)) a := by
                    exact h _ (by
                      simp [clauseToFormula, complementPairConstraints])
                  have hsecond :
                      Constraint.Satisfies
                        (naeConstraint (auxNegVar φ i) (litVar φ l₃) (falseVar φ)) a := by
                    exact h _ (by
                      simp [clauseToFormula, complementPairConstraints])
                  have hpair :
                      Formula.Satisfies
                        (complementPairConstraints (auxVar φ i) (auxNegVar φ i)
                          (falseVar φ) (trueVar φ)) a := by
                    intro d hd
                    exact h d (by simp [clauseToFormula, hd])
                  have hAuxNeg : a (auxNegVar φ i) = !(a (auxVar φ i)) := by
                    exact complementPair_project hF hT hpair
                  have hnae₁ := (naeConstraint_satisfies_iff (litVar φ l₁)
                    (litVar φ l₂) (auxVar φ i) a).1 hfirst
                  have hnae₂ := (naeConstraint_satisfies_iff (auxNegVar φ i)
                    (litVar φ l₃) (falseVar φ) a).1 hsecond
                  have hLit₁ := hLit l₁ (by simp)
                  have hLit₂ := hLit l₂ (by simp)
                  have hLit₃ := hLit l₃ (by simp)
                  rcases naeTernary_project (a (litVar φ l₁)) (a (litVar φ l₂))
                    (a (litVar φ l₃)) (a (auxVar φ i))
                    (by simpa using hnae₁)
                    (by simpa [hAuxNeg, hF] using hnae₂) with h₁ | h₂ | h₃
                  · exact ⟨l₁, by simp, by simpa [hLit₁] using h₁⟩
                  · exact ⟨l₂, by simp, by simpa [hLit₂] using h₂⟩
                  · exact ⟨l₃, by simp, by simpa [hLit₃] using h₃⟩
              | cons _ _ =>
                  simp at hlen

theorem clauseToFormula_extend {φ : ThreeCNF} {c : Clause} (hlen : c.length ≤ 3)
    {i : Nat} {a b : Assignment}
    (hF : b (falseVar φ) = false)
    (hT : b (trueVar φ) = true)
    (hAux : b (auxVar φ i) = sourceClauseAuxValue a c)
    (hAuxNeg : b (auxNegVar φ i) = !(b (auxVar φ i)))
    (hLit : ∀ l ∈ c, b (litVar φ l) = l.eval a)
    (hSat : Clause.Satisfies c a) :
    Formula.Satisfies (clauseToFormula φ i c) b := by
  cases c with
  | nil =>
      rcases hSat with ⟨l, hl, _⟩
      cases hl
  | cons l₁ rest =>
      cases rest with
      | nil =>
          intro d hd
          have hdEq :
              d = naeConstraint (litVar φ l₁) (falseVar φ) (falseVar φ) := by
            simpa [clauseToFormula] using hd
          subst d
          rcases hSat with ⟨l, hl, hlEval⟩
          have hl₁ : l = l₁ := by simpa using hl
          subst l
          exact (naeConstraint_satisfies_iff (litVar φ l₁) (falseVar φ) (falseVar φ) b).2
            (by
              have hLit₁ := hLit l₁ (by simp)
              simpa [hF, hLit₁] using naeUnit_extend (b (litVar φ l₁)) (by
                simpa [hLit₁] using hlEval))
      | cons l₂ rest₂ =>
          cases rest₂ with
          | nil =>
              intro d hd
              have hdEq :
                  d = naeConstraint (litVar φ l₁) (litVar φ l₂) (falseVar φ) := by
                simpa [clauseToFormula] using hd
              subst d
              have hLit₁ := hLit l₁ (by simp)
              have hLit₂ := hLit l₂ (by simp)
              exact (naeConstraint_satisfies_iff (litVar φ l₁) (litVar φ l₂)
                (falseVar φ) b).2 (by
                  simpa [hF] using
                    naeBinary_extend (b (litVar φ l₁)) (b (litVar φ l₂)) (by
                      rcases hSat with ⟨l, hl, hlEval⟩
                      rcases List.mem_cons.mp hl with h₁ | htail
                      · subst l
                        exact Or.inl (by simpa [hLit₁] using hlEval)
                      · have h₂ : l = l₂ := by simpa using htail
                        subst l
                        exact Or.inr (by simpa [hLit₂] using hlEval)))
          | cons l₃ rest₃ =>
              cases rest₃ with
              | nil =>
                  intro d hd
                  have hLit₁ := hLit l₁ (by simp)
                  have hLit₂ := hLit l₂ (by simp)
                  have hLit₃ := hLit l₃ (by simp)
                  have hdCases :
                      d = naeConstraint (auxVar φ i) (auxNegVar φ i) (falseVar φ) ∨
                        d = naeConstraint (auxVar φ i) (auxNegVar φ i) (trueVar φ) ∨
                        d = naeConstraint (litVar φ l₁) (litVar φ l₂) (auxVar φ i) ∨
                        d = naeConstraint (auxNegVar φ i) (litVar φ l₃) (falseVar φ) := by
                    simpa [clauseToFormula, complementPairConstraints] using hd
                  rcases hdCases with hpairF | hpairT | hfirst | hsecond
                  · subst d
                    exact (naeConstraint_satisfies_iff (auxVar φ i) (auxNegVar φ i)
                      (falseVar φ) b).2 (by
                        cases haux : b (auxVar φ i) <;>
                          cases hauxN : b (auxNegVar φ i) <;>
                          simp [hF, haux, hauxN] at hAuxNeg ⊢)
                  · subst d
                    exact (naeConstraint_satisfies_iff (auxVar φ i) (auxNegVar φ i)
                      (trueVar φ) b).2 (by
                        cases haux : b (auxVar φ i) <;>
                          cases hauxN : b (auxNegVar φ i) <;>
                          simp [hT, haux, hauxN] at hAuxNeg ⊢)
                  · subst d
                    exact (naeConstraint_satisfies_iff (litVar φ l₁) (litVar φ l₂)
                      (auxVar φ i) b).2 (by
                        simpa [hAux, sourceClauseAuxValue, hLit₁, hLit₂] using
                          naeTernary_first_extend (b (litVar φ l₁)) (b (litVar φ l₂)))
                  · subst d
                    exact (naeConstraint_satisfies_iff (auxNegVar φ i) (litVar φ l₃)
                      (falseVar φ) b).2 (by
                        have hSatBool :
                            l₁.eval a = true ∨ l₂.eval a = true ∨ l₃.eval a = true := by
                          rcases hSat with ⟨l, hl, hlEval⟩
                          rcases List.mem_cons.mp hl with hmem₁ | hmem
                          · subst l
                            exact Or.inl hlEval
                          · rcases List.mem_cons.mp hmem with hmem₂ | hmem₃
                            · subst l
                              exact Or.inr (Or.inl hlEval)
                            · have hmem₃' : l = l₃ := by simpa using hmem₃
                              subst l
                              exact Or.inr (Or.inr hlEval)
                        have hSatBoolB :
                            b (litVar φ l₁) = true ∨ b (litVar φ l₂) = true ∨
                              b (litVar φ l₃) = true := by
                          rcases hSatBool with h₁ | h₂ | h₃
                          · exact Or.inl (by simpa [hLit₁] using h₁)
                          · exact Or.inr (Or.inl (by simpa [hLit₂] using h₂))
                          · exact Or.inr (Or.inr (by simpa [hLit₃] using h₃))
                        simpa [hAuxNeg, hAux, hF, sourceClauseAuxValue, hLit₁, hLit₂,
                          hLit₃] using
                          naeTernary_second_extend' (b (litVar φ l₁)) (b (litVar φ l₂))
                            (b (litVar φ l₃)) hSatBoolB)
              | cons _ _ =>
                  simp at hlen

theorem clausesToFormulaAux_project {φ : ThreeCNF} {clauses : CNF} {i : Nat}
    {a : Assignment}
    (hThree : CNF.IsThreeCNF clauses)
    (hVars : ∀ c ∈ clauses, ∀ l ∈ c, l.var < falseVar φ)
    (hF : a (falseVar φ) = false)
    (hT : a (trueVar φ) = true)
    (hNeg : ∀ x, x < falseVar φ → a (negVar φ x) = !(a x))
    (h : Formula.Satisfies (clausesToFormulaAux φ i clauses) a) :
    CNF.Satisfies clauses a := by
  induction clauses generalizing i with
  | nil =>
      intro c hc
      cases hc
  | cons head tail ih =>
      intro d hd
      have hcLen : head.length ≤ 3 := hThree head (by simp)
      have hcsThree : CNF.IsThreeCNF tail := by
        intro e he
        exact hThree e (by simp [he])
      have hcsVars : ∀ e ∈ tail, ∀ l ∈ e, l.var < falseVar φ := by
        intro e he l hl
        exact hVars e (by simp [he]) l hl
      have hBlock : Formula.Satisfies (clauseToFormula φ i head) a := by
        intro e he
        exact h e (by simp [clausesToFormulaAux, he])
      have hTail : Formula.Satisfies (clausesToFormulaAux φ (i + 1) tail) a := by
        intro e he
        exact h e (by simp [clausesToFormulaAux, he])
      rcases List.mem_cons.mp hd with rfl | hds
      · exact clauseToFormula_project hcLen hF hT
          (by
            intro l hl
            exact litVar_eval_eq hNeg (hVars d (by simp) l hl))
          hBlock
      · exact ih (i := i + 1) hcsThree hcsVars hTail d hds

theorem threeCNFToNAE3Formula_project (φ : ThreeCNF) :
    Formula.Satisfiable (threeCNFToNAE3Formula φ) → φ.Satisfiable := by
  rintro ⟨a, hSat⟩
  have hNorm := normalize_formula_of_anchor
    (φ := φ)
    (ψ := sourceComplementConstraints φ ++ clausesToFormulaAux φ 0 φ.clauses)
    (a := a)
    (by simpa [threeCNFToNAE3Formula] using hSat)
  rcases hNorm with ⟨b, hF, hT, hSatB⟩
  have hTail :
      Formula.Satisfies
        (sourceComplementConstraints φ ++ clausesToFormulaAux φ 0 φ.clauses) b := by
    intro c hc
    exact hSatB c (by simp [hc])
  have hSource :
      Formula.Satisfies (sourceComplementConstraints φ) b :=
    ((Formula.satisfies_append (sourceComplementConstraints φ)
      (clausesToFormulaAux φ 0 φ.clauses) b).1 hTail).1
  have hClauses :
      Formula.Satisfies (clausesToFormulaAux φ 0 φ.clauses) b :=
    ((Formula.satisfies_append (sourceComplementConstraints φ)
      (clausesToFormulaAux φ 0 φ.clauses) b).1 hTail).2
  have hNeg : ∀ x, x < falseVar φ → b (negVar φ x) = !(b x) :=
    sourceComplementConstraintsAux_project hF hT hSource
  have hVars : ∀ c ∈ φ.clauses, ∀ l ∈ c, l.var < falseVar φ := by
    intro c hc
    exact CNF.clause_vars_lt_varBound hc
  exact ⟨b, clausesToFormulaAux_project φ.isThree hVars hF hT hNeg hClauses⟩

def AuxValues : ThreeCNF → Nat → CNF → Assignment → Assignment → Prop
  | _, _, [], _, _ => True
  | φ, i, c :: cs, source, target =>
      target (auxVar φ i) = sourceClauseAuxValue source c ∧
        target (auxNegVar φ i) = !(target (auxVar φ i)) ∧
          AuxValues φ (i + 1) cs source target

theorem clausesToFormulaAux_extend_of_auxValues {φ : ThreeCNF} {clauses : CNF}
    {i : Nat} {a b : Assignment}
    (hThree : CNF.IsThreeCNF clauses)
    (hF : b (falseVar φ) = false)
    (hT : b (trueVar φ) = true)
    (hLit : ∀ c ∈ clauses, ∀ l ∈ c, b (litVar φ l) = l.eval a)
    (hAux : AuxValues φ i clauses a b)
    (hSat : CNF.Satisfies clauses a) :
    Formula.Satisfies (clausesToFormulaAux φ i clauses) b := by
  induction clauses generalizing i with
  | nil =>
      intro c hc
      cases hc
  | cons head tail ih =>
      have hHeadLen : head.length ≤ 3 := hThree head (by simp)
      have hTailThree : CNF.IsThreeCNF tail := by
        intro c hc
        exact hThree c (by simp [hc])
      have hHeadAux : b (auxVar φ i) = sourceClauseAuxValue a head := hAux.1
      have hHeadAuxNeg : b (auxNegVar φ i) = !(b (auxVar φ i)) := hAux.2.1
      have hTailAux : AuxValues φ (i + 1) tail a b := hAux.2.2
      have hHeadSat : Formula.Satisfies (clauseToFormula φ i head) b :=
        clauseToFormula_extend hHeadLen hF hT hHeadAux hHeadAuxNeg
          (by intro l hl; exact hLit head (by simp) l hl)
          (hSat head (by simp))
      have hTailSat : Formula.Satisfies (clausesToFormulaAux φ (i + 1) tail) b :=
        ih (i := i + 1) hTailThree
          (by
            intro c hc l hl
            exact hLit c (by simp [hc]) l hl)
          hTailAux
          (by
            intro c hc
            exact hSat c (by simp [hc]))
      intro c hc
      rcases List.mem_append.mp (by simpa [clausesToFormulaAux] using hc) with hleft | hright
      · exact hHeadSat c hleft
      · exact hTailSat c hright

noncomputable def extendBaseAssignment (φ : ThreeCNF) (a : Assignment) : Assignment :=
  fun v =>
    if v = falseVar φ then false
    else if v = trueVar φ then true
    else if h : ∃ x, x < falseVar φ ∧ v = negVar φ x then
      !(a h.choose)
    else a v

def setClauseAux (φ : ThreeCNF) (i : Nat) (c : Clause)
    (source target : Assignment) : Assignment :=
  SAT.Clause.setVar
    (SAT.Clause.setVar target (auxVar φ i) (sourceClauseAuxValue source c))
    (auxNegVar φ i) (!(sourceClauseAuxValue source c))

def extendAssignmentAux (φ : ThreeCNF) : Nat → CNF → Assignment → Assignment → Assignment
  | _, [], _, base => base
  | i, c :: cs, source, base =>
      setClauseAux φ i c source (extendAssignmentAux φ (i + 1) cs source base)

noncomputable def extendAssignment (φ : ThreeCNF) (a : Assignment) : Assignment :=
  extendAssignmentAux φ 0 φ.clauses a (extendBaseAssignment φ a)

theorem negVar_ne_falseVar {φ : ThreeCNF} {x : Nat} :
    negVar φ x ≠ falseVar φ := by
  unfold negVar
  omega

theorem negVar_ne_trueVar {φ : ThreeCNF} {x : Nat} :
    negVar φ x ≠ trueVar φ := by
  unfold negVar trueVar
  omega

theorem negVar_injective {φ : ThreeCNF} {x y : Nat}
    (h : negVar φ x = negVar φ y) : x = y := by
  unfold negVar at h
  omega

theorem auxVar_ne_falseVar {φ : ThreeCNF} {i : Nat} :
    auxVar φ i ≠ falseVar φ := by
  unfold auxVar auxBase
  omega

theorem auxNegVar_ne_falseVar {φ : ThreeCNF} {i : Nat} :
    auxNegVar φ i ≠ falseVar φ := by
  unfold auxNegVar auxBase
  omega

theorem auxVar_ne_trueVar {φ : ThreeCNF} {i : Nat} :
    auxVar φ i ≠ trueVar φ := by
  unfold auxVar auxBase trueVar
  omega

theorem auxNegVar_ne_trueVar {φ : ThreeCNF} {i : Nat} :
    auxNegVar φ i ≠ trueVar φ := by
  unfold auxNegVar auxBase trueVar
  omega

theorem auxVar_ne_sourceVar {φ : ThreeCNF} {i x : Nat} (hx : x < falseVar φ) :
    auxVar φ i ≠ x := by
  unfold auxVar auxBase
  omega

theorem auxNegVar_ne_sourceVar {φ : ThreeCNF} {i x : Nat} (hx : x < falseVar φ) :
    auxNegVar φ i ≠ x := by
  unfold auxNegVar auxBase
  omega

theorem auxVar_ne_negVar {φ : ThreeCNF} {i x : Nat} (hx : x < falseVar φ) :
    auxVar φ i ≠ negVar φ x := by
  unfold auxVar auxBase negVar
  omega

theorem auxNegVar_ne_negVar {φ : ThreeCNF} {i x : Nat} (hx : x < falseVar φ) :
    auxNegVar φ i ≠ negVar φ x := by
  unfold auxNegVar auxBase negVar
  omega

theorem auxNegVar_ne_auxVar_self {φ : ThreeCNF} {i : Nat} :
    auxNegVar φ i ≠ auxVar φ i := by
  unfold auxNegVar auxVar
  omega

theorem auxVar_injective {φ : ThreeCNF} {i j : Nat}
    (h : auxVar φ i = auxVar φ j) : i = j := by
  unfold auxVar at h
  omega

theorem auxNegVar_injective {φ : ThreeCNF} {i j : Nat}
    (h : auxNegVar φ i = auxNegVar φ j) : i = j := by
  unfold auxNegVar at h
  omega

theorem auxVar_ne_auxNegVar {φ : ThreeCNF} {i j : Nat} :
    auxVar φ i ≠ auxNegVar φ j := by
  unfold auxVar auxNegVar
  omega

theorem auxNegVar_ne_auxVar {φ : ThreeCNF} {i j : Nat} :
    auxNegVar φ i ≠ auxVar φ j := by
  exact Ne.symm (auxVar_ne_auxNegVar (φ := φ) (i := j) (j := i))

theorem setClauseAux_falseVar {φ : ThreeCNF} {i : Nat} {c : Clause}
    {source target : Assignment} :
    setClauseAux φ i c source target (falseVar φ) = target (falseVar φ) := by
  simp [setClauseAux,
    SAT.Clause.setVar_ne (Ne.symm (auxNegVar_ne_falseVar (φ := φ) (i := i))),
    SAT.Clause.setVar_ne (Ne.symm (auxVar_ne_falseVar (φ := φ) (i := i)))]

theorem setClauseAux_trueVar {φ : ThreeCNF} {i : Nat} {c : Clause}
    {source target : Assignment} :
    setClauseAux φ i c source target (trueVar φ) = target (trueVar φ) := by
  simp [setClauseAux,
    SAT.Clause.setVar_ne (Ne.symm (auxNegVar_ne_trueVar (φ := φ) (i := i))),
    SAT.Clause.setVar_ne (Ne.symm (auxVar_ne_trueVar (φ := φ) (i := i)))]

theorem setClauseAux_source {φ : ThreeCNF} {i x : Nat} {c : Clause}
    {source target : Assignment}
    (hx : x < falseVar φ) :
    setClauseAux φ i c source target x = target x := by
  simp [setClauseAux,
    SAT.Clause.setVar_ne (Ne.symm (auxNegVar_ne_sourceVar (φ := φ) (i := i) hx)),
    SAT.Clause.setVar_ne (Ne.symm (auxVar_ne_sourceVar (φ := φ) (i := i) hx))]

theorem setClauseAux_negVar {φ : ThreeCNF} {i x : Nat} {c : Clause}
    {source target : Assignment}
    (hx : x < falseVar φ) :
    setClauseAux φ i c source target (negVar φ x) = target (negVar φ x) := by
  simp [setClauseAux,
    SAT.Clause.setVar_ne (Ne.symm (auxNegVar_ne_negVar (φ := φ) (i := i) hx)),
    SAT.Clause.setVar_ne (Ne.symm (auxVar_ne_negVar (φ := φ) (i := i) hx))]

theorem setClauseAux_auxVar_same {φ : ThreeCNF} {i : Nat} {c : Clause}
    {source target : Assignment} :
    setClauseAux φ i c source target (auxVar φ i) = sourceClauseAuxValue source c := by
  simp [setClauseAux, SAT.Clause.setVar_ne (auxVar_ne_auxNegVar (φ := φ) (i := i) (j := i))]

theorem setClauseAux_auxNegVar_same {φ : ThreeCNF} {i : Nat} {c : Clause}
    {source target : Assignment} :
    setClauseAux φ i c source target (auxNegVar φ i) = !(sourceClauseAuxValue source c) := by
  simp [setClauseAux]

theorem setClauseAux_auxVar_of_ne {φ : ThreeCNF} {i j : Nat} {c : Clause}
    {source target : Assignment} (hij : i ≠ j) :
    setClauseAux φ j c source target (auxVar φ i) = target (auxVar φ i) := by
  have hAuxNeg : auxVar φ i ≠ auxNegVar φ j :=
    auxVar_ne_auxNegVar (φ := φ) (i := i) (j := j)
  have hAux : auxVar φ i ≠ auxVar φ j := by
    intro h
    exact hij (auxVar_injective h)
  simp [setClauseAux, SAT.Clause.setVar_ne hAuxNeg, SAT.Clause.setVar_ne hAux]

theorem setClauseAux_auxNegVar_of_ne {φ : ThreeCNF} {i j : Nat} {c : Clause}
    {source target : Assignment} (hij : i ≠ j) :
    setClauseAux φ j c source target (auxNegVar φ i) = target (auxNegVar φ i) := by
  have hAuxNeg : auxNegVar φ i ≠ auxNegVar φ j := by
    intro h
    exact hij (auxNegVar_injective h)
  have hAux : auxNegVar φ i ≠ auxVar φ j :=
    auxNegVar_ne_auxVar (φ := φ) (i := i) (j := j)
  simp [setClauseAux, SAT.Clause.setVar_ne hAuxNeg, SAT.Clause.setVar_ne hAux]

theorem auxValues_setClauseAux_before {φ : ThreeCNF} {clauses : CNF}
    {source target : Assignment} {setAt start : Nat} {c : Clause}
    (hBefore : setAt < start) :
    AuxValues φ start clauses source (setClauseAux φ setAt c source target) ↔
      AuxValues φ start clauses source target := by
  induction clauses generalizing start with
  | nil =>
      simp [AuxValues]
  | cons head tail ih =>
      have hne : start ≠ setAt := ne_of_gt hBefore
      have hAux :
          setClauseAux φ setAt c source target (auxVar φ start) =
            target (auxVar φ start) :=
        setClauseAux_auxVar_of_ne hne
      have hAuxNeg :
          setClauseAux φ setAt c source target (auxNegVar φ start) =
            target (auxNegVar φ start) :=
        setClauseAux_auxNegVar_of_ne hne
      have htail := ih (start := start + 1)
        (Nat.lt_trans hBefore (Nat.lt_succ_self start))
      constructor
      · intro h
        exact ⟨by simpa [hAux] using h.1,
          by simpa [hAux, hAuxNeg] using h.2.1, htail.1 h.2.2⟩
      · intro h
        exact ⟨by simpa [hAux] using h.1,
          by simpa [hAux, hAuxNeg] using h.2.1, htail.2 h.2.2⟩

theorem extendAssignmentAux_falseVar {φ : ThreeCNF} {clauses : CNF}
    {i : Nat} {source base : Assignment} :
    extendAssignmentAux φ i clauses source base (falseVar φ) = base (falseVar φ) := by
  induction clauses generalizing i with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [extendAssignmentAux, setClauseAux_falseVar, ih]

theorem extendAssignmentAux_trueVar {φ : ThreeCNF} {clauses : CNF}
    {i : Nat} {source base : Assignment} :
    extendAssignmentAux φ i clauses source base (trueVar φ) = base (trueVar φ) := by
  induction clauses generalizing i with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [extendAssignmentAux, setClauseAux_trueVar, ih]

theorem extendAssignmentAux_source {φ : ThreeCNF} {clauses : CNF}
    {i x : Nat} {source base : Assignment} (hx : x < falseVar φ) :
    extendAssignmentAux φ i clauses source base x = base x := by
  induction clauses generalizing i with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [extendAssignmentAux, setClauseAux_source hx, ih]

theorem extendAssignmentAux_negVar {φ : ThreeCNF} {clauses : CNF}
    {i x : Nat} {source base : Assignment} (hx : x < falseVar φ) :
    extendAssignmentAux φ i clauses source base (negVar φ x) = base (negVar φ x) := by
  induction clauses generalizing i with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [extendAssignmentAux, setClauseAux_negVar hx, ih]

theorem extendAssignmentAux_auxVar_before {φ : ThreeCNF} {clauses : CNF}
    {start i : Nat} {source base : Assignment} (hBefore : i < start) :
    extendAssignmentAux φ start clauses source base (auxVar φ i) = base (auxVar φ i) := by
  induction clauses generalizing start with
  | nil =>
      rfl
  | cons c cs ih =>
      have hne : i ≠ start := ne_of_lt hBefore
      simp [extendAssignmentAux, setClauseAux_auxVar_of_ne hne,
        ih (Nat.lt_trans hBefore (Nat.lt_succ_self start))]

theorem extendAssignmentAux_auxNegVar_before {φ : ThreeCNF} {clauses : CNF}
    {start i : Nat} {source base : Assignment} (hBefore : i < start) :
    extendAssignmentAux φ start clauses source base (auxNegVar φ i) =
      base (auxNegVar φ i) := by
  induction clauses generalizing start with
  | nil =>
      rfl
  | cons c cs ih =>
      have hne : i ≠ start := ne_of_lt hBefore
      simp [extendAssignmentAux, setClauseAux_auxNegVar_of_ne hne,
        ih (Nat.lt_trans hBefore (Nat.lt_succ_self start))]

theorem extendAssignmentAux_auxValues {φ : ThreeCNF} {clauses : CNF}
    {i : Nat} {source base : Assignment} :
    AuxValues φ i clauses source (extendAssignmentAux φ i clauses source base) := by
  induction clauses generalizing i with
  | nil =>
      trivial
  | cons c cs ih =>
      constructor
      · simp [extendAssignmentAux, setClauseAux_auxVar_same]
      · constructor
        · simp [extendAssignmentAux, setClauseAux_auxNegVar_same, setClauseAux_auxVar_same]
        · exact (auxValues_setClauseAux_before
            (φ := φ) (clauses := cs) (source := source)
            (target := extendAssignmentAux φ (i + 1) cs source base)
            (setAt := i) (start := i + 1) (c := c)
            (Nat.lt_succ_self i)).2 (ih (i := i + 1))

theorem sourceVar_ne_falseVar {φ : ThreeCNF} {x : Nat} (hx : x < falseVar φ) :
    x ≠ falseVar φ := by
  exact ne_of_lt hx

theorem sourceVar_ne_trueVar {φ : ThreeCNF} {x : Nat} (hx : x < falseVar φ) :
    x ≠ trueVar φ := by
  unfold trueVar
  omega

theorem sourceVar_not_negVar {φ : ThreeCNF} {x : Nat} (hx : x < falseVar φ) :
    ¬(∃ z, z < falseVar φ ∧ x = negVar φ z) := by
  rintro ⟨z, _hz, hxz⟩
  unfold negVar at hxz
  omega

theorem extendBaseAssignment_falseVar (φ : ThreeCNF) (a : Assignment) :
    extendBaseAssignment φ a (falseVar φ) = false := by
  simp [extendBaseAssignment]

theorem extendBaseAssignment_trueVar (φ : ThreeCNF) (a : Assignment) :
    extendBaseAssignment φ a (trueVar φ) = true := by
  simp [extendBaseAssignment, trueVar]

theorem extendBaseAssignment_source {φ : ThreeCNF} {a : Assignment} {x : Nat}
    (hx : x < falseVar φ) :
    extendBaseAssignment φ a x = a x := by
  unfold extendBaseAssignment
  rw [if_neg (sourceVar_ne_falseVar hx), if_neg (sourceVar_ne_trueVar hx),
    dif_neg (sourceVar_not_negVar hx)]

end NAE3SAT
end Hardness
end CSP
end ComplexityReduction
