/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Examples.OneInThree
import ComplexityReduction.Certificates
import ComplexityReduction.SAT.CNFTo3SATCosted

/-!
Ordinary one-in-three SAT reverse gadget, work in progress for P0.

This file starts the direct `3SAT <=p one-in-three SAT` construction over the
ordinary singleton exactly-one ternary language.  The target constraints use no
pinning relation and no hidden polarity symbols; constants are represented by
global anchor variables forced with repeated-variable one-in-three constraints.
-/

namespace ComplexityReduction
namespace CSP
namespace Hardness
namespace OneInThree

open SAT

/-- Boolean exactly-one predicate for three values. -/
def oneBool (x y z : Bool) : Prop :=
  (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = 1

/-- Ordinary one-in-three constraint over three variables. -/
def oneConstraint (x y z : Nat) : Constraint Examples.oneInThreeLanguage where
  symbol := Examples.OneInThreeSymbol.rel
  vars := fun
    | ⟨0, _⟩ => x
    | ⟨1, _⟩ => y
    | _ => z

theorem oneInThreeRel_holds_iff (x y z : Bool) :
    Examples.oneInThreeRel.Holds
        (fun i : Fin Examples.oneInThreeRel.arity =>
          match i.val with
          | 0 => x
          | 1 => y
          | _ => z) ↔
      oneBool x y z := by
  change
    (fun i : Fin 3 =>
        match i.val with
        | 0 => x
        | 1 => y
        | _ => z) ∈
        Finset.univ.filter (fun t : BoolTuple 3 => Examples.trueCount3 t = 1) ↔
      oneBool x y z
  rw [Finset.mem_filter]
  simp [Examples.trueCount3, oneBool]

theorem oneConstraint_satisfies_iff (x y z : Nat) (a : Assignment) :
    Constraint.Satisfies (oneConstraint x y z) a ↔ oneBool (a x) (a y) (a z) := by
  cases hx : a x <;> cases hy : a y <;> cases hz : a z <;>
    simp [Constraint.Satisfies, Constraint.assignmentTuple, oneConstraint,
      Examples.oneInThreeLanguage, Examples.oneInThreeRel, Examples.trueCount3,
      oneBool, hx, hy, hz]

/-- First fresh variable used as the global false anchor. -/
def falseVar (φ : ThreeCNF) : Nat :=
  CNF.varBound φ.clauses

/-- Second fresh variable used as the global true anchor. -/
def trueVar (φ : ThreeCNF) : Nat :=
  falseVar φ + 1

/-- Dedicated variable representing the negation of source variable `x`. -/
def negVar (φ : ThreeCNF) (x : Nat) : Nat :=
  falseVar φ + 2 + x

/-- First local auxiliary variable block for clause `i`. -/
def auxBase (φ : ThreeCNF) : Nat :=
  falseVar φ + 2 + falseVar φ

def aux0Var (φ : ThreeCNF) (i : Nat) : Nat :=
  auxBase φ + 4 * i

def aux1Var (φ : ThreeCNF) (i : Nat) : Nat :=
  auxBase φ + 4 * i + 1

def aux2Var (φ : ThreeCNF) (i : Nat) : Nat :=
  auxBase φ + 4 * i + 2

def aux3Var (φ : ThreeCNF) (i : Nat) : Nat :=
  auxBase φ + 4 * i + 3

/-- Anchor constraints forcing `falseVar` to false and `trueVar` to true. -/
def anchorConstraints (φ : ThreeCNF) : Formula Examples.oneInThreeLanguage :=
  [oneConstraint (falseVar φ) (falseVar φ) (trueVar φ)]

theorem anchorConstraints_project_false {φ : ThreeCNF} {a : Assignment}
    (h : Formula.Satisfies (anchorConstraints φ) a) :
    a (falseVar φ) = false := by
  have hc :
      Constraint.Satisfies
        (oneConstraint (falseVar φ) (falseVar φ) (trueVar φ)) a := by
    exact h _ (by simp [anchorConstraints])
  have hone := (oneConstraint_satisfies_iff (falseVar φ) (falseVar φ) (trueVar φ) a).1 hc
  cases hf : a (falseVar φ) <;> cases ht : a (trueVar φ) <;>
    simp [oneBool, hf, ht] at hone ⊢

theorem anchorConstraints_project_true {φ : ThreeCNF} {a : Assignment}
    (h : Formula.Satisfies (anchorConstraints φ) a) :
    a (trueVar φ) = true := by
  have hc :
      Constraint.Satisfies
        (oneConstraint (falseVar φ) (falseVar φ) (trueVar φ)) a := by
    exact h _ (by simp [anchorConstraints])
  have hone := (oneConstraint_satisfies_iff (falseVar φ) (falseVar φ) (trueVar φ) a).1 hc
  cases hf : a (falseVar φ) <;> cases ht : a (trueVar φ) <;>
    simp [oneBool, hf, ht] at hone ⊢

theorem anchorConstraints_extend {φ : ThreeCNF} {a : Assignment}
    (hF : a (falseVar φ) = false) (hT : a (trueVar φ) = true) :
    Formula.Satisfies (anchorConstraints φ) a := by
  intro c hc
  have hcEq :
      c = oneConstraint (falseVar φ) (falseVar φ) (trueVar φ) := by
    simpa [anchorConstraints] using hc
  subst c
  exact (oneConstraint_satisfies_iff (falseVar φ) (falseVar φ) (trueVar φ) a).2
    (by simp [oneBool, hF, hT])

/-- Constraint forcing `nx` to be the complement of `x`, assuming the false anchor. -/
def complementPairConstraints (φ : ThreeCNF) (x nx : Nat) :
    Formula Examples.oneInThreeLanguage :=
  [oneConstraint x nx (falseVar φ)]

def sourceComplementConstraintsAux (φ : ThreeCNF) : Nat → Formula Examples.oneInThreeLanguage
  | 0 => []
  | n + 1 =>
      complementPairConstraints φ n (negVar φ n) ++ sourceComplementConstraintsAux φ n

def sourceComplementConstraints (φ : ThreeCNF) : Formula Examples.oneInThreeLanguage :=
  sourceComplementConstraintsAux φ (falseVar φ)

def litVar (φ : ThreeCNF) (l : Literal) : Nat :=
  if l.neg then negVar φ l.var else l.var

def litNegVar (φ : ThreeCNF) (l : Literal) : Nat :=
  if l.neg then l.var else negVar φ l.var

theorem complementPair_project {φ : ThreeCNF} {x nx : Nat} {a : Assignment}
    (hF : a (falseVar φ) = false)
    (h : Formula.Satisfies (complementPairConstraints φ x nx) a) :
    a nx = !(a x) := by
  have hc : Constraint.Satisfies (oneConstraint x nx (falseVar φ)) a := by
    exact h _ (by simp [complementPairConstraints])
  have hone := (oneConstraint_satisfies_iff x nx (falseVar φ) a).1 hc
  cases hx : a x <;> cases hnx : a nx <;>
    simp [oneBool, hF, hx, hnx] at hone ⊢

theorem complementPair_extend {φ : ThreeCNF} {x nx : Nat} {a : Assignment}
    (hF : a (falseVar φ) = false) (hNX : a nx = !(a x)) :
    Formula.Satisfies (complementPairConstraints φ x nx) a := by
  intro c hc
  have hcEq : c = oneConstraint x nx (falseVar φ) := by
    simpa [complementPairConstraints] using hc
  subst c
  exact (oneConstraint_satisfies_iff x nx (falseVar φ) a).2 (by
    cases hx : a x <;> cases hnx : a nx <;>
      simp [oneBool, hF, hx, hnx] at hNX ⊢)

theorem sourceComplementConstraintsAux_project {φ : ThreeCNF} {a : Assignment}
    (hF : a (falseVar φ) = false)
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
        exact h c (by exact List.mem_append.mpr (Or.inr hc))
      have hhead :
          Formula.Satisfies (complementPairConstraints φ k (negVar φ k)) a := by
        intro c hc
        exact h c (by exact List.mem_append.mpr (Or.inl hc))
      intro x hx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hxlt | rfl
      · exact sourceComplementConstraintsAux_project hF htail x hxlt
      · exact complementPair_project hF hhead

theorem sourceComplementConstraintsAux_extend {φ : ThreeCNF} {a : Assignment}
    (hF : a (falseVar φ) = false)
    {n : Nat} (hNeg : ∀ x, x < n → a (negVar φ x) = !(a x)) :
    Formula.Satisfies (sourceComplementConstraintsAux φ n) a := by
  induction n with
  | zero =>
      intro c hc
      cases hc
  | succ n ih =>
      intro c hc
      rcases List.mem_append.mp (by simpa [sourceComplementConstraintsAux] using hc) with hhead | htail
      · exact complementPair_extend hF (hNeg n (Nat.lt_succ_self n)) c hhead
      · exact ih (by intro x hx; exact hNeg x (Nat.lt_trans hx (Nat.lt_succ_self n))) c htail

theorem litVar_eval_eq {φ : ThreeCNF} {a : Assignment}
    (hNeg : ∀ x, x < falseVar φ → a (negVar φ x) = !(a x))
    {l : Literal} (hl : l.var < falseVar φ) :
    a (litVar φ l) = l.eval a := by
  cases l with
  | mk v neg =>
      cases neg <;> simp [litVar, Literal.eval, hNeg v hl]

theorem litNegVar_eval_eq {φ : ThreeCNF} {a : Assignment}
    (hNeg : ∀ x, x < falseVar φ → a (negVar φ x) = !(a x))
    {l : Literal} (hl : l.var < falseVar φ) :
    a (litNegVar φ l) = !(l.eval a) := by
  cases l with
  | mk v neg =>
      cases neg <;> simp [litNegVar, Literal.eval, hNeg v hl]

theorem litNegVar_complement_litVar {φ : ThreeCNF} {a : Assignment}
    (hNeg : ∀ x, x < falseVar φ → a (negVar φ x) = !(a x))
    {l : Literal} (hl : l.var < falseVar φ) :
    a (litNegVar φ l) = !(a (litVar φ l)) := by
  cases l with
  | mk v neg =>
      cases neg <;> simp [litVar, litNegVar, hNeg v hl]

/-- First auxiliary witness for the fixed three-constraint OR gadget. -/
def gadgetAux0 (x y z : Bool) : Bool :=
  x && !y && !z

/-- Second auxiliary witness for the fixed three-constraint OR gadget. -/
def gadgetAux1 (x y z : Bool) : Bool :=
  x && (y || z)

/-- Third auxiliary witness for the fixed three-constraint OR gadget. -/
def gadgetAux2 (_x y z : Bool) : Bool :=
  y && !z

/-- Fourth auxiliary witness for the fixed three-constraint OR gadget. -/
def gadgetAux3 (_x y z : Bool) : Bool :=
  y && z

/--
Fixed exactly-one OR gadget.  The first two constraints consume complements of
the first two inputs; the third input is used directly.
-/
def clauseGadgetBlock (x y z a0 a1 a2 a3 : Bool) : Prop :=
  oneBool (!x) a0 a1 ∧ oneBool (!y) a2 a3 ∧ oneBool z a0 a2

theorem clauseGadget_project (x y z a0 a1 a2 a3 : Bool)
    (h : clauseGadgetBlock x y z a0 a1 a2 a3) :
    x = true ∨ y = true ∨ z = true := by
  cases x <;> cases y <;> cases z <;> cases a0 <;> cases a1 <;>
    cases a2 <;> cases a3 <;> simp [clauseGadgetBlock, oneBool] at h ⊢

theorem clauseGadget_extend (x y z : Bool)
    (h : x = true ∨ y = true ∨ z = true) :
    clauseGadgetBlock x y z
      (gadgetAux0 x y z) (gadgetAux1 x y z)
      (gadgetAux2 x y z) (gadgetAux3 x y z) := by
  cases x <;> cases y <;> cases z <;>
    simp [clauseGadgetBlock, oneBool, gadgetAux0, gadgetAux1, gadgetAux2, gadgetAux3] at h ⊢

def clauseGadgetFormula (φ : ThreeCNF) (i : Nat)
    (_x nx _y ny z : Nat) : Formula Examples.oneInThreeLanguage :=
  [ oneConstraint nx (aux0Var φ i) (aux1Var φ i)
  , oneConstraint ny (aux2Var φ i) (aux3Var φ i)
  , oneConstraint z (aux0Var φ i) (aux2Var φ i)
  ]

theorem clauseGadgetFormula_project {φ : ThreeCNF} {i x nx y ny z : Nat}
    {a : Assignment}
    (hNX : a nx = !(a x)) (hNY : a ny = !(a y))
    (h : Formula.Satisfies (clauseGadgetFormula φ i x nx y ny z) a) :
    a x = true ∨ a y = true ∨ a z = true := by
  have h₁ :
      Constraint.Satisfies (oneConstraint nx (aux0Var φ i) (aux1Var φ i)) a := by
    exact h _ (by simp [clauseGadgetFormula])
  have h₂ :
      Constraint.Satisfies (oneConstraint ny (aux2Var φ i) (aux3Var φ i)) a := by
    exact h _ (by simp [clauseGadgetFormula])
  have h₃ :
      Constraint.Satisfies (oneConstraint z (aux0Var φ i) (aux2Var φ i)) a := by
    exact h _ (by simp [clauseGadgetFormula])
  exact clauseGadget_project (a x) (a y) (a z)
    (a (aux0Var φ i)) (a (aux1Var φ i)) (a (aux2Var φ i)) (a (aux3Var φ i))
    (by
      constructor
      · simpa [hNX] using
          (oneConstraint_satisfies_iff nx (aux0Var φ i) (aux1Var φ i) a).1 h₁
      · constructor
        · simpa [hNY] using
            (oneConstraint_satisfies_iff ny (aux2Var φ i) (aux3Var φ i) a).1 h₂
        · exact (oneConstraint_satisfies_iff z (aux0Var φ i) (aux2Var φ i) a).1 h₃)

theorem clauseGadgetFormula_extend {φ : ThreeCNF} {i x nx y ny z : Nat}
    {a : Assignment} {vx vy vz : Bool}
    (_hX : a x = vx) (hNX : a nx = !vx)
    (_hY : a y = vy) (hNY : a ny = !vy)
    (hZ : a z = vz)
    (hA0 : a (aux0Var φ i) = gadgetAux0 vx vy vz)
    (hA1 : a (aux1Var φ i) = gadgetAux1 vx vy vz)
    (hA2 : a (aux2Var φ i) = gadgetAux2 vx vy vz)
    (hA3 : a (aux3Var φ i) = gadgetAux3 vx vy vz)
    (hSat : vx = true ∨ vy = true ∨ vz = true) :
    Formula.Satisfies (clauseGadgetFormula φ i x nx y ny z) a := by
  have hBlock := clauseGadget_extend vx vy vz hSat
  intro c hc
  have hCases :
      c = oneConstraint nx (aux0Var φ i) (aux1Var φ i) ∨
        c = oneConstraint ny (aux2Var φ i) (aux3Var φ i) ∨
          c = oneConstraint z (aux0Var φ i) (aux2Var φ i) := by
    simpa [clauseGadgetFormula] using hc
  rcases hCases with h₁ | h₂ | h₃
  · subst c
    exact (oneConstraint_satisfies_iff nx (aux0Var φ i) (aux1Var φ i) a).2
      (by simpa [hNX, hA0, hA1] using hBlock.1)
  · subst c
    exact (oneConstraint_satisfies_iff ny (aux2Var φ i) (aux3Var φ i) a).2
      (by simpa [hNY, hA2, hA3] using hBlock.2.1)
  · subst c
    exact (oneConstraint_satisfies_iff z (aux0Var φ i) (aux2Var φ i) a).2
      (by simpa [hZ, hA0, hA2] using hBlock.2.2)

def sourceClauseXValue (a : Assignment) : Clause → Bool
  | l₁ :: _ => l₁.eval a
  | [] => false

def sourceClauseYValue (a : Assignment) : Clause → Bool
  | _ :: l₂ :: _ => l₂.eval a
  | _ => false

def sourceClauseZValue (a : Assignment) : Clause → Bool
  | _ :: _ :: l₃ :: _ => l₃.eval a
  | _ => false

def clauseToFormula (φ : ThreeCNF) (i : Nat) : Clause → Formula Examples.oneInThreeLanguage
  | [] =>
      [oneConstraint (trueVar φ) (trueVar φ) (falseVar φ)]
  | [l₁] =>
      clauseGadgetFormula φ i
        (litVar φ l₁) (litNegVar φ l₁)
        (falseVar φ) (trueVar φ)
        (falseVar φ)
  | [l₁, l₂] =>
      clauseGadgetFormula φ i
        (litVar φ l₁) (litNegVar φ l₁)
        (litVar φ l₂) (litNegVar φ l₂)
        (falseVar φ)
  | l₁ :: l₂ :: l₃ :: _ =>
      clauseGadgetFormula φ i
        (litVar φ l₁) (litNegVar φ l₁)
        (litVar φ l₂) (litNegVar φ l₂)
        (litVar φ l₃)

def clausesToFormulaAux (φ : ThreeCNF) : Nat → CNF → Formula Examples.oneInThreeLanguage
  | _, [] => []
  | i, c :: cs => clauseToFormula φ i c ++ clausesToFormulaAux φ (i + 1) cs

def threeCNFToOneInThreeFormula (φ : ThreeCNF) : Formula Examples.oneInThreeLanguage :=
  anchorConstraints φ ++ sourceComplementConstraints φ ++ clausesToFormulaAux φ 0 φ.clauses

theorem clauseToFormula_project {φ : ThreeCNF} {c : Clause} (hlen : c.length ≤ 3)
    {i : Nat} {a : Assignment}
    (hF : a (falseVar φ) = false)
    (hT : a (trueVar φ) = true)
    (hNeg : ∀ x, x < falseVar φ → a (negVar φ x) = !(a x))
    (hVars : ∀ l ∈ c, l.var < falseVar φ)
    (h : Formula.Satisfies (clauseToFormula φ i c) a) :
    Clause.Satisfies c a := by
  cases c with
  | nil =>
      have hc :
          Constraint.Satisfies (oneConstraint (trueVar φ) (trueVar φ) (falseVar φ)) a := by
        exact h _ (by simp [clauseToFormula])
      have hone := (oneConstraint_satisfies_iff (trueVar φ) (trueVar φ) (falseVar φ) a).1 hc
      simp [oneBool, hF, hT] at hone
  | cons l₁ rest =>
      cases rest with
      | nil =>
          have hOr :
              a (litVar φ l₁) = true ∨ a (falseVar φ) = true ∨
                a (falseVar φ) = true := by
            exact clauseGadgetFormula_project
              (litNegVar_complement_litVar hNeg (hVars l₁ (by simp)))
              (by simpa [hF] using hT)
              (by simpa [clauseToFormula] using h)
          have hLit₁ := litVar_eval_eq hNeg (hVars l₁ (by simp))
          rcases hOr with h₁ | h₂ | h₃
          · exact ⟨l₁, by simp, by simpa [hLit₁] using h₁⟩
          · simp [hF] at h₂
          · simp [hF] at h₃
      | cons l₂ rest₂ =>
          cases rest₂ with
          | nil =>
              have hOr :
                  a (litVar φ l₁) = true ∨ a (litVar φ l₂) = true ∨
                    a (falseVar φ) = true := by
                exact clauseGadgetFormula_project
                  (litNegVar_complement_litVar hNeg (hVars l₁ (by simp)))
                  (litNegVar_complement_litVar hNeg (hVars l₂ (by simp)))
                  (by simpa [clauseToFormula] using h)
              have hLit₁ := litVar_eval_eq hNeg (hVars l₁ (by simp))
              have hLit₂ := litVar_eval_eq hNeg (hVars l₂ (by simp))
              rcases hOr with h₁ | h₂ | h₃
              · exact ⟨l₁, by simp, by simpa [hLit₁] using h₁⟩
              · exact ⟨l₂, by simp, by simpa [hLit₂] using h₂⟩
              · simp [hF] at h₃
          | cons l₃ rest₃ =>
              cases rest₃ with
              | nil =>
                  have hOr :
                      a (litVar φ l₁) = true ∨ a (litVar φ l₂) = true ∨
                        a (litVar φ l₃) = true := by
                    exact clauseGadgetFormula_project
                      (litNegVar_complement_litVar hNeg (hVars l₁ (by simp)))
                      (litNegVar_complement_litVar hNeg (hVars l₂ (by simp)))
                      (by simpa [clauseToFormula] using h)
                  have hLit₁ := litVar_eval_eq hNeg (hVars l₁ (by simp))
                  have hLit₂ := litVar_eval_eq hNeg (hVars l₂ (by simp))
                  have hLit₃ := litVar_eval_eq hNeg (hVars l₃ (by simp))
                  rcases hOr with h₁ | h₂ | h₃
                  · exact ⟨l₁, by simp, by simpa [hLit₁] using h₁⟩
                  · exact ⟨l₂, by simp, by simpa [hLit₂] using h₂⟩
                  · exact ⟨l₃, by simp, by simpa [hLit₃] using h₃⟩
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
      · exact clauseToFormula_project hcLen hF hT hNeg
          (by intro l hl; exact hVars d (by simp) l hl)
          hBlock
      · exact ih (i := i + 1) hcsThree hcsVars hTail d hds

theorem threeCNFToOneInThreeFormula_project (φ : ThreeCNF) :
    Formula.Satisfiable (threeCNFToOneInThreeFormula φ) → φ.Satisfiable := by
  rintro ⟨a, hSat⟩
  have hSplit₁ :
      Formula.Satisfies (anchorConstraints φ) a ∧
        Formula.Satisfies (sourceComplementConstraints φ ++ clausesToFormulaAux φ 0 φ.clauses) a :=
    (Formula.satisfies_append (anchorConstraints φ)
      (sourceComplementConstraints φ ++ clausesToFormulaAux φ 0 φ.clauses) a).1
      (by simpa [threeCNFToOneInThreeFormula, List.append_assoc] using hSat)
  have hF : a (falseVar φ) = false := anchorConstraints_project_false hSplit₁.1
  have hT : a (trueVar φ) = true := anchorConstraints_project_true hSplit₁.1
  have hSplit₂ :
      Formula.Satisfies (sourceComplementConstraints φ) a ∧
        Formula.Satisfies (clausesToFormulaAux φ 0 φ.clauses) a :=
    (Formula.satisfies_append (sourceComplementConstraints φ)
      (clausesToFormulaAux φ 0 φ.clauses) a).1 hSplit₁.2
  have hNeg : ∀ x, x < falseVar φ → a (negVar φ x) = !(a x) :=
    sourceComplementConstraintsAux_project hF hSplit₂.1
  have hVars : ∀ c ∈ φ.clauses, ∀ l ∈ c, l.var < falseVar φ := by
    intro c hc
    exact CNF.clause_vars_lt_varBound hc
  exact ⟨a, clausesToFormulaAux_project φ.isThree hVars hF hT hNeg hSplit₂.2⟩

theorem clauseToFormula_extend {φ : ThreeCNF} {c : Clause} (hlen : c.length ≤ 3)
    {i : Nat} {a b : Assignment}
    (hF : b (falseVar φ) = false)
    (hT : b (trueVar φ) = true)
    (hLit : ∀ l ∈ c, b (litVar φ l) = l.eval a)
    (hLitNeg : ∀ l ∈ c, b (litNegVar φ l) = !(l.eval a))
    (hA0 :
      b (aux0Var φ i) =
        gadgetAux0 (sourceClauseXValue a c) (sourceClauseYValue a c)
          (sourceClauseZValue a c))
    (hA1 :
      b (aux1Var φ i) =
        gadgetAux1 (sourceClauseXValue a c) (sourceClauseYValue a c)
          (sourceClauseZValue a c))
    (hA2 :
      b (aux2Var φ i) =
        gadgetAux2 (sourceClauseXValue a c) (sourceClauseYValue a c)
          (sourceClauseZValue a c))
    (hA3 :
      b (aux3Var φ i) =
        gadgetAux3 (sourceClauseXValue a c) (sourceClauseYValue a c)
          (sourceClauseZValue a c))
    (hSat : Clause.Satisfies c a) :
    Formula.Satisfies (clauseToFormula φ i c) b := by
  cases c with
  | nil =>
      rcases hSat with ⟨l, hl, _⟩
      cases hl
  | cons l₁ rest =>
      cases rest with
      | nil =>
          rcases hSat with ⟨l, hl, hlEval⟩
          have hl₁ : l = l₁ := by simpa using hl
          subst l
          exact clauseGadgetFormula_extend
            (by simpa [sourceClauseXValue] using hLit l₁ (by simp))
            (by simpa [sourceClauseXValue] using hLitNeg l₁ (by simp))
            hF
            (by simpa [hF] using hT)
            hF
            (by simpa [sourceClauseXValue, sourceClauseYValue, sourceClauseZValue] using hA0)
            (by simpa [sourceClauseXValue, sourceClauseYValue, sourceClauseZValue] using hA1)
            (by simpa [sourceClauseXValue, sourceClauseYValue, sourceClauseZValue] using hA2)
            (by simpa [sourceClauseXValue, sourceClauseYValue, sourceClauseZValue] using hA3)
            (Or.inl hlEval)
      | cons l₂ rest₂ =>
          cases rest₂ with
          | nil =>
              have hSatBool :
                  l₁.eval a = true ∨ l₂.eval a = true ∨ false = true := by
                rcases hSat with ⟨l, hl, hlEval⟩
                rcases List.mem_cons.mp hl with h₁ | htail
                · subst l
                  exact Or.inl hlEval
                · have h₂ : l = l₂ := by simpa using htail
                  subst l
                  exact Or.inr (Or.inl hlEval)
              exact clauseGadgetFormula_extend
                (by simpa [sourceClauseXValue] using hLit l₁ (by simp))
                (by simpa [sourceClauseXValue] using hLitNeg l₁ (by simp))
                (by simpa [sourceClauseYValue] using hLit l₂ (by simp))
                (by simpa [sourceClauseYValue] using hLitNeg l₂ (by simp))
                hF
                (by
                  simpa [sourceClauseXValue, sourceClauseYValue, sourceClauseZValue] using hA0)
                (by
                  simpa [sourceClauseXValue, sourceClauseYValue, sourceClauseZValue] using hA1)
                (by
                  simpa [sourceClauseXValue, sourceClauseYValue, sourceClauseZValue] using hA2)
                (by
                  simpa [sourceClauseXValue, sourceClauseYValue, sourceClauseZValue] using hA3)
                hSatBool
          | cons l₃ rest₃ =>
              cases rest₃ with
              | nil =>
                  have hSatBool :
                      l₁.eval a = true ∨ l₂.eval a = true ∨ l₃.eval a = true := by
                    rcases hSat with ⟨l, hl, hlEval⟩
                    rcases List.mem_cons.mp hl with h₁ | htail
                    · subst l
                      exact Or.inl hlEval
                    · rcases List.mem_cons.mp htail with h₂ | htail₂
                      · subst l
                        exact Or.inr (Or.inl hlEval)
                      · have h₃ : l = l₃ := by simpa using htail₂
                        subst l
                        exact Or.inr (Or.inr hlEval)
                  exact clauseGadgetFormula_extend
                    (by simpa [sourceClauseXValue] using hLit l₁ (by simp))
                    (by simpa [sourceClauseXValue] using hLitNeg l₁ (by simp))
                    (by simpa [sourceClauseYValue] using hLit l₂ (by simp))
                    (by simpa [sourceClauseYValue] using hLitNeg l₂ (by simp))
                    (by simpa [sourceClauseZValue] using hLit l₃ (by simp))
                    (by
                      simpa [sourceClauseXValue, sourceClauseYValue, sourceClauseZValue] using hA0)
                    (by
                      simpa [sourceClauseXValue, sourceClauseYValue, sourceClauseZValue] using hA1)
                    (by
                      simpa [sourceClauseXValue, sourceClauseYValue, sourceClauseZValue] using hA2)
                    (by
                      simpa [sourceClauseXValue, sourceClauseYValue, sourceClauseZValue] using hA3)
                    hSatBool
              | cons _ _ =>
                  simp at hlen

def AuxValues : ThreeCNF → Nat → CNF → Assignment → Assignment → Prop
  | _, _, [], _, _ => True
  | φ, i, c :: cs, source, target =>
      target (aux0Var φ i) =
          gadgetAux0 (sourceClauseXValue source c) (sourceClauseYValue source c)
            (sourceClauseZValue source c) ∧
        target (aux1Var φ i) =
            gadgetAux1 (sourceClauseXValue source c) (sourceClauseYValue source c)
              (sourceClauseZValue source c) ∧
          target (aux2Var φ i) =
              gadgetAux2 (sourceClauseXValue source c) (sourceClauseYValue source c)
                (sourceClauseZValue source c) ∧
            target (aux3Var φ i) =
                gadgetAux3 (sourceClauseXValue source c) (sourceClauseYValue source c)
                  (sourceClauseZValue source c) ∧
              AuxValues φ (i + 1) cs source target

theorem clausesToFormulaAux_extend_of_auxValues {φ : ThreeCNF} {clauses : CNF}
    {i : Nat} {a b : Assignment}
    (hThree : CNF.IsThreeCNF clauses)
    (hF : b (falseVar φ) = false)
    (hT : b (trueVar φ) = true)
    (hLit : ∀ c ∈ clauses, ∀ l ∈ c, b (litVar φ l) = l.eval a)
    (hLitNeg : ∀ c ∈ clauses, ∀ l ∈ c, b (litNegVar φ l) = !(l.eval a))
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
      have hHeadSat : Formula.Satisfies (clauseToFormula φ i head) b :=
        clauseToFormula_extend hHeadLen hF hT
          (by intro l hl; exact hLit head (by simp) l hl)
          (by intro l hl; exact hLitNeg head (by simp) l hl)
          hAux.1 hAux.2.1 hAux.2.2.1 hAux.2.2.2.1
          (hSat head (by simp))
      have hTailSat : Formula.Satisfies (clausesToFormulaAux φ (i + 1) tail) b :=
        ih (i := i + 1) hTailThree
          (by
            intro c hc l hl
            exact hLit c (by simp [hc]) l hl)
          (by
            intro c hc l hl
            exact hLitNeg c (by simp [hc]) l hl)
          hAux.2.2.2.2
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
    (SAT.Clause.setVar
      (SAT.Clause.setVar
        (SAT.Clause.setVar target (aux0Var φ i)
          (gadgetAux0 (sourceClauseXValue source c) (sourceClauseYValue source c)
            (sourceClauseZValue source c)))
        (aux1Var φ i)
          (gadgetAux1 (sourceClauseXValue source c) (sourceClauseYValue source c)
            (sourceClauseZValue source c)))
      (aux2Var φ i)
        (gadgetAux2 (sourceClauseXValue source c) (sourceClauseYValue source c)
          (sourceClauseZValue source c)))
    (aux3Var φ i)
      (gadgetAux3 (sourceClauseXValue source c) (sourceClauseYValue source c)
        (sourceClauseZValue source c))

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

theorem aux0Var_ne_falseVar {φ : ThreeCNF} {i : Nat} :
    aux0Var φ i ≠ falseVar φ := by
  unfold aux0Var auxBase
  omega

theorem aux1Var_ne_falseVar {φ : ThreeCNF} {i : Nat} :
    aux1Var φ i ≠ falseVar φ := by
  unfold aux1Var auxBase
  omega

theorem aux2Var_ne_falseVar {φ : ThreeCNF} {i : Nat} :
    aux2Var φ i ≠ falseVar φ := by
  unfold aux2Var auxBase
  omega

theorem aux3Var_ne_falseVar {φ : ThreeCNF} {i : Nat} :
    aux3Var φ i ≠ falseVar φ := by
  unfold aux3Var auxBase
  omega

theorem aux0Var_ne_trueVar {φ : ThreeCNF} {i : Nat} :
    aux0Var φ i ≠ trueVar φ := by
  unfold aux0Var auxBase trueVar
  omega

theorem aux1Var_ne_trueVar {φ : ThreeCNF} {i : Nat} :
    aux1Var φ i ≠ trueVar φ := by
  unfold aux1Var auxBase trueVar
  omega

theorem aux2Var_ne_trueVar {φ : ThreeCNF} {i : Nat} :
    aux2Var φ i ≠ trueVar φ := by
  unfold aux2Var auxBase trueVar
  omega

theorem aux3Var_ne_trueVar {φ : ThreeCNF} {i : Nat} :
    aux3Var φ i ≠ trueVar φ := by
  unfold aux3Var auxBase trueVar
  omega

theorem aux0Var_ne_sourceVar {φ : ThreeCNF} {i x : Nat} (hx : x < falseVar φ) :
    aux0Var φ i ≠ x := by
  unfold aux0Var auxBase
  omega

theorem aux1Var_ne_sourceVar {φ : ThreeCNF} {i x : Nat} (hx : x < falseVar φ) :
    aux1Var φ i ≠ x := by
  unfold aux1Var auxBase
  omega

theorem aux2Var_ne_sourceVar {φ : ThreeCNF} {i x : Nat} (hx : x < falseVar φ) :
    aux2Var φ i ≠ x := by
  unfold aux2Var auxBase
  omega

theorem aux3Var_ne_sourceVar {φ : ThreeCNF} {i x : Nat} (hx : x < falseVar φ) :
    aux3Var φ i ≠ x := by
  unfold aux3Var auxBase
  omega

theorem aux0Var_ne_negVar {φ : ThreeCNF} {i x : Nat} (hx : x < falseVar φ) :
    aux0Var φ i ≠ negVar φ x := by
  unfold aux0Var auxBase negVar
  omega

theorem aux1Var_ne_negVar {φ : ThreeCNF} {i x : Nat} (hx : x < falseVar φ) :
    aux1Var φ i ≠ negVar φ x := by
  unfold aux1Var auxBase negVar
  omega

theorem aux2Var_ne_negVar {φ : ThreeCNF} {i x : Nat} (hx : x < falseVar φ) :
    aux2Var φ i ≠ negVar φ x := by
  unfold aux2Var auxBase negVar
  omega

theorem aux3Var_ne_negVar {φ : ThreeCNF} {i x : Nat} (hx : x < falseVar φ) :
    aux3Var φ i ≠ negVar φ x := by
  unfold aux3Var auxBase negVar
  omega

theorem aux0Var_injective {φ : ThreeCNF} {i j : Nat}
    (h : aux0Var φ i = aux0Var φ j) : i = j := by
  unfold aux0Var at h
  omega

theorem aux1Var_injective {φ : ThreeCNF} {i j : Nat}
    (h : aux1Var φ i = aux1Var φ j) : i = j := by
  unfold aux1Var at h
  omega

theorem aux2Var_injective {φ : ThreeCNF} {i j : Nat}
    (h : aux2Var φ i = aux2Var φ j) : i = j := by
  unfold aux2Var at h
  omega

theorem aux3Var_injective {φ : ThreeCNF} {i j : Nat}
    (h : aux3Var φ i = aux3Var φ j) : i = j := by
  unfold aux3Var at h
  omega

theorem aux0Var_ne_aux1Var {φ : ThreeCNF} {i j : Nat} :
    aux0Var φ i ≠ aux1Var φ j := by
  unfold aux0Var aux1Var
  omega

theorem aux0Var_ne_aux2Var {φ : ThreeCNF} {i j : Nat} :
    aux0Var φ i ≠ aux2Var φ j := by
  unfold aux0Var aux2Var
  omega

theorem aux0Var_ne_aux3Var {φ : ThreeCNF} {i j : Nat} :
    aux0Var φ i ≠ aux3Var φ j := by
  unfold aux0Var aux3Var
  omega

theorem aux1Var_ne_aux0Var {φ : ThreeCNF} {i j : Nat} :
    aux1Var φ i ≠ aux0Var φ j := by
  exact Ne.symm (aux0Var_ne_aux1Var (φ := φ) (i := j) (j := i))

theorem aux1Var_ne_aux2Var {φ : ThreeCNF} {i j : Nat} :
    aux1Var φ i ≠ aux2Var φ j := by
  unfold aux1Var aux2Var
  omega

theorem aux1Var_ne_aux3Var {φ : ThreeCNF} {i j : Nat} :
    aux1Var φ i ≠ aux3Var φ j := by
  unfold aux1Var aux3Var
  omega

theorem aux2Var_ne_aux0Var {φ : ThreeCNF} {i j : Nat} :
    aux2Var φ i ≠ aux0Var φ j := by
  exact Ne.symm (aux0Var_ne_aux2Var (φ := φ) (i := j) (j := i))

theorem aux2Var_ne_aux1Var {φ : ThreeCNF} {i j : Nat} :
    aux2Var φ i ≠ aux1Var φ j := by
  exact Ne.symm (aux1Var_ne_aux2Var (φ := φ) (i := j) (j := i))

theorem aux2Var_ne_aux3Var {φ : ThreeCNF} {i j : Nat} :
    aux2Var φ i ≠ aux3Var φ j := by
  unfold aux2Var aux3Var
  omega

theorem aux3Var_ne_aux0Var {φ : ThreeCNF} {i j : Nat} :
    aux3Var φ i ≠ aux0Var φ j := by
  exact Ne.symm (aux0Var_ne_aux3Var (φ := φ) (i := j) (j := i))

theorem aux3Var_ne_aux1Var {φ : ThreeCNF} {i j : Nat} :
    aux3Var φ i ≠ aux1Var φ j := by
  exact Ne.symm (aux1Var_ne_aux3Var (φ := φ) (i := j) (j := i))

theorem aux3Var_ne_aux2Var {φ : ThreeCNF} {i j : Nat} :
    aux3Var φ i ≠ aux2Var φ j := by
  exact Ne.symm (aux2Var_ne_aux3Var (φ := φ) (i := j) (j := i))

theorem setClauseAux_falseVar {φ : ThreeCNF} {i : Nat} {c : Clause}
    {source target : Assignment} :
    setClauseAux φ i c source target (falseVar φ) = target (falseVar φ) := by
  simp [setClauseAux,
    SAT.Clause.setVar_ne (Ne.symm (aux3Var_ne_falseVar (φ := φ) (i := i))),
    SAT.Clause.setVar_ne (Ne.symm (aux2Var_ne_falseVar (φ := φ) (i := i))),
    SAT.Clause.setVar_ne (Ne.symm (aux1Var_ne_falseVar (φ := φ) (i := i))),
    SAT.Clause.setVar_ne (Ne.symm (aux0Var_ne_falseVar (φ := φ) (i := i)))]

theorem setClauseAux_trueVar {φ : ThreeCNF} {i : Nat} {c : Clause}
    {source target : Assignment} :
    setClauseAux φ i c source target (trueVar φ) = target (trueVar φ) := by
  simp [setClauseAux,
    SAT.Clause.setVar_ne (Ne.symm (aux3Var_ne_trueVar (φ := φ) (i := i))),
    SAT.Clause.setVar_ne (Ne.symm (aux2Var_ne_trueVar (φ := φ) (i := i))),
    SAT.Clause.setVar_ne (Ne.symm (aux1Var_ne_trueVar (φ := φ) (i := i))),
    SAT.Clause.setVar_ne (Ne.symm (aux0Var_ne_trueVar (φ := φ) (i := i)))]

theorem setClauseAux_source {φ : ThreeCNF} {i x : Nat} {c : Clause}
    {source target : Assignment}
    (hx : x < falseVar φ) :
    setClauseAux φ i c source target x = target x := by
  simp [setClauseAux,
    SAT.Clause.setVar_ne (Ne.symm (aux3Var_ne_sourceVar (φ := φ) (i := i) hx)),
    SAT.Clause.setVar_ne (Ne.symm (aux2Var_ne_sourceVar (φ := φ) (i := i) hx)),
    SAT.Clause.setVar_ne (Ne.symm (aux1Var_ne_sourceVar (φ := φ) (i := i) hx)),
    SAT.Clause.setVar_ne (Ne.symm (aux0Var_ne_sourceVar (φ := φ) (i := i) hx))]

theorem setClauseAux_negVar {φ : ThreeCNF} {i x : Nat} {c : Clause}
    {source target : Assignment}
    (hx : x < falseVar φ) :
    setClauseAux φ i c source target (negVar φ x) = target (negVar φ x) := by
  simp [setClauseAux,
    SAT.Clause.setVar_ne (Ne.symm (aux3Var_ne_negVar (φ := φ) (i := i) hx)),
    SAT.Clause.setVar_ne (Ne.symm (aux2Var_ne_negVar (φ := φ) (i := i) hx)),
    SAT.Clause.setVar_ne (Ne.symm (aux1Var_ne_negVar (φ := φ) (i := i) hx)),
    SAT.Clause.setVar_ne (Ne.symm (aux0Var_ne_negVar (φ := φ) (i := i) hx))]

end OneInThree
end Hardness
end CSP
end ComplexityReduction
