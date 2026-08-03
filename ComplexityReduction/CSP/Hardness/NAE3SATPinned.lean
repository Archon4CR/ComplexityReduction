/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Examples.NAE3SAT
import ComplexityReduction.SAT.CNFTo3SATCosted

/-!
Pinned, polarized NAE-3SAT reverse gadget.

This file proves the semantic direction `3SAT <= SAT(NAE3Pinned)`.  The target
language contains the eight literal-polarity variants of the ternary NAE
relation plus one unary `pinFalse` symbol.  This is intentionally a pinned
variant; no ordinary NAE-3SAT hardness theorem is claimed here.
-/

namespace ComplexityReduction
namespace CSP
namespace Hardness
namespace NAE3SATPinned

open SAT

/-- Relation symbols for pinned, literal-polarity NAE-3 constraints. -/
inductive NAE3PinnedSymbol where
  | nae (firstNeg secondNeg thirdNeg : Bool)
  | pinFalse
  deriving DecidableEq, Repr

instance : Fintype NAE3PinnedSymbol where
  elems :=
    { val :=
        [ NAE3PinnedSymbol.nae false false false
        , NAE3PinnedSymbol.nae true false false
        , NAE3PinnedSymbol.nae false true false
        , NAE3PinnedSymbol.nae false false true
        , NAE3PinnedSymbol.nae true true false
        , NAE3PinnedSymbol.nae true false true
        , NAE3PinnedSymbol.nae false true true
        , NAE3PinnedSymbol.nae true true true
        , NAE3PinnedSymbol.pinFalse
        ]
      nodup := by simp }
  complete := by
    intro s
    cases s with
    | pinFalse => simp
    | nae n₁ n₂ n₃ =>
        cases n₁ <;> cases n₂ <;> cases n₃ <;> simp

/-- Ternary NAE relation over literal values with one polarity bit per coordinate. -/
noncomputable def polarizedNAE3Rel (n₁ n₂ n₃ : Bool) : BoolRel :=
  BoolRel.ofPredicate 3 fun t =>
    StandardRelations.literalValue n₁ (t ⟨0, by decide⟩) ≠
        StandardRelations.literalValue n₂ (t ⟨1, by decide⟩) ∨
      StandardRelations.literalValue n₁ (t ⟨0, by decide⟩) ≠
        StandardRelations.literalValue n₃ (t ⟨2, by decide⟩)

@[simp]
theorem polarizedNAE3Rel_arity (n₁ n₂ n₃ : Bool) :
    (polarizedNAE3Rel n₁ n₂ n₃).arity = 3 :=
  rfl

/-- Relation carried by pinned NAE-3 symbols. -/
noncomputable def nae3PinnedRelationOf : NAE3PinnedSymbol → BoolRel
  | NAE3PinnedSymbol.nae n₁ n₂ n₃ => polarizedNAE3Rel n₁ n₂ n₃
  | NAE3PinnedSymbol.pinFalse => StandardRelations.pinFalseRel

/-- The fixed pinned NAE-3 language. -/
noncomputable def nae3PinnedLanguage : BoolLanguage where
  Symbol := NAE3PinnedSymbol
  finiteSymbol := inferInstance
  relationOf := nae3PinnedRelationOf

/-- The encoded decision problem for pinned NAE-3SAT. -/
noncomputable def nae3PinnedDecisionProblem : EncodedDecisionProblem :=
  boolCSPDecisionProblem nae3PinnedLanguage

/-- A polarized NAE-3 constraint over three SAT literals. -/
def constraintOfLiterals (l₁ l₂ l₃ : Literal) : Constraint nae3PinnedLanguage where
  symbol := NAE3PinnedSymbol.nae l₁.neg l₂.neg l₃.neg
  vars := fun i =>
    match i.val with
    | 0 => l₁.var
    | 1 => l₂.var
    | _ => l₃.var

/-- Unary pinning constraint forcing a variable to false. -/
def pinFalseConstraint (v : Nat) : Constraint nae3PinnedLanguage where
  symbol := NAE3PinnedSymbol.pinFalse
  vars := fun _ => v

theorem constraintOfLiterals_satisfies_iff (l₁ l₂ l₃ : Literal) (a : Assignment) :
    Constraint.Satisfies (constraintOfLiterals l₁ l₂ l₃) a ↔
      l₁.eval a ≠ l₂.eval a ∨ l₁.eval a ≠ l₃.eval a := by
  rcases l₁ with ⟨v₁, n₁⟩
  rcases l₂ with ⟨v₂, n₂⟩
  rcases l₃ with ⟨v₃, n₃⟩
  change
    (polarizedNAE3Rel n₁ n₂ n₃).Holds
        (fun i : Fin (polarizedNAE3Rel n₁ n₂ n₃).arity =>
          a (match i.val with | 0 => v₁ | 1 => v₂ | _ => v₃)) ↔
      ({ var := v₁, neg := n₁ } : Literal).eval a ≠
          ({ var := v₂, neg := n₂ } : Literal).eval a ∨
        ({ var := v₁, neg := n₁ } : Literal).eval a ≠
          ({ var := v₃, neg := n₃ } : Literal).eval a
  cases n₁ <;> cases n₂ <;> cases n₃ <;>
    unfold polarizedNAE3Rel <;>
    rw [BoolRel.holds_ofPredicate_iff] <;>
    simp [Literal.eval,
      StandardRelations.literalValue]

theorem pinFalseConstraint_satisfies_iff (v : Nat) (a : Assignment) :
    Constraint.Satisfies (pinFalseConstraint v) a ↔ a v = false := by
  change StandardRelations.pinFalseRel.Holds (fun _ : Fin 1 => a v) ↔ a v = false
  unfold StandardRelations.pinFalseRel
  rw [BoolRel.holds_ofPredicate_iff]

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

/--
Auxiliary value used by the standard clause gadget.  For ternary clauses this
is the local witness `y = ¬(l₁ ∨ l₂)`; short clauses ignore the auxiliary slot.
-/
def clauseAuxValue (a : Assignment) : Clause → Bool
  | l₁ :: l₂ :: _ => !((l₁.eval a) || (l₂.eval a))
  | _ => false

/--
Translate one 3CNF clause into the pinned polarized NAE-3 language.  Empty
clauses map to an impossible NAE constraint; unit and binary clauses use the
global false variable; ternary clauses use one local auxiliary variable.
-/
def clauseToFormula (falseVar auxVar : Nat) : Clause → Formula nae3PinnedLanguage
  | [] =>
      [constraintOfLiterals (Literal.positive falseVar) (Literal.positive falseVar)
        (Literal.positive falseVar)]
  | [l₁] =>
      [constraintOfLiterals l₁ (Literal.positive falseVar) (Literal.positive falseVar)]
  | [l₁, l₂] =>
      [constraintOfLiterals l₁ l₂ (Literal.positive falseVar)]
  | l₁ :: l₂ :: l₃ :: _ =>
      [ constraintOfLiterals l₁ l₂ (Literal.positive auxVar)
      , constraintOfLiterals (Literal.negative auxVar) l₃ (Literal.positive falseVar)
      ]

def clausesToFormulaAux (falseVar nextAux : Nat) : CNF → Formula nae3PinnedLanguage
  | [] => []
  | c :: cs => clauseToFormula falseVar nextAux c ++ clausesToFormulaAux falseVar (nextAux + 1) cs

/-- First fresh variable reserved for the global false pin. -/
def falseVar (φ : ThreeCNF) : Nat :=
  CNF.varBound φ.clauses

/-- Translate bundled local 3SAT into pinned NAE-3SAT. -/
def threeCNFToNAE3PinnedFormula (φ : ThreeCNF) : Formula nae3PinnedLanguage :=
  pinFalseConstraint (falseVar φ) ::
    clausesToFormulaAux (falseVar φ) (falseVar φ + 1) φ.clauses

theorem clauseToFormula_project {c : Clause} (hlen : c.length ≤ 3)
    {falseVar auxVar : Nat} {a : Assignment}
    (hFalse : a falseVar = false)
    (h : Formula.Satisfies (clauseToFormula falseVar auxVar c) a) :
    Clause.Satisfies c a := by
  cases c with
  | nil =>
      have hc :
          Constraint.Satisfies
            (constraintOfLiterals (Literal.positive falseVar) (Literal.positive falseVar)
              (Literal.positive falseVar)) a := by
        exact h _ (by simp [clauseToFormula])
      have hnae :=
        (constraintOfLiterals_satisfies_iff (Literal.positive falseVar)
          (Literal.positive falseVar) (Literal.positive falseVar) a).1 hc
      simp [Literal.positive, Literal.eval, hFalse] at hnae
  | cons l₁ rest =>
      cases rest with
      | nil =>
          have hc :
              Constraint.Satisfies
                (constraintOfLiterals l₁ (Literal.positive falseVar)
                  (Literal.positive falseVar)) a := by
            exact h _ (by simp [clauseToFormula])
          have hnae :=
            (constraintOfLiterals_satisfies_iff l₁ (Literal.positive falseVar)
              (Literal.positive falseVar) a).1 hc
          have hl : l₁.eval a = true := by
            exact naeUnit_project (l₁.eval a) (by
              simpa [Literal.positive, Literal.eval, hFalse] using hnae)
          exact ⟨l₁, by simp, hl⟩
      | cons l₂ rest₂ =>
          cases rest₂ with
          | nil =>
              have hc :
                  Constraint.Satisfies
                    (constraintOfLiterals l₁ l₂ (Literal.positive falseVar)) a := by
                exact h _ (by simp [clauseToFormula])
              have hnae :=
                (constraintOfLiterals_satisfies_iff l₁ l₂ (Literal.positive falseVar) a).1 hc
              rcases naeBinary_project (l₁.eval a) (l₂.eval a) (by
                simpa [Literal.positive, Literal.eval, hFalse] using hnae) with h₁ | h₂
              · exact ⟨l₁, by simp, h₁⟩
              · exact ⟨l₂, by simp, h₂⟩
          | cons l₃ rest₃ =>
              cases rest₃ with
              | nil =>
                  have hfirst :
                      Constraint.Satisfies
                        (constraintOfLiterals l₁ l₂ (Literal.positive auxVar)) a := by
                    exact h _ (by simp [clauseToFormula])
                  have hsecond :
                      Constraint.Satisfies
                        (constraintOfLiterals (Literal.negative auxVar) l₃
                          (Literal.positive falseVar)) a := by
                    exact h _ (by simp [clauseToFormula])
                  have hnae₁ :=
                    (constraintOfLiterals_satisfies_iff l₁ l₂ (Literal.positive auxVar) a).1 hfirst
                  have hnae₂ :=
                    (constraintOfLiterals_satisfies_iff (Literal.negative auxVar) l₃
                      (Literal.positive falseVar) a).1 hsecond
                  rcases naeTernary_project (l₁.eval a) (l₂.eval a) (l₃.eval a) (a auxVar)
                    (by simpa [Literal.positive, Literal.eval] using hnae₁)
                    (by simpa [Literal.positive, Literal.negative, Literal.eval, hFalse] using hnae₂)
                    with h₁ | h₂ | h₃
                  · exact ⟨l₁, by simp, h₁⟩
                  · exact ⟨l₂, by simp, h₂⟩
                  · exact ⟨l₃, by simp, h₃⟩
              | cons _ _ =>
                  simp at hlen

theorem clauseToFormula_extend {c : Clause} (hlen : c.length ≤ 3)
    {falseVar auxVar : Nat} {a b : Assignment}
    (hFalse : b falseVar = false)
    (hAux : b auxVar = clauseAuxValue a c)
    (hAgree : ∀ l ∈ c, b l.var = a l.var)
    (hSat : Clause.Satisfies c a) :
    Formula.Satisfies (clauseToFormula falseVar auxVar c) b := by
  cases c with
  | nil =>
      rcases hSat with ⟨l, hl, _⟩
      cases hl
  | cons l₁ rest =>
      cases rest with
      | nil =>
          intro d hd
          have hdEq :
              d = constraintOfLiterals l₁ (Literal.positive falseVar)
                (Literal.positive falseVar) := by
            simpa [clauseToFormula] using hd
          subst d
          rcases hSat with ⟨l, hl, hlEval⟩
          have hl₁ : l = l₁ := by simpa using hl
          subst l
          have hEval : l₁.eval b = true := by
            have heq := SAT.Clause.literal_eval_eq_of_var_eq l₁ (hAgree l₁ (by simp))
            simpa [heq] using hlEval
          have hFalseLit : (Literal.positive falseVar).eval b = false := by
            simp [Literal.positive, Literal.eval, hFalse]
          exact (constraintOfLiterals_satisfies_iff l₁ (Literal.positive falseVar)
            (Literal.positive falseVar) b).2 (by
              simpa [hFalseLit] using naeUnit_extend (l₁.eval b) hEval)
      | cons l₂ rest₂ =>
          cases rest₂ with
          | nil =>
              intro d hd
              have hdEq : d = constraintOfLiterals l₁ l₂ (Literal.positive falseVar) := by
                simpa [clauseToFormula] using hd
              subst d
              rcases hSat with ⟨l, hl, hlEval⟩
              have h₁eq : l₁.eval b = l₁.eval a :=
                SAT.Clause.literal_eval_eq_of_var_eq l₁ (hAgree l₁ (by simp))
              have h₂eq : l₂.eval b = l₂.eval a :=
                SAT.Clause.literal_eval_eq_of_var_eq l₂ (hAgree l₂ (by simp))
              have hFalseLit : (Literal.positive falseVar).eval b = false := by
                simp [Literal.positive, Literal.eval, hFalse]
              exact (constraintOfLiterals_satisfies_iff l₁ l₂ (Literal.positive falseVar) b).2
                (by
                  simpa [hFalseLit] using
                    naeBinary_extend (l₁.eval b) (l₂.eval b) (by
                  rcases List.mem_cons.mp hl with h₁ | htail
                  · subst l
                    exact Or.inl (by simpa [h₁eq] using hlEval)
                  · have h₂ : l = l₂ := by simpa using htail
                    subst l
                    exact Or.inr (by simpa [h₂eq] using hlEval)))
          | cons l₃ rest₃ =>
              cases rest₃ with
              | nil =>
                  intro d hd
                  have h₁eq : l₁.eval b = l₁.eval a :=
                    SAT.Clause.literal_eval_eq_of_var_eq l₁ (hAgree l₁ (by simp))
                  have h₂eq : l₂.eval b = l₂.eval a :=
                    SAT.Clause.literal_eval_eq_of_var_eq l₂ (hAgree l₂ (by simp))
                  have h₃eq : l₃.eval b = l₃.eval a :=
                    SAT.Clause.literal_eval_eq_of_var_eq l₃ (hAgree l₃ (by simp))
                  have hAuxLit : (Literal.positive auxVar).eval b = !((l₁.eval b) || (l₂.eval b)) := by
                    simp only [Literal.eval_positive]
                    rw [hAux]
                    simp [clauseAuxValue]
                    rw [← h₁eq, ← h₂eq]
                  have hFalseLit : (Literal.positive falseVar).eval b = false := by
                    simp [Literal.positive, Literal.eval, hFalse]
                  have hNegAuxLit :
                      (Literal.negative auxVar).eval b = !(!((l₁.eval b) || (l₂.eval b))) := by
                    simp only [Literal.eval_negative]
                    rw [hAux]
                    simp [clauseAuxValue]
                    rw [← h₁eq, ← h₂eq]
                  have hdCases :
                      d = constraintOfLiterals l₁ l₂ (Literal.positive auxVar) ∨
                        d = constraintOfLiterals (Literal.negative auxVar) l₃
                          (Literal.positive falseVar) := by
                    simpa [clauseToFormula] using hd
                  rcases hdCases with hfirst | hsecond
                  · subst d
                    exact (constraintOfLiterals_satisfies_iff l₁ l₂
                      (Literal.positive auxVar) b).2 (by
                        simpa [hAuxLit] using
                          naeTernary_first_extend (l₁.eval b) (l₂.eval b))
                  · subst d
                    exact (constraintOfLiterals_satisfies_iff (Literal.negative auxVar) l₃
                      (Literal.positive falseVar) b).2 (by
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
                            l₁.eval b = true ∨ l₂.eval b = true ∨ l₃.eval b = true := by
                          rcases hSatBool with h₁sat | h₂sat | h₃sat
                          · exact Or.inl (by simpa [h₁eq] using h₁sat)
                          · exact Or.inr (Or.inl (by simpa [h₂eq] using h₂sat))
                          · exact Or.inr (Or.inr (by simpa [h₃eq] using h₃sat))
                        simpa [hNegAuxLit, hFalseLit] using
                          naeTernary_second_extend' (l₁.eval b) (l₂.eval b) (l₃.eval b) hSatBoolB)
              | cons _ _ =>
                  simp at hlen

def AuxValues : Nat → CNF → Assignment → Assignment → Prop
  | _, [], _, _ => True
  | nextAux, c :: cs, a, b =>
      b nextAux = clauseAuxValue a c ∧ AuxValues (nextAux + 1) cs a b

def extendAssignment (falseVar nextAux : Nat) : CNF → Assignment → Assignment
  | [], a => fun v => if v = falseVar then false else a v
  | c :: cs, a =>
      SAT.Clause.setVar (extendAssignment falseVar (nextAux + 1) cs a)
        nextAux (clauseAuxValue a c)

theorem extendAssignment_pinFalse {clauses : CNF} {a : Assignment}
    {falseVar nextAux : Nat} (hFresh : falseVar < nextAux) :
    extendAssignment falseVar nextAux clauses a falseVar = false := by
  induction clauses generalizing nextAux with
  | nil =>
      simp [extendAssignment]
  | cons c cs ih =>
      simp [extendAssignment, SAT.Clause.setVar_ne (ne_of_lt hFresh),
        ih (Nat.lt_trans hFresh (Nat.lt_succ_self nextAux))]

theorem extendAssignment_agrees_below {clauses : CNF} {a : Assignment}
    {falseVar nextAux v : Nat} (hv : v < falseVar) (hFresh : falseVar < nextAux) :
    extendAssignment falseVar nextAux clauses a v = a v := by
  induction clauses generalizing nextAux with
  | nil =>
      simp [extendAssignment, ne_of_lt hv]
  | cons c cs ih =>
      have hvnext : v ≠ nextAux := ne_of_lt (Nat.lt_trans hv hFresh)
      simp [extendAssignment, SAT.Clause.setVar_ne hvnext,
        ih (Nat.lt_trans hFresh (Nat.lt_succ_self nextAux))]

theorem auxValues_setVar_before {clauses : CNF} {a b : Assignment}
    {setAt nextAux : Nat} {value : Bool} (hBefore : setAt < nextAux) :
    AuxValues nextAux clauses a (SAT.Clause.setVar b setAt value) ↔
      AuxValues nextAux clauses a b := by
  induction clauses generalizing nextAux with
  | nil =>
      simp [AuxValues]
  | cons c cs ih =>
      have hne : nextAux ≠ setAt := ne_of_gt hBefore
      constructor
      · intro h
        exact ⟨by simpa [SAT.Clause.setVar_ne hne] using h.1,
          (ih (Nat.lt_trans hBefore (Nat.lt_succ_self nextAux))).1 h.2⟩
      · intro h
        exact ⟨by simpa [SAT.Clause.setVar_ne hne] using h.1,
          (ih (Nat.lt_trans hBefore (Nat.lt_succ_self nextAux))).2 h.2⟩

theorem extendAssignment_auxValues {clauses : CNF} {a : Assignment}
    {falseVar nextAux : Nat} :
    AuxValues nextAux clauses a (extendAssignment falseVar nextAux clauses a) := by
  induction clauses generalizing nextAux with
  | nil =>
      trivial
  | cons c cs ih =>
      constructor
      · simp [extendAssignment, SAT.Clause.setVar_self]
      · have htail := ih (nextAux := nextAux + 1)
        exact (auxValues_setVar_before (clauses := cs) (a := a)
          (b := extendAssignment falseVar (nextAux + 1) cs a)
          (setAt := nextAux) (nextAux := nextAux + 1)
          (value := clauseAuxValue a c) (Nat.lt_succ_self nextAux)).2 htail

theorem clausesToFormulaAux_project {clauses : CNF} {falseVar nextAux : Nat}
    {a : Assignment} (hThree : CNF.IsThreeCNF clauses)
    (hFalse : a falseVar = false)
    (h : Formula.Satisfies (clausesToFormulaAux falseVar nextAux clauses) a) :
    CNF.Satisfies clauses a := by
  induction clauses generalizing nextAux with
  | nil =>
      intro c hc
      cases hc
  | cons c cs ih =>
      intro d hd
      have hcLen : c.length ≤ 3 := hThree c (by simp)
      have hcsThree : CNF.IsThreeCNF cs := by
        intro e he
        exact hThree e (by simp [he])
      have hBlock :
          Formula.Satisfies (clauseToFormula falseVar nextAux c) a := by
        intro e he
        exact h e (by simp [clausesToFormulaAux, he])
      have hTail :
          Formula.Satisfies (clausesToFormulaAux falseVar (nextAux + 1) cs) a := by
        intro e he
        exact h e (by simp [clausesToFormulaAux, he])
      rcases List.mem_cons.mp hd with rfl | hds
      · exact clauseToFormula_project hcLen hFalse hBlock
      · exact ih (nextAux := nextAux + 1) hcsThree hTail d hds

theorem clausesToFormulaAux_extend_of_auxValues {clauses : CNF} {falseVar nextAux : Nat}
    {a b : Assignment} (hThree : CNF.IsThreeCNF clauses)
    (hFalse : b falseVar = false)
    (hAgree : ∀ c ∈ clauses, ∀ l ∈ c, b l.var = a l.var)
    (hAux : AuxValues nextAux clauses a b)
    (hSat : CNF.Satisfies clauses a) :
    Formula.Satisfies (clausesToFormulaAux falseVar nextAux clauses) b := by
  induction clauses generalizing nextAux with
  | nil =>
      intro c hc
      cases hc
  | cons c cs ih =>
      have hcLen : c.length ≤ 3 := hThree c (by simp)
      have hcsThree : CNF.IsThreeCNF cs := by
        intro e he
        exact hThree e (by simp [he])
      have hAuxHead : b nextAux = clauseAuxValue a c := hAux.1
      have hAuxTail : AuxValues (nextAux + 1) cs a b := hAux.2
      have hBlock := clauseToFormula_extend hcLen hFalse hAuxHead
        (by intro l hl; exact hAgree c (by simp) l hl) (hSat c (by simp))
      have hTail := ih (nextAux := nextAux + 1) hcsThree
        (by
          intro d hd l hl
          exact hAgree d (by simp [hd]) l hl)
        hAuxTail
        (by
          intro d hd
          exact hSat d (by simp [hd]))
      intro d hd
      rcases List.mem_append.mp (by simpa [clausesToFormulaAux] using hd) with hleft | hright
      · exact hBlock d hleft
      · exact hTail d hright

theorem threeCNFToNAE3PinnedFormula_satisfiable_iff (φ : ThreeCNF) :
    Formula.Satisfiable (threeCNFToNAE3PinnedFormula φ) ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨a, h⟩
    have hPin :
        Constraint.Satisfies (pinFalseConstraint (falseVar φ)) a := by
      exact h _ (by simp [threeCNFToNAE3PinnedFormula])
    have hFalse : a (falseVar φ) = false :=
      (pinFalseConstraint_satisfies_iff (falseVar φ) a).1 hPin
    have hTail :
        Formula.Satisfies (clausesToFormulaAux (falseVar φ) (falseVar φ + 1) φ.clauses) a := by
      intro c hc
      exact h c (by simp [threeCNFToNAE3PinnedFormula, hc])
    exact ⟨a, clausesToFormulaAux_project φ.isThree hFalse hTail⟩
  · rintro ⟨a, hSat⟩
    let b := extendAssignment (falseVar φ) (falseVar φ + 1) φ.clauses a
    refine ⟨b, ?_⟩
    intro c hc
    rcases List.mem_cons.mp (by simpa [threeCNFToNAE3PinnedFormula] using hc) with hpin | htail
    · subst c
      exact (pinFalseConstraint_satisfies_iff (falseVar φ) b).2
        (extendAssignment_pinFalse (clauses := φ.clauses) (a := a)
          (Nat.lt_succ_self (falseVar φ)))
    · have hFalse : b (falseVar φ) = false :=
        extendAssignment_pinFalse (clauses := φ.clauses) (a := a)
          (Nat.lt_succ_self (falseVar φ))
      have hAgree : ∀ d ∈ φ.clauses, ∀ l ∈ d, b l.var = a l.var := by
        intro d hd l hl
        exact extendAssignment_agrees_below
          (clauses := φ.clauses) (a := a)
          (SAT.CNF.clause_vars_lt_varBound hd l hl)
          (Nat.lt_succ_self (falseVar φ))
      have hAux : AuxValues (falseVar φ + 1) φ.clauses a b :=
        extendAssignment_auxValues (clauses := φ.clauses) (a := a)
      exact clausesToFormulaAux_extend_of_auxValues φ.isThree hFalse hAgree hAux hSat c htail

/-- Semantic reverse reduction from local 3SAT to pinned NAE-3SAT. -/
noncomputable def threeSATToNAE3PinnedReduction :
    SemanticReduction SAT.threeSATDecisionProblem nae3PinnedDecisionProblem where
  f := threeCNFToNAE3PinnedFormula
  correct := by
    intro φ
    exact (threeCNFToNAE3PinnedFormula_satisfiable_iff φ).symm

theorem constraintOfLiterals_encodedLength (l₁ l₂ l₃ : Literal) :
    (Encoding.encodeConstraint (constraintOfLiterals l₁ l₂ l₃)).length =
      l₁.var + l₂.var + l₃.var + 8 := by
  rw [Encoding.encodeConstraint_length]
  simp only [constraintOfLiterals, nae3PinnedLanguage, nae3PinnedRelationOf,
    polarizedNAE3Rel_arity, List.map_ofFn]
  conv_lhs =>
    enter [2, 1]
    rw [List.ofFn_succ]
    rw [List.ofFn_succ]
    rw [List.ofFn_succ]
  simp
  omega

theorem pinFalseConstraint_encodedLength (v : Nat) :
    (Encoding.encodeConstraint (pinFalseConstraint v)).length = v + 4 := by
  rw [Encoding.encodeConstraint_length]
  simp [pinFalseConstraint, nae3PinnedLanguage, nae3PinnedRelationOf,
    StandardRelations.pinFalseRel]
  omega

theorem clauseToFormula_encodedLength_le {c : Clause} (hlen : c.length ≤ 3)
    {falseVar auxVar B : Nat}
    (hFalse : falseVar ≤ B) (hAux : auxVar ≤ B)
    (hVars : ∀ l ∈ c, l.var ≤ B) :
    (Encoding.encodeFormula (clauseToFormula falseVar auxVar c)).length ≤
      2 * (3 * B + 8) := by
  cases c with
  | nil =>
      simp [clauseToFormula, constraintOfLiterals_encodedLength, Literal.positive]
      omega
  | cons l₁ rest =>
      cases rest with
      | nil =>
          have h₁ : l₁.var ≤ B := hVars l₁ (by simp)
          simp [clauseToFormula, constraintOfLiterals_encodedLength, Literal.positive]
          omega
      | cons l₂ rest₂ =>
          cases rest₂ with
          | nil =>
              have h₁ : l₁.var ≤ B := hVars l₁ (by simp)
              have h₂ : l₂.var ≤ B := hVars l₂ (by simp)
              simp [clauseToFormula, constraintOfLiterals_encodedLength, Literal.positive]
              omega
          | cons l₃ rest₃ =>
              cases rest₃ with
              | nil =>
                  have h₁ : l₁.var ≤ B := hVars l₁ (by simp)
                  have h₂ : l₂.var ≤ B := hVars l₂ (by simp)
                  have h₃ : l₃.var ≤ B := hVars l₃ (by simp)
                  simp [clauseToFormula, constraintOfLiterals_encodedLength, Literal.positive,
                    Literal.negative]
                  omega
              | cons _ _ =>
                  simp at hlen

theorem clausesToFormulaAux_encodedLength_le {clauses : CNF}
    (hThree : CNF.IsThreeCNF clauses) {falseVar nextAux B : Nat}
    (hFalse : falseVar ≤ B)
    (hAux : ∀ i, nextAux ≤ i → i < nextAux + clauses.length → i ≤ B)
    (hVars : ∀ c ∈ clauses, ∀ l ∈ c, l.var ≤ B) :
    (Encoding.encodeFormula (clausesToFormulaAux falseVar nextAux clauses)).length ≤
      2 * clauses.length * (3 * B + 8) := by
  induction clauses generalizing nextAux with
  | nil =>
      simp [clausesToFormulaAux]
  | cons c cs ih =>
      have hcLen : c.length ≤ 3 := hThree c (by simp)
      have hcsThree : CNF.IsThreeCNF cs := by
        intro d hd
        exact hThree d (by simp [hd])
      have hAuxHead : nextAux ≤ B := hAux nextAux (Nat.le_refl nextAux) (by simp)
      have hBlock := clauseToFormula_encodedLength_le (c := c) hcLen hFalse hAuxHead
        (by intro l hl; exact hVars c (by simp) l hl)
      have hTail := ih (nextAux := nextAux + 1) hcsThree
        (by
          intro i hiLower hiUpper
          exact hAux i (Nat.le_trans (Nat.le_succ nextAux) hiLower)
            (by simp at hiUpper ⊢; omega))
        (by intro d hd l hl; exact hVars d (by simp [hd]) l hl)
      simp [clausesToFormulaAux, Encoding.encodeFormula, List.length_flatMap] at hBlock hTail ⊢
      calc
        (List.map (fun a => (Encoding.encodeConstraint a).length)
              (clauseToFormula falseVar nextAux c)).sum +
            (List.map (fun a => (Encoding.encodeConstraint a).length)
              (clausesToFormulaAux falseVar (nextAux + 1) cs)).sum
            ≤ 2 * (3 * B + 8) + 2 * cs.length * (3 * B + 8) :=
          Nat.add_le_add hBlock hTail
        _ = 2 * (cs.length + 1) * (3 * B + 8) := by ring

theorem literal_var_lt_encodeClause_length {c : Clause} {l : Literal} (hl : l ∈ c) :
    l.var < (ThreeSATEncoding.encodeClause c).length := by
  have hmem : (ThreeSATEncoding.encodeLiteral l).length ∈
      (c.map fun x => (ThreeSATEncoding.encodeLiteral x).length) := by
    exact List.mem_map.mpr ⟨l, hl, rfl⟩
  have hle : (ThreeSATEncoding.encodeLiteral l).length ≤
      (c.map fun x => (ThreeSATEncoding.encodeLiteral x).length).sum :=
    List.le_sum_of_mem hmem
  simp [ThreeSATEncoding.encodeClause, ThreeSATEncoding.encodeLiteral,
    ThreeSATEncoding.encodeNat, EncodedType.nat, List.length_flatMap] at hle ⊢
  omega

theorem threeCNF_varBound_le_inputSize (φ : ThreeCNF) :
    falseVar φ ≤ SAT.threeSATDecisionProblem.Instance.inputSize φ := by
  unfold falseVar
  change CNF.varBound φ.clauses ≤ (ThreeSATEncoding.encodeThreeCNF φ).length
  exact CNF.varBound_le_of_vars_lt φ.clauses (ThreeSATEncoding.encodeThreeCNF φ).length
    (by
      intro c hc l hl
      have hLit : l.var < (ThreeSATEncoding.encodeClause c).length :=
        literal_var_lt_encodeClause_length hl
      have hBlock :
          (ThreeSATEncoding.encodeClause c).length ≤
            (ThreeSATEncoding.encodeThreeCNF φ).length := by
        unfold ThreeSATEncoding.encodeThreeCNF
        rw [List.length_flatMap]
        exact List.le_sum_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)
      exact Nat.lt_of_lt_of_le hLit hBlock)

theorem cnf_clauseLength_le_encodeCNF (clauses : CNF) :
    clauses.length ≤ (ThreeSATEncoding.encodeCNF clauses).length := by
  induction clauses with
  | nil =>
      simp [ThreeSATEncoding.encodeCNF]
  | cons c cs ih =>
      have hc : 1 ≤ (ThreeSATEncoding.encodeClause c).length := by
        simp [ThreeSATEncoding.encodeClause]
      rw [ThreeSATEncoding.encodeCNF_cons, List.length_append, List.length_cons]
      omega

theorem threeCNF_clauseLength_le_inputSize (φ : ThreeCNF) :
    φ.clauses.length ≤ SAT.threeSATDecisionProblem.Instance.inputSize φ := by
  change φ.clauses.length ≤ (ThreeSATEncoding.encodeThreeCNF φ).length
  simpa [ThreeSATEncoding.encodeThreeCNF_eq_encodeCNF] using
    cnf_clauseLength_le_encodeCNF φ.clauses

theorem threeCNFToNAE3PinnedFormula_encodedLength_le_quadratic (φ : ThreeCNF) :
    (Encoding.encodeFormula (threeCNFToNAE3PinnedFormula φ)).length ≤
      40 * (SAT.threeSATDecisionProblem.Instance.inputSize φ + 1) ^ 2 := by
  let n := SAT.threeSATDecisionProblem.Instance.inputSize φ
  let B := 2 * (n + 1)
  have hFalseVarInput : falseVar φ ≤ n := by
    unfold n
    exact threeCNF_varBound_le_inputSize φ
  have hFalseVar : falseVar φ ≤ B := by
    unfold B
    omega
  have hClauseLen : φ.clauses.length ≤ n := by
    unfold n
    exact threeCNF_clauseLength_le_inputSize φ
  have hAuxBound :
      ∀ i, falseVar φ + 1 ≤ i → i < falseVar φ + 1 + φ.clauses.length → i ≤ B := by
    intro i _hiLower hiUpper
    have hiLe : i ≤ falseVar φ + φ.clauses.length := Nat.le_of_lt_succ (by omega)
    calc
      i ≤ falseVar φ + φ.clauses.length := hiLe
      _ ≤ n + n := Nat.add_le_add hFalseVarInput hClauseLen
      _ ≤ 2 * (n + 1) := by omega
  have hVars : ∀ c ∈ φ.clauses, ∀ l ∈ c, l.var ≤ B := by
    intro c hc l hl
    have hlt := CNF.clause_vars_lt_varBound hc l hl
    unfold falseVar at hFalseVar
    omega
  have hTail := clausesToFormulaAux_encodedLength_le φ.isThree
    (falseVar := falseVar φ) (nextAux := falseVar φ + 1) (B := B)
    hFalseVar hAuxBound hVars
  have hPin := pinFalseConstraint_encodedLength (falseVar φ)
  simp [threeCNFToNAE3PinnedFormula, Encoding.encodeFormula, List.length_flatMap] at hTail ⊢
  rw [hPin]
  have hMain :
      falseVar φ + 4 + 2 * φ.clauses.length * (3 * B + 8) ≤ 40 * (n + 1) ^ 2 := by
    unfold B
    let A := n + 1
    have hApos : 1 ≤ A := by unfold A; omega
    have hmA : φ.clauses.length ≤ A := by unfold A; omega
    have hpin : falseVar φ + 4 ≤ 4 * A := by unfold A; omega
    have hpinSq : falseVar φ + 4 ≤ 4 * A ^ 2 := by
      have hmulA : 4 * A ≤ 4 * (A * A) := by
        exact Nat.mul_le_mul_left 4 (by simpa using Nat.mul_le_mul_left A hApos)
      calc
        falseVar φ + 4 ≤ 4 * A := hpin
        _ ≤ 4 * (A * A) := hmulA
        _ = 4 * A ^ 2 := by rw [pow_two]
    have hfactor : 3 * (2 * A) + 8 ≤ 14 * A := by omega
    have hmul :
        2 * φ.clauses.length * (3 * (2 * A) + 8) ≤ 2 * A * (14 * A) := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hmA) hfactor
    calc
      falseVar φ + 4 + 2 * φ.clauses.length * (3 * (2 * A) + 8)
          ≤ falseVar φ + 4 + 2 * A * (14 * A) := Nat.add_le_add_left hmul _
      _ = falseVar φ + 4 + 28 * A ^ 2 := by ring
      _ ≤ 4 * A ^ 2 + 28 * A ^ 2 := Nat.add_le_add_right hpinSq _
      _ ≤ 40 * A ^ 2 := by omega
  exact (Nat.add_le_add_left hTail (falseVar φ + 4)).trans hMain

theorem threeCNFToNAE3PinnedFormula_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : ThreeCNF => SAT.threeSATDecisionProblem.Instance.inputSize φ)
      (fun ψ : Formula nae3PinnedLanguage => nae3PinnedDecisionProblem.Instance.inputSize ψ)
      threeCNFToNAE3PinnedFormula :=
  PolynomialSizeBound.intro_with 2 160 40 (by
    intro φ
    have h := threeCNFToNAE3PinnedFormula_encodedLength_le_quadratic φ
    calc
      nae3PinnedDecisionProblem.Instance.inputSize (threeCNFToNAE3PinnedFormula φ)
          ≤ 40 * (SAT.threeSATDecisionProblem.Instance.inputSize φ + 1) ^ 2 := by
        simpa [EncodedType.inputSize, nae3PinnedDecisionProblem, boolCSPDecisionProblem,
          boolCSPSatLike, formulaEncodedType] using h
      _ ≤ 40 *
          (4 * (SAT.threeSATDecisionProblem.Instance.inputSize φ) ^ 2 + 1) := by
        exact Nat.mul_le_mul_left 40
          (Formula.add_one_sq_le_four_sq_add_one
            (SAT.threeSATDecisionProblem.Instance.inputSize φ))
      _ = 160 * (SAT.threeSATDecisionProblem.Instance.inputSize φ) ^ 2 + 40 := by
        ring)

/-- Project-local costed reverse reduction from local 3SAT to pinned NAE-3SAT. -/
noncomputable def threeSATToNAE3PinnedCostedReduction :
    CostedReduction SAT.threeSATDecisionProblem nae3PinnedDecisionProblem :=
  CostedReduction.ofCostedMap
    threeCNFToNAE3PinnedFormula
    threeSATToNAE3PinnedReduction.correct
    (CostedMap.of_encodedPolynomialSizeBound
      threeCNFToNAE3PinnedFormula_polynomialSizeBound)

/-- Costed-model Karp reverse reduction from local 3SAT to pinned NAE-3SAT. -/
noncomputable def threeSATToNAE3PinnedKarpReduction :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem nae3PinnedDecisionProblem :=
  threeSATToNAE3PinnedCostedReduction.toKarpReductionM

end NAE3SATPinned
end Hardness
end CSP
end ComplexityReduction
