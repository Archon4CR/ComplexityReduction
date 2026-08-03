/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.CSP.FiniteDomain.BoolBridge
import ComplexityReduction.CSP.Polymorphisms.Bool

/-!
Finite-domain polymorphism predicates for CSP languages.

An `n`-ary operation acts coordinatewise on `n` accepted tuples of a relation.
Preservation of every relation symbol is the local algebraic predicate used by
finite-template CSP classification arguments.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain

/-- An `n`-ary operation on a finite-domain carrier. -/
abbrev Operation (D : Type) (n : Nat) : Type :=
  (Fin n → D) → D

namespace Operation

/-- Apply an operation coordinatewise to a family of tuples. -/
def applyTuple {D : Type} {n k : Nat} (op : Operation D n)
    (rows : Fin n → Tuple D k) : Tuple D k :=
  fun i => op fun j => rows j i

/-- Apply an operation pointwise to a family of assignments. -/
def applyAssignment {D : Type} {n : Nat} (op : Operation D n)
    (rows : Fin n → Assignment D) : Assignment D :=
  fun x => op fun j => rows j x

@[simp]
theorem applyTuple_apply {D : Type} {n k : Nat} (op : Operation D n)
    (rows : Fin n → Tuple D k) (i : Fin k) :
    applyTuple op rows i = op (fun j => rows j i) :=
  rfl

@[simp]
theorem applyAssignment_apply {D : Type} {n : Nat} (op : Operation D n)
    (rows : Fin n → Assignment D) (x : Nat) :
    applyAssignment op rows x = op (fun j => rows j x) :=
  rfl

/-- The nullary false operation on `Bool`. -/
def boolFalse : Operation Bool 0 :=
  fun _ => false

/-- The nullary true operation on `Bool`. -/
def boolTrue : Operation Bool 0 :=
  fun _ => true

/-- Binary Boolean conjunction as a finite-domain operation. -/
def boolAnd : Operation Bool 2 :=
  fun v => v 0 && v 1

/-- Binary Boolean disjunction as a finite-domain operation. -/
def boolOr : Operation Bool 2 :=
  fun v => v 0 || v 1

/-- Ternary Boolean xor as a finite-domain operation. -/
def boolTernaryXor : Operation Bool 3 :=
  fun v => xor (xor (v 0) (v 1)) (v 2)

/-- Ternary Boolean majority as a finite-domain operation. -/
def boolMajority : Operation Bool 3 :=
  fun v => (v 0 && v 1) || (v 0 && v 2) || (v 1 && v 2)

/-- Unary Boolean complement as a finite-domain operation. -/
def boolComplement : Operation Bool 1 :=
  fun v => !(v 0)

/-- An operation is idempotent when constant input rows return that value. -/
def IsIdempotent {D : Type} {n : Nat} (op : Operation D n) : Prop :=
  ∀ x : D, op (fun _ => x) = x

/-- A ternary operation is a majority operation when any two equal inputs determine output. -/
def IsMajority {D : Type} (op : Operation D 3) : Prop :=
  ∀ x y : D,
    op (fun i => if i = (0 : Fin 3) then y else x) = x ∧
      op (fun i => if i = (1 : Fin 3) then y else x) = x ∧
        op (fun i => if i = (2 : Fin 3) then y else x) = x

/-- A ternary operation is a minority operation when the unique differing input is returned. -/
def IsMinority {D : Type} (op : Operation D 3) : Prop :=
  ∀ x y : D,
    op (fun i => if i = (0 : Fin 3) then y else x) = y ∧
      op (fun i => if i = (1 : Fin 3) then y else x) = y ∧
        op (fun i => if i = (2 : Fin 3) then y else x) = y

/-- A ternary operation satisfies the Mal'tsev identities. -/
def IsMaltsev {D : Type} (op : Operation D 3) : Prop :=
  ∀ x y : D,
    op (fun i =>
      if i = (0 : Fin 3) then x else y) = x ∧
    op (fun i =>
      if i = (2 : Fin 3) then x else y) = x

/-- Near-unanimity operation: replacing one coordinate by `y` still returns `x`. -/
def IsNearUnanimity {D : Type} {n : Nat} (op : Operation D n) : Prop :=
  0 < n ∧ ∀ x y : D, ∀ i : Fin n, op (fun j => if j = i then y else x) = x

/-- Semilattice-like binary operation: idempotent, commutative, and associative. -/
def IsSemilatticeLike {D : Type} (op : Operation D 2) : Prop :=
  IsIdempotent op ∧
    (∀ x y : D,
      op (fun i => if i = (0 : Fin 2) then x else y) =
        op (fun i => if i = (0 : Fin 2) then y else x)) ∧
    (∀ x y z : D,
      op (fun i =>
        if i = (0 : Fin 2) then
          op (fun j => if j = (0 : Fin 2) then x else y)
        else z) =
      op (fun i =>
        if i = (0 : Fin 2) then x
        else op (fun j => if j = (0 : Fin 2) then y else z)))

theorem boolAnd_isIdempotent :
    IsIdempotent boolAnd := by
  intro x
  cases x <;> rfl

theorem boolOr_isIdempotent :
    IsIdempotent boolOr := by
  intro x
  cases x <;> rfl

theorem boolAnd_isSemilatticeLike :
    IsSemilatticeLike boolAnd := by
  constructor
  · exact boolAnd_isIdempotent
  constructor
  · intro x y
    cases x <;> cases y <;> rfl
  · intro x y z
    cases x <;> cases y <;> cases z <;> rfl

theorem boolOr_isSemilatticeLike :
    IsSemilatticeLike boolOr := by
  constructor
  · exact boolOr_isIdempotent
  constructor
  · intro x y
    cases x <;> cases y <;> rfl
  · intro x y z
    cases x <;> cases y <;> cases z <;> rfl

theorem boolMajority_isMajority :
    IsMajority boolMajority := by
  intro x y
  cases x <;> cases y <;> simp [boolMajority]

theorem boolMajority_isNearUnanimity :
    IsNearUnanimity boolMajority := by
  constructor
  · omega
  · intro x y i
    fin_cases i <;> cases x <;> cases y <;> simp [boolMajority]

theorem boolTernaryXor_isMinority :
    IsMinority boolTernaryXor := by
  intro x y
  cases x <;> cases y <;> simp [boolTernaryXor]

theorem boolTernaryXor_isMaltsev :
    IsMaltsev boolTernaryXor := by
  intro x y
  cases x <;> cases y <;> simp [boolTernaryXor]

end Operation

/-- An operation preserves a relation when the coordinatewise output is accepted. -/
def PreservesRel {D : Type} {n : Nat} (op : Operation D n) (R : Rel D) : Prop :=
  ∀ rows : Fin n → Tuple D R.arity,
    (∀ j, R.Holds (rows j)) → R.Holds (Operation.applyTuple op rows)

/-- An operation preserves every relation symbol in a finite-domain language. -/
def PreservesLanguage {D : Type} {n : Nat} (op : Operation D n)
    (Γ : Language D) : Prop :=
  ∀ s : Γ.Symbol, PreservesRel op (Γ.relationOf s)

/-- A proof-bearing polymorphism of a finite-domain language. -/
structure Polymorphism {D : Type} (Γ : Language D) (n : Nat) where
  op : Operation D n
  preserves : PreservesLanguage op Γ

/-- Compatibility alias: every relation in the language is preserved by `op`. -/
def AllRelationsPreserved {D : Type} (Γ : Language D) {n : Nat}
    (op : Operation D n) : Prop :=
  PreservesLanguage op Γ

namespace Polymorphism

theorem preservesRel {D : Type} {Γ : Language D} {n : Nat}
    (p : Polymorphism Γ n) (s : Γ.Symbol) :
    PreservesRel p.op (Γ.relationOf s) :=
  p.preserves s

end Polymorphism

namespace BoolTransport

theorem preservesRel_boolFalse_iff_isZeroValid (R : BoolRel) :
    PreservesRel Operation.boolFalse (BoolBridge.relOfBoolRel R) ↔
      ComplexityReduction.CSP.IsZeroValid R := by
  constructor
  · intro h
    let rows : Fin 0 → Tuple Bool R.arity := fun j => Fin.elim0 j
    have hRows : ∀ j, (BoolBridge.relOfBoolRel R).Holds (rows j) := by
      intro j
      exact Fin.elim0 j
    have hOut := h rows hRows
    have hEq :
        Operation.applyTuple Operation.boolFalse rows =
          BoolTuple.constFalse R.arity := by
      funext i
      rfl
    simpa [ComplexityReduction.CSP.IsZeroValid, BoolBridge.relOfBoolRel_holds_iff, hEq]
      using hOut
  · intro h rows _hRows
    simpa [ComplexityReduction.CSP.IsZeroValid, BoolBridge.relOfBoolRel_holds_iff,
      Operation.applyTuple, Operation.boolFalse, BoolTuple.constFalse] using h

theorem preservesRel_boolTrue_iff_isOneValid (R : BoolRel) :
    PreservesRel Operation.boolTrue (BoolBridge.relOfBoolRel R) ↔
      ComplexityReduction.CSP.IsOneValid R := by
  constructor
  · intro h
    let rows : Fin 0 → Tuple Bool R.arity := fun j => Fin.elim0 j
    have hRows : ∀ j, (BoolBridge.relOfBoolRel R).Holds (rows j) := by
      intro j
      exact Fin.elim0 j
    have hOut := h rows hRows
    have hEq :
        Operation.applyTuple Operation.boolTrue rows =
          BoolTuple.constTrue R.arity := by
      funext i
      rfl
    simpa [ComplexityReduction.CSP.IsOneValid, BoolBridge.relOfBoolRel_holds_iff, hEq]
      using hOut
  · intro h rows _hRows
    simpa [ComplexityReduction.CSP.IsOneValid, BoolBridge.relOfBoolRel_holds_iff,
      Operation.applyTuple, Operation.boolTrue, BoolTuple.constTrue] using h

theorem preservesRel_boolAnd_iff_isHorn (R : BoolRel) :
    PreservesRel Operation.boolAnd (BoolBridge.relOfBoolRel R) ↔
      ComplexityReduction.CSP.IsHorn R := by
  constructor
  · intro h a b ha hb
    let rows : Fin 2 → Tuple Bool R.arity := fun j =>
      if j = (0 : Fin 2) then a else b
    have hRows : ∀ j, (BoolBridge.relOfBoolRel R).Holds (rows j) := by
      intro j
      fin_cases j
      · simpa [rows, BoolBridge.relOfBoolRel_holds_iff, BoolRel.Holds] using ha
      · simpa [rows, BoolBridge.relOfBoolRel_holds_iff, BoolRel.Holds] using hb
    have hOut := h rows hRows
    have hEq :
        Operation.applyTuple Operation.boolAnd rows =
          BoolTuple.pointwiseAnd a b := by
      funext i
      simp [Operation.applyTuple, Operation.boolAnd, BoolTuple.pointwiseAnd, rows]
    simpa [BoolBridge.relOfBoolRel_holds_iff, hEq] using hOut
  · intro h rows hRows
    have hOut := h (rows 0) (rows 1)
      (by simpa [BoolBridge.relOfBoolRel_holds_iff] using hRows 0)
      (by simpa [BoolBridge.relOfBoolRel_holds_iff] using hRows 1)
    simpa [BoolBridge.relOfBoolRel_holds_iff, Operation.applyTuple, Operation.boolAnd,
      BoolTuple.pointwiseAnd] using hOut

theorem preservesRel_boolOr_iff_isDualHorn (R : BoolRel) :
    PreservesRel Operation.boolOr (BoolBridge.relOfBoolRel R) ↔
      ComplexityReduction.CSP.IsDualHorn R := by
  constructor
  · intro h a b ha hb
    let rows : Fin 2 → Tuple Bool R.arity := fun j =>
      if j = (0 : Fin 2) then a else b
    have hRows : ∀ j, (BoolBridge.relOfBoolRel R).Holds (rows j) := by
      intro j
      fin_cases j
      · simpa [rows, BoolBridge.relOfBoolRel_holds_iff, BoolRel.Holds] using ha
      · simpa [rows, BoolBridge.relOfBoolRel_holds_iff, BoolRel.Holds] using hb
    have hOut := h rows hRows
    have hEq :
        Operation.applyTuple Operation.boolOr rows =
          BoolTuple.pointwiseOr a b := by
      funext i
      simp [Operation.applyTuple, Operation.boolOr, BoolTuple.pointwiseOr, rows]
    simpa [BoolBridge.relOfBoolRel_holds_iff, hEq] using hOut
  · intro h rows hRows
    have hOut := h (rows 0) (rows 1)
      (by simpa [BoolBridge.relOfBoolRel_holds_iff] using hRows 0)
      (by simpa [BoolBridge.relOfBoolRel_holds_iff] using hRows 1)
    simpa [BoolBridge.relOfBoolRel_holds_iff, Operation.applyTuple, Operation.boolOr,
      BoolTuple.pointwiseOr] using hOut

theorem preservesRel_boolTernaryXor_iff_isAffine (R : BoolRel) :
    PreservesRel Operation.boolTernaryXor (BoolBridge.relOfBoolRel R) ↔
      ComplexityReduction.CSP.IsAffine R := by
  constructor
  · intro h a b c ha hb hc
    let rows : Fin 3 → Tuple Bool R.arity := fun j =>
      if j = (0 : Fin 3) then a else if j = (1 : Fin 3) then b else c
    have hRows : ∀ j, (BoolBridge.relOfBoolRel R).Holds (rows j) := by
      intro j
      fin_cases j
      · simpa [rows, BoolBridge.relOfBoolRel_holds_iff, BoolRel.Holds] using ha
      · simpa [rows, BoolBridge.relOfBoolRel_holds_iff, BoolRel.Holds] using hb
      · simpa [rows, BoolBridge.relOfBoolRel_holds_iff, BoolRel.Holds] using hc
    have hOut := h rows hRows
    have hEq :
        Operation.applyTuple Operation.boolTernaryXor rows =
          BoolTuple.pointwiseTernaryXor a b c := by
      funext i
      simp [Operation.applyTuple, Operation.boolTernaryXor, BoolTuple.pointwiseTernaryXor,
        rows]
    simpa [BoolBridge.relOfBoolRel_holds_iff, hEq] using hOut
  · intro h rows hRows
    have hOut := h (rows 0) (rows 1) (rows 2)
      (by simpa [BoolBridge.relOfBoolRel_holds_iff] using hRows 0)
      (by simpa [BoolBridge.relOfBoolRel_holds_iff] using hRows 1)
      (by simpa [BoolBridge.relOfBoolRel_holds_iff] using hRows 2)
    simpa [BoolBridge.relOfBoolRel_holds_iff, Operation.applyTuple,
      Operation.boolTernaryXor, BoolTuple.pointwiseTernaryXor] using hOut

theorem preservesRel_boolMajority_iff_isBijunctive (R : BoolRel) :
    PreservesRel Operation.boolMajority (BoolBridge.relOfBoolRel R) ↔
      ComplexityReduction.CSP.IsBijunctive R := by
  constructor
  · intro h a b c ha hb hc
    let rows : Fin 3 → Tuple Bool R.arity := fun j =>
      if j = (0 : Fin 3) then a else if j = (1 : Fin 3) then b else c
    have hRows : ∀ j, (BoolBridge.relOfBoolRel R).Holds (rows j) := by
      intro j
      fin_cases j
      · simpa [rows, BoolBridge.relOfBoolRel_holds_iff, BoolRel.Holds] using ha
      · simpa [rows, BoolBridge.relOfBoolRel_holds_iff, BoolRel.Holds] using hb
      · simpa [rows, BoolBridge.relOfBoolRel_holds_iff, BoolRel.Holds] using hc
    have hOut := h rows hRows
    have hEq :
        Operation.applyTuple Operation.boolMajority rows =
          BoolTuple.pointwiseMajority a b c := by
      funext i
      simp [Operation.applyTuple, Operation.boolMajority, BoolTuple.pointwiseMajority, rows]
    simpa [BoolBridge.relOfBoolRel_holds_iff, hEq] using hOut
  · intro h rows hRows
    have hOut := h (rows 0) (rows 1) (rows 2)
      (by simpa [BoolBridge.relOfBoolRel_holds_iff] using hRows 0)
      (by simpa [BoolBridge.relOfBoolRel_holds_iff] using hRows 1)
      (by simpa [BoolBridge.relOfBoolRel_holds_iff] using hRows 2)
    simpa [BoolBridge.relOfBoolRel_holds_iff, Operation.applyTuple,
      Operation.boolMajority, BoolTuple.pointwiseMajority] using hOut

theorem preservesRel_boolComplement_iff_isComplementive (R : BoolRel) :
    PreservesRel Operation.boolComplement (BoolBridge.relOfBoolRel R) ↔
      ComplexityReduction.CSP.IsComplementive R := by
  constructor
  · intro h a ha
    let rows : Fin 1 → Tuple Bool R.arity := fun _ => a
    have hRows : ∀ j, (BoolBridge.relOfBoolRel R).Holds (rows j) := by
      intro j
      simpa [rows, BoolBridge.relOfBoolRel_holds_iff] using ha
    have hOut := h rows hRows
    have hEq :
        Operation.applyTuple Operation.boolComplement rows =
          BoolTuple.complement a := by
      funext i
      simp [Operation.applyTuple, Operation.boolComplement, BoolTuple.complement, rows]
    simpa [BoolBridge.relOfBoolRel_holds_iff, hEq] using hOut
  · intro h rows hRows
    have hOut := h (rows 0) (by
      simpa [BoolBridge.relOfBoolRel_holds_iff] using hRows 0)
    simpa [BoolBridge.relOfBoolRel_holds_iff, Operation.applyTuple,
      Operation.boolComplement, BoolTuple.complement] using hOut

theorem preservesLanguage_boolAnd_iff_allRelationsHorn (Γ : BoolLanguage) :
    PreservesLanguage Operation.boolAnd (BoolBridge.languageOfBoolLanguage Γ) ↔
      ComplexityReduction.CSP.AllRelationsSatisfy Γ ComplexityReduction.CSP.IsHorn := by
  constructor
  · intro h s
    exact (preservesRel_boolAnd_iff_isHorn (Γ.relationOf s)).1
      (by simpa [BoolBridge.languageOfBoolLanguage] using h s)
  · intro h s
    exact (preservesRel_boolAnd_iff_isHorn (Γ.relationOf s)).2
      (by simpa using h s)

theorem preservesLanguage_boolOr_iff_allRelationsDualHorn (Γ : BoolLanguage) :
    PreservesLanguage Operation.boolOr (BoolBridge.languageOfBoolLanguage Γ) ↔
      ComplexityReduction.CSP.AllRelationsSatisfy Γ ComplexityReduction.CSP.IsDualHorn := by
  constructor
  · intro h s
    exact (preservesRel_boolOr_iff_isDualHorn (Γ.relationOf s)).1
      (by simpa [BoolBridge.languageOfBoolLanguage] using h s)
  · intro h s
    exact (preservesRel_boolOr_iff_isDualHorn (Γ.relationOf s)).2
      (by simpa using h s)

theorem preservesLanguage_boolTernaryXor_iff_allRelationsAffine (Γ : BoolLanguage) :
    PreservesLanguage Operation.boolTernaryXor (BoolBridge.languageOfBoolLanguage Γ) ↔
      ComplexityReduction.CSP.AllRelationsSatisfy Γ ComplexityReduction.CSP.IsAffine := by
  constructor
  · intro h s
    exact (preservesRel_boolTernaryXor_iff_isAffine (Γ.relationOf s)).1
      (by simpa [BoolBridge.languageOfBoolLanguage] using h s)
  · intro h s
    exact (preservesRel_boolTernaryXor_iff_isAffine (Γ.relationOf s)).2
      (by simpa using h s)

theorem preservesLanguage_boolMajority_iff_allRelationsBijunctive (Γ : BoolLanguage) :
    PreservesLanguage Operation.boolMajority (BoolBridge.languageOfBoolLanguage Γ) ↔
      ComplexityReduction.CSP.AllRelationsSatisfy Γ ComplexityReduction.CSP.IsBijunctive := by
  constructor
  · intro h s
    exact (preservesRel_boolMajority_iff_isBijunctive (Γ.relationOf s)).1
      (by simpa [BoolBridge.languageOfBoolLanguage] using h s)
  · intro h s
    exact (preservesRel_boolMajority_iff_isBijunctive (Γ.relationOf s)).2
      (by simpa using h s)

theorem preservesLanguage_boolComplement_iff_allRelationsComplementive (Γ : BoolLanguage) :
    PreservesLanguage Operation.boolComplement (BoolBridge.languageOfBoolLanguage Γ) ↔
      ComplexityReduction.CSP.AllRelationsSatisfy Γ
        ComplexityReduction.CSP.IsComplementive := by
  constructor
  · intro h s
    exact (preservesRel_boolComplement_iff_isComplementive (Γ.relationOf s)).1
      (by simpa [BoolBridge.languageOfBoolLanguage] using h s)
  · intro h s
    exact (preservesRel_boolComplement_iff_isComplementive (Γ.relationOf s)).2
      (by simpa using h s)

theorem preservesLanguage_boolFalse_iff_allRelationsZeroValid (Γ : BoolLanguage) :
    PreservesLanguage Operation.boolFalse (BoolBridge.languageOfBoolLanguage Γ) ↔
      ComplexityReduction.CSP.AllRelationsSatisfy Γ ComplexityReduction.CSP.IsZeroValid := by
  constructor
  · intro h s
    exact (preservesRel_boolFalse_iff_isZeroValid (Γ.relationOf s)).1
      (by simpa [BoolBridge.languageOfBoolLanguage] using h s)
  · intro h s
    exact (preservesRel_boolFalse_iff_isZeroValid (Γ.relationOf s)).2
      (by simpa using h s)

theorem preservesLanguage_boolTrue_iff_allRelationsOneValid (Γ : BoolLanguage) :
    PreservesLanguage Operation.boolTrue (BoolBridge.languageOfBoolLanguage Γ) ↔
      ComplexityReduction.CSP.AllRelationsSatisfy Γ ComplexityReduction.CSP.IsOneValid := by
  constructor
  · intro h s
    exact (preservesRel_boolTrue_iff_isOneValid (Γ.relationOf s)).1
      (by simpa [BoolBridge.languageOfBoolLanguage] using h s)
  · intro h s
    exact (preservesRel_boolTrue_iff_isOneValid (Γ.relationOf s)).2
      (by simpa using h s)

end BoolTransport

end FiniteDomain
end CSP
end ComplexityReduction
