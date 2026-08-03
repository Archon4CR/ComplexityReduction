/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Language

/-!
Boolean tuple operations and relation-family predicates used by CSP
classification theorems.

These predicates are intentionally generic over `CSP.BoolRel` and
`CSP.BoolLanguage`; Schaefer-specific modules map their named tractable
conditions to this stable library surface.
-/

namespace ComplexityReduction
namespace CSP

namespace BoolTuple

/-- The all-false tuple of arity `k`. -/
def constFalse (k : Nat) : BoolTuple k :=
  fun _ => false

/-- The all-true tuple of arity `k`. -/
def constTrue (k : Nat) : BoolTuple k :=
  fun _ => true

/-- Pointwise conjunction of Boolean tuples. -/
def pointwiseAnd {k : Nat} (a b : BoolTuple k) : BoolTuple k :=
  fun i => a i && b i

/-- Pointwise disjunction of Boolean tuples. -/
def pointwiseOr {k : Nat} (a b : BoolTuple k) : BoolTuple k :=
  fun i => a i || b i

/-- Pointwise ternary xor over `Bool`. -/
def pointwiseTernaryXor {k : Nat} (a b c : BoolTuple k) : BoolTuple k :=
  fun i => xor (xor (a i) (b i)) (c i)

/-- Pointwise majority of three Boolean tuples. -/
def pointwiseMajority {k : Nat} (a b c : BoolTuple k) : BoolTuple k :=
  fun i => (a i && b i) || (a i && c i) || (b i && c i)

/-- Pointwise Boolean complement. -/
def complement {k : Nat} (a : BoolTuple k) : BoolTuple k :=
  fun i => !a i

@[simp]
theorem constFalse_apply (k : Nat) (i : Fin k) :
    constFalse k i = false :=
  rfl

@[simp]
theorem constTrue_apply (k : Nat) (i : Fin k) :
    constTrue k i = true :=
  rfl

@[simp]
theorem pointwiseAnd_apply {k : Nat} (a b : BoolTuple k) (i : Fin k) :
    pointwiseAnd a b i = (a i && b i) :=
  rfl

@[simp]
theorem pointwiseOr_apply {k : Nat} (a b : BoolTuple k) (i : Fin k) :
    pointwiseOr a b i = (a i || b i) :=
  rfl

@[simp]
theorem pointwiseTernaryXor_apply {k : Nat} (a b c : BoolTuple k) (i : Fin k) :
    pointwiseTernaryXor a b c i = xor (xor (a i) (b i)) (c i) :=
  rfl

@[simp]
theorem pointwiseMajority_apply {k : Nat} (a b c : BoolTuple k) (i : Fin k) :
    pointwiseMajority a b c i = ((a i && b i) || (a i && c i) || (b i && c i)) :=
  rfl

@[simp]
theorem complement_apply {k : Nat} (a : BoolTuple k) (i : Fin k) :
    complement a i = !a i :=
  rfl

end BoolTuple

/-- Zero-valid relation predicate: the all-false tuple is accepted. -/
def IsZeroValid (R : BoolRel) : Prop :=
  R.Holds (BoolTuple.constFalse R.arity)

/-- One-valid relation predicate: the all-true tuple is accepted. -/
def IsOneValid (R : BoolRel) : Prop :=
  R.Holds (BoolTuple.constTrue R.arity)

/-- Horn/weakly-positive predicate, stated as closure under pointwise AND. -/
def IsHorn (R : BoolRel) : Prop :=
  ∀ a b : BoolTuple R.arity,
    R.Holds a → R.Holds b → R.Holds (BoolTuple.pointwiseAnd a b)

/-- Compatibility name for Schaefer's weakly-positive condition. -/
abbrev IsWeaklyPositive (R : BoolRel) : Prop :=
  IsHorn R

/-- Dual-Horn/weakly-negative predicate, stated as closure under pointwise OR. -/
def IsDualHorn (R : BoolRel) : Prop :=
  ∀ a b : BoolTuple R.arity,
    R.Holds a → R.Holds b → R.Holds (BoolTuple.pointwiseOr a b)

/-- Compatibility name for Schaefer's weakly-negative condition. -/
abbrev IsWeaklyNegative (R : BoolRel) : Prop :=
  IsDualHorn R

/-- Affine predicate, stated as closure under ternary xor. -/
def IsAffine (R : BoolRel) : Prop :=
  ∀ a b c : BoolTuple R.arity,
    R.Holds a → R.Holds b → R.Holds c →
      R.Holds (BoolTuple.pointwiseTernaryXor a b c)

/-- Bijunctive predicate, stated as closure under majority. -/
def IsBijunctive (R : BoolRel) : Prop :=
  ∀ a b c : BoolTuple R.arity,
    R.Holds a → R.Holds b → R.Holds c →
      R.Holds (BoolTuple.pointwiseMajority a b c)

/-- Complementive relation predicate used by no-constants hard-side routes. -/
def IsComplementive (R : BoolRel) : Prop :=
  ∀ a : BoolTuple R.arity, R.Holds a → R.Holds (BoolTuple.complement a)

/-- Every relation symbol in a finite Boolean CSP language satisfies predicate `P`. -/
def AllRelationsSatisfy (Γ : BoolLanguage) (P : BoolRel → Prop) : Prop :=
  ∀ s : Γ.Symbol, P (Γ.relationOf s)

/-- Every relation in the language is nonempty. -/
def AllRelationsNonempty (Γ : BoolLanguage) : Prop :=
  ∀ s : Γ.Symbol, (Γ.relationOf s).Nonempty

end CSP
end ComplexityReduction
