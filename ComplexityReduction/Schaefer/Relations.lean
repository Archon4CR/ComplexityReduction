/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Polymorphisms.Bool

/-!
Local Schaefer relation-family predicates over the repository's `CSP.BoolRel`
foundation.

The Boolean tuple operations and raw polymorphism predicates now live in
`ComplexityReduction.CSP.Polymorphisms.Bool`.  This file keeps the Schaefer
condition names and hard-case package as the application-specific surface.
-/

namespace ComplexityReduction
namespace Schaefer

namespace BoolTuple

abbrev constFalse (k : Nat) : CSP.BoolTuple k :=
  CSP.BoolTuple.constFalse k

abbrev constTrue (k : Nat) : CSP.BoolTuple k :=
  CSP.BoolTuple.constTrue k

abbrev pointwiseAnd {k : Nat} (a b : CSP.BoolTuple k) : CSP.BoolTuple k :=
  CSP.BoolTuple.pointwiseAnd a b

abbrev pointwiseOr {k : Nat} (a b : CSP.BoolTuple k) : CSP.BoolTuple k :=
  CSP.BoolTuple.pointwiseOr a b

abbrev pointwiseTernaryXor {k : Nat} (a b c : CSP.BoolTuple k) : CSP.BoolTuple k :=
  CSP.BoolTuple.pointwiseTernaryXor a b c

abbrev pointwiseMajority {k : Nat} (a b c : CSP.BoolTuple k) : CSP.BoolTuple k :=
  CSP.BoolTuple.pointwiseMajority a b c

abbrev complement {k : Nat} (a : CSP.BoolTuple k) : CSP.BoolTuple k :=
  CSP.BoolTuple.complement a

@[simp]
theorem constFalse_apply (k : Nat) (i : Fin k) :
    constFalse k i = false :=
  rfl

@[simp]
theorem constTrue_apply (k : Nat) (i : Fin k) :
    constTrue k i = true :=
  rfl

@[simp]
theorem pointwiseAnd_apply {k : Nat} (a b : CSP.BoolTuple k) (i : Fin k) :
    pointwiseAnd a b i = (a i && b i) :=
  rfl

@[simp]
theorem pointwiseOr_apply {k : Nat} (a b : CSP.BoolTuple k) (i : Fin k) :
    pointwiseOr a b i = (a i || b i) :=
  rfl

@[simp]
theorem pointwiseTernaryXor_apply {k : Nat} (a b c : CSP.BoolTuple k) (i : Fin k) :
    pointwiseTernaryXor a b c i = xor (xor (a i) (b i)) (c i) :=
  rfl

@[simp]
theorem pointwiseMajority_apply {k : Nat} (a b c : CSP.BoolTuple k) (i : Fin k) :
    pointwiseMajority a b c i = ((a i && b i) || (a i && c i) || (b i && c i)) :=
  rfl

@[simp]
theorem complement_apply {k : Nat} (a : CSP.BoolTuple k) (i : Fin k) :
    complement a i = !a i :=
  rfl

end BoolTuple

abbrev IsZeroValid (R : CSP.BoolRel) : Prop :=
  CSP.IsZeroValid R

abbrev IsOneValid (R : CSP.BoolRel) : Prop :=
  CSP.IsOneValid R

abbrev IsHorn (R : CSP.BoolRel) : Prop :=
  CSP.IsHorn R

abbrev IsWeaklyPositive (R : CSP.BoolRel) : Prop :=
  CSP.IsWeaklyPositive R

abbrev IsDualHorn (R : CSP.BoolRel) : Prop :=
  CSP.IsDualHorn R

abbrev IsWeaklyNegative (R : CSP.BoolRel) : Prop :=
  CSP.IsWeaklyNegative R

abbrev IsAffine (R : CSP.BoolRel) : Prop :=
  CSP.IsAffine R

abbrev IsBijunctive (R : CSP.BoolRel) : Prop :=
  CSP.IsBijunctive R

abbrev IsComplementive (R : CSP.BoolRel) : Prop :=
  CSP.IsComplementive R

/-- The six Schaefer tractable-condition names. -/
inductive TractableConditionKind where
  | zeroValid
  | oneValid
  | horn
  | dualHorn
  | affine
  | bijunctive
  deriving DecidableEq, Repr

namespace TractableConditionKind

/-- Stable spelling for gap maps and manifests. -/
def asString : TractableConditionKind → String
  | zeroValid => "zero-valid"
  | oneValid => "one-valid"
  | horn => "Horn/weakly-positive"
  | dualHorn => "dual-Horn/weakly-negative"
  | affine => "affine"
  | bijunctive => "bijunctive"

end TractableConditionKind

/-- Whether a relation satisfies one named Schaefer tractable condition. -/
def RelationSatisfies (condition : TractableConditionKind) (R : CSP.BoolRel) : Prop :=
  match condition with
  | TractableConditionKind.zeroValid => IsZeroValid R
  | TractableConditionKind.oneValid => IsOneValid R
  | TractableConditionKind.horn => IsHorn R
  | TractableConditionKind.dualHorn => IsDualHorn R
  | TractableConditionKind.affine => IsAffine R
  | TractableConditionKind.bijunctive => IsBijunctive R

/-- Every relation symbol in a finite local language satisfies predicate `P`. -/
abbrev AllRelationsSatisfy (Γ : CSP.BoolLanguage) (P : CSP.BoolRel → Prop) : Prop :=
  CSP.AllRelationsSatisfy Γ P

/-- A language satisfies a named Schaefer condition when every relation does. -/
def LanguageSatisfies (condition : TractableConditionKind) (Γ : CSP.BoolLanguage) : Prop :=
  AllRelationsSatisfy Γ (RelationSatisfies condition)

/-- Local zero-valid language condition. -/
abbrev IsZeroValidLanguage (Γ : CSP.BoolLanguage) : Prop :=
  LanguageSatisfies TractableConditionKind.zeroValid Γ

/-- Local one-valid language condition. -/
abbrev IsOneValidLanguage (Γ : CSP.BoolLanguage) : Prop :=
  LanguageSatisfies TractableConditionKind.oneValid Γ

/-- Local Horn language condition. -/
abbrev IsHornLanguage (Γ : CSP.BoolLanguage) : Prop :=
  LanguageSatisfies TractableConditionKind.horn Γ

/-- Local dual-Horn language condition. -/
abbrev IsDualHornLanguage (Γ : CSP.BoolLanguage) : Prop :=
  LanguageSatisfies TractableConditionKind.dualHorn Γ

/-- Local affine language condition. -/
abbrev IsAffineLanguage (Γ : CSP.BoolLanguage) : Prop :=
  LanguageSatisfies TractableConditionKind.affine Γ

/-- Local bijunctive language condition. -/
abbrev IsBijunctiveLanguage (Γ : CSP.BoolLanguage) : Prop :=
  LanguageSatisfies TractableConditionKind.bijunctive Γ

/-- The tractable side of Schaefer: at least one of the six conditions holds. -/
def IsTractableLanguage (Γ : CSP.BoolLanguage) : Prop :=
  ∃ condition : TractableConditionKind, LanguageSatisfies condition Γ

/-- The hard side of Schaefer: all six local tractable conditions fail. -/
def IsHardCaseLanguage (Γ : CSP.BoolLanguage) : Prop :=
  ∀ condition : TractableConditionKind, ¬ LanguageSatisfies condition Γ

/-- Structured hard-case assumptions for later local proof targets. -/
structure HardCaseAssumptions (Γ : CSP.BoolLanguage) where
  notZeroValid : ¬ IsZeroValidLanguage Γ
  notOneValid : ¬ IsOneValidLanguage Γ
  notHorn : ¬ IsHornLanguage Γ
  notDualHorn : ¬ IsDualHornLanguage Γ
  notAffine : ¬ IsAffineLanguage Γ
  notBijunctive : ¬ IsBijunctiveLanguage Γ

namespace HardCaseAssumptions

/-- Convert the named-field hard-case package to the uniform condition predicate. -/
theorem toIsHardCaseLanguage {Γ : CSP.BoolLanguage} (h : HardCaseAssumptions Γ) :
    IsHardCaseLanguage Γ := by
  intro condition
  cases condition with
  | zeroValid => exact h.notZeroValid
  | oneValid => exact h.notOneValid
  | horn => exact h.notHorn
  | dualHorn => exact h.notDualHorn
  | affine => exact h.notAffine
  | bijunctive => exact h.notBijunctive

end HardCaseAssumptions

end Schaefer
end ComplexityReduction
