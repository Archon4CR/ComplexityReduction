/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Bool.Basic

namespace ComplexityReduction.Schaefer.Hardness.LocalRep

/-! ## Logical Relations and Schaefer's Six Properties

A k-ary logical relation is a finite set of k-ary Boolean tuples.
Schaefer's dichotomy theorem characterizes SAT(S) based on six
closure properties of the relations in S.
-/

/-- A k-ary logical relation is a finite set of k-ary Boolean tuples.
    We use `abbrev` so that Lean unfolds `LogRel k` to `Finset (Fin k → Bool)`
    during type class resolution (e.g., for `∈` membership). -/
abbrev LogRel (k : Nat) := Finset (Fin k → Bool)

namespace LogRel

/-- The all-false (zero) tuple. -/
def constFalse {k : Nat} : Fin k → Bool := fun _ => false

/-- The all-true (one) tuple. -/
def constTrue {k : Nat} : Fin k → Bool := fun _ => true

/-- Pointwise AND of two tuples (conjunction).
    This is the closure operation for weakly positive (Horn) relations. -/
def pointwiseAnd {k : Nat} (f g : Fin k → Bool) : Fin k → Bool :=
  fun i => f i && g i

/-- Pointwise OR of two tuples (disjunction).
    This is the closure operation for weakly negative (dual-Horn) relations. -/
def pointwiseOr {k : Nat} (f g : Fin k → Bool) : Fin k → Bool :=
  fun i => f i || g i

/-- Pointwise ternary XOR (affine operation: x ⊕ y ⊕ z over GF(2)).
    This is the closure operation for affine relations. -/
def pointwiseTernaryXor {k : Nat} (f g h : Fin k → Bool) : Fin k → Bool :=
  fun i => (f i && !(g i) && !(h i))
        || (!(f i) && g i && !(h i))
        || (!(f i) && !(g i) && h i)
        || (f i && g i && h i)

/-- Pointwise majority of three tuples.
    This is the closure operation for bijunctive (2-SAT) relations.
    maj(a,b,c) is true iff at least two of {a,b,c} are true. -/
def pointwiseMaj {k : Nat} (f g h : Fin k → Bool) : Fin k → Bool :=
  fun i => (f i && g i) || (g i && h i) || (f i && h i)

/-- A relation is 0-valid if it contains the all-false tuple. -/
def IsZeroValid {k : Nat} (R : LogRel k) : Prop :=
  constFalse ∈ R

/-- A relation is 1-valid if it contains the all-true tuple. -/
def IsOneValid {k : Nat} (R : LogRel k) : Prop :=
  constTrue ∈ R

/-- A relation is weakly positive (Horn) if it is closed under pointwise AND.
    That is, for any two tuples f, g in R, their pointwise AND is also in R. -/
def IsWeaklyPositive {k : Nat} (R : LogRel k) : Prop :=
  ∀ ⦃f g : Fin k → Bool⦄, f ∈ R → g ∈ R → pointwiseAnd f g ∈ R

/-- A relation is weakly negative (dual-Horn) if it is closed under pointwise OR.
    That is, for any two tuples f, g in R, their pointwise OR is also in R. -/
def IsWeaklyNegative {k : Nat} (R : LogRel k) : Prop :=
  ∀ ⦃f g : Fin k → Bool⦄, f ∈ R → g ∈ R → pointwiseOr f g ∈ R

/-- A relation is affine if it is closed under ternary XOR (x ⊕ y ⊕ z).
    That is, for any three tuples f, g, h in R, their pointwise ternary XOR
    is also in R. Equivalently, R is the solution set of a system of linear
    equations over GF(2). -/
def IsAffine {k : Nat} (R : LogRel k) : Prop :=
  ∀ ⦃f g h : Fin k → Bool⦄, f ∈ R → g ∈ R → h ∈ R → pointwiseTernaryXor f g h ∈ R

/-- A relation is bijunctive (2-SAT) if it is closed under majority.
    That is, for any three tuples f, g, h in R, their pointwise majority
    is also in R. Equivalently, R can be expressed as a conjunction of
    2-literal clauses. -/
def IsBijunctive {k : Nat} (R : LogRel k) : Prop :=
  ∀ ⦃f g h : Fin k → Bool⦄, f ∈ R → g ∈ R → h ∈ R → pointwiseMaj f g h ∈ R

end LogRel

end LocalRep