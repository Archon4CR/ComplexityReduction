/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Schaefer.Hardness.LocalRep.SAT.LogicalRelation
import ComplexityReduction.Schaefer.Hardness.LocalRep.Closure.Operations

namespace ComplexityReduction.Schaefer.Hardness.LocalRep

open LogRel

/-! ## Representability: Rep(S)

A relation R is **representable** from S (written `InRep S R`) if it can be
obtained from the relations in S using the three fundamental operations:
existential quantification, substitution, and conjunction.

This is equivalent to R being primitive-positive (pp-) definable from S,
which is the notion used in Schaefer's dichotomy theorem.
-/

/-- A bundled k-ary logical relation, used as the element type for
    finite sets of relations (S in SAT(S)). -/
structure BundledLogRel where
  arity : Nat
  rel : LogRel arity
  deriving DecidableEq

/-- Coercion from BundledLogRel to the Sigma type. -/
instance : Coe BundledLogRel (Σ k, LogRel k) where
  coe b := ⟨b.arity, b.rel⟩

/-- A k-ary relation R is representable from S (in Rep(S))
    if it can be derived from relations in S using
    existential quantification, substitution, and conjunction. -/
inductive InRep (S : Finset BundledLogRel) : ∀ k, LogRel k → Prop
  | base (r : BundledLogRel) : ↑r ∈ S → InRep S r.arity r.rel
  | existential {k : Nat} (R : LogRel (k + 1)) :
      InRep S (k + 1) R → InRep S k (existentialQuantify R)
  | conj {k l : Nat} (R : LogRel k) (T : LogRel l) :
      InRep S k R → InRep S l T → InRep S (k + l) (conjoin R T)
  | subst {k m : Nat} (R : LogRel k) (π : Fin k → Fin m ⊕ Bool) :
      InRep S k R → InRep S m (substitute R π)

/-- Rep(S) is monotone: if S ⊆ S', then InRep S R → InRep S' R.
    Proof by induction on the InRep derivation, replacing the base case
    since the new set S' is a superset. -/
theorem InRep.mono {S S' : Finset BundledLogRel} (h : S ⊆ S')
    {k : Nat} {R : LogRel k} : InRep S k R → InRep S' k R
  | .base r hm => .base r (h hm)
  | .existential R hi => .existential R (mono h hi)
  | .conj R T h1 h2 => .conj R T (mono h h1) (mono h h2)
  | .subst R π hi => .subst R π (mono h hi)

/-- Every relation in S is in Rep(S). -/
theorem InRep.of_mem {S : Finset BundledLogRel} {r : BundledLogRel}
    (h : ↑r ∈ S) : InRep S r.arity r.rel := InRep.base r h

/-- Rep(S) at arity k: the set of all k-ary relations representable from S. -/
def RepAt (S : Finset BundledLogRel) (k : Nat) : Set (LogRel k) :=
  { R : LogRel k | InRep S k R }

end LocalRep
