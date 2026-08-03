/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Bool.Basic
import ComplexityReduction.Schaefer.Hardness.LocalRep.SAT.LogicalRelation

namespace ComplexityReduction.Schaefer.Hardness.LocalRep

open LogRel

/-! ## Helper Functions for Tuple Manipulation
-/

/-- Extend a k-tuple with one Boolean value to a (k+1)-tuple.
    The first k positions come from t, the last position is b. -/
def extendWith {k : Nat} (t : Fin k → Bool) (b : Bool) : Fin (k + 1) → Bool :=
  fun i => if h : i.val < k then t ⟨i.val, h⟩ else b

/-- Project a (k+1)-tuple to its first k components. -/
def restrictFin {k : Nat} (t : Fin (k + 1) → Bool) : Fin k → Bool :=
  fun i => t ⟨i.val, by omega⟩

/-- Extract the left (first k) components of a (k+l)-tuple. -/
def splitLeft {k l : Nat} (t : Fin (k + l) → Bool) : Fin k → Bool :=
  fun i => t ⟨i.val, by omega⟩

/-- Extract the right (last l) components of a (k+l)-tuple. -/
def splitRight {k l : Nat} (t : Fin (k + l) → Bool) : Fin l → Bool :=
  fun j => t ⟨j.val + k, by omega⟩

/-- Concatenate a k-tuple and an l-tuple into a (k+l)-tuple. -/
def concatTuples {k l : Nat} (t : Fin k → Bool) (u : Fin l → Bool) : Fin (k + l) → Bool :=
  fun i => if h : i.val < k then t ⟨i.val, h⟩ else u ⟨i.val - k, by omega⟩

/-! ## Fundamental Operations on Logical Relations

These three operations — existential quantification, substitution,
and conjunction — generate all primitive-positive definable relations
from a given set S, forming the closure Rep(S).
-/

/-- Existential quantification: project out the last variable.
    Given R ⊆ {0,1}^(k+1), ∃R ⊆ {0,1}^k consists of tuples t such that
    there exists b : Bool with (t extended with b) ∈ R. -/
def existentialQuantify {k : Nat} (R : LogRel (k + 1)) : LogRel k :=
  Finset.filter (fun t : Fin k → Bool => ∃ b : Bool, extendWith t b ∈ R) Finset.univ

/-- Apply a substitution π to a tuple s : Fin m → Bool, producing a k-tuple.
    For each position i : Fin k, if π i = inl j we use s j; if π i = inr b we use b. -/
def substApply {k m : Nat} (π : Fin k → Fin m ⊕ Bool) (s : Fin m → Bool) : Fin k → Bool :=
  fun i => match π i with | Sum.inl j => s j | Sum.inr b => b

/-- Substitution: given R of arity k and a mapping π : Fin k → Fin m ⊕ Bool,
    produce a relation of arity m: the set of m-tuples s such that
    the substituted tuple (substApply π s) belongs to R.
    This operation encompasses variable identification,
    variable permutation, and constant substitution. -/
def substitute {k m : Nat} (R : LogRel k) (π : Fin k → Fin m ⊕ Bool) : LogRel m :=
  Finset.filter (fun s : Fin m → Bool => substApply π s ∈ R) Finset.univ

/-- Negated substitution: like substitution but negated variables.
    For each position i : Fin k, if π i = inl j we use !(s j); if π i = inr b we use b. -/
def negSubstApply {k m : Nat} (π : Fin k → Fin m ⊕ Bool) (s : Fin m → Bool) : Fin k → Bool :=
  fun i => match π i with | Sum.inl j => !(s j) | Sum.inr b => b

/-- Negated substitution: the relation obtained by negating referenced variables
    before applying the substitution. This is NOT a closure operation of Rep(S),
    but is important for constructing specific relations (e.g., [x≠y]). -/
def negSubstitute {k m : Nat} (R : LogRel k) (π : Fin k → Fin m ⊕ Bool) : LogRel m :=
  Finset.filter (fun s : Fin m → Bool => negSubstApply π s ∈ R) Finset.univ

/-- Conjunction (Cartesian product / join): given R ⊆ {0,1}^k and S ⊆ {0,1}^l,
    produce R ∧ S ⊆ {0,1}^(k+l) consisting of tuples t such that
    splitLeft t ∈ R and splitRight t ∈ S. -/
def conjoin {k l : Nat} (R : LogRel k) (S : LogRel l) : LogRel (k + l) :=
  Finset.filter (fun t : Fin (k + l) → Bool =>
    splitLeft t ∈ R ∧ splitRight t ∈ S) Finset.univ

/-! ## Commonly Used Logical Relations
-/

/-- The equality relation: [x = y] = {(true, true), (false, false)}. -/
def eqRel : LogRel 2 :=
  Finset.filter (fun t : Fin 2 → Bool => t ⟨0, by omega⟩ = t ⟨1, by omega⟩) Finset.univ

/-- The disequality relation: [x ≠ y] = {(true, false), (false, true)}. -/
def neqRel : LogRel 2 :=
  Finset.filter (fun t : Fin 2 → Bool => t ⟨0, by omega⟩ ≠ t ⟨1, by omega⟩) Finset.univ

/-- The unary "all-true" relation: {true}. -/
def allTrueRel : LogRel 1 :=
  Finset.filter (fun t : Fin 1 → Bool => t ⟨0, by omega⟩ = true) Finset.univ

/-- The unary "all-false" relation: {false}. -/
def allFalseRel : LogRel 1 :=
  Finset.filter (fun t : Fin 1 → Bool => t ⟨0, by omega⟩ = false) Finset.univ

/-- The binary OR relation: {(true,true), (true,false), (false,true)}.
    R(x,y) = (x ∨ y). -/
def orRel : LogRel 2 :=
  Finset.filter (fun t : Fin 2 → Bool => t ⟨0, by omega⟩ || t ⟨1, by omega⟩) Finset.univ

/-- The binary AND relation: {(true,true)}.
    R(x,y) = (x ∧ y). -/
def andRel : LogRel 2 :=
  Finset.filter (fun t : Fin 2 → Bool => t ⟨0, by omega⟩ && t ⟨1, by omega⟩) Finset.univ

/-- The unary NOT relation: {false}. R(x) = ¬x.
    Note: This is the same set as allFalseRel, but represents the
    constraint ¬x rather than the constant false. -/
def notRel : LogRel 1 :=
  Finset.filter (fun t : Fin 1 → Bool => !(t ⟨0, by omega⟩)) Finset.univ

/-- The "exactly one" relation on 3 variables: exactly one of x, y, z is true.
    {(true, false, false), (false, true, false), (false, false, true)}. -/
def exactlyOneRel : LogRel 3 :=
  Finset.filter (fun t : Fin 3 → Bool =>
    (t ⟨0, by omega⟩ && !t ⟨1, by omega⟩ && !t ⟨2, by omega⟩) ||
    (!t ⟨0, by omega⟩ && t ⟨1, by omega⟩ && !t ⟨2, by omega⟩) ||
    (!t ⟨0, by omega⟩ && !t ⟨1, by omega⟩ && t ⟨2, by omega⟩))
    Finset.univ

/-- The 3-ary OR relation: at least one of x, y, z is true.
    All tuples except (false, false, false). -/
def or3Rel : LogRel 3 :=
  Finset.filter (fun t : Fin 3 → Bool =>
    t ⟨0, by omega⟩ || t ⟨1, by omega⟩ || t ⟨2, by omega⟩) Finset.univ

/-- The 3-ary NAND relation: not all of x, y, z are true.
    All tuples except (true, true, true). -/
def nand3Rel : LogRel 3 :=
  Finset.filter (fun t : Fin 3 → Bool =>
    !(t ⟨0, by omega⟩ && t ⟨1, by omega⟩ && t ⟨2, by omega⟩)) Finset.univ

/-- The full k-ary relation: all possible tuples. -/
def fullRel (k : Nat) : LogRel k := Finset.univ

/-- The empty k-ary relation: no tuples. -/
def emptyRel (k : Nat) : LogRel k := Finset.empty

/-- The relation [x → y] = {(true,true), (false,true), (false,false)}: implication. -/
def implRel : LogRel 2 :=
  Finset.filter (fun t : Fin 2 → Bool =>
    !(t ⟨0, by omega⟩) || t ⟨1, by omega⟩) Finset.univ

/-! ## Membership Characterization Lemmas
-/

@[simp] theorem mem_existentialQuantify {k : Nat} {R : LogRel (k + 1)} {t : Fin k → Bool} :
    t ∈ existentialQuantify R ↔ ∃ b : Bool, extendWith t b ∈ R := by
  unfold existentialQuantify; simp [Finset.mem_filter, Finset.mem_univ]

@[simp] theorem mem_substitute {k m : Nat} {R : LogRel k} {π : Fin k → Fin m ⊕ Bool}
    {s : Fin m → Bool} :
    s ∈ substitute R π ↔ substApply π s ∈ R := by
  unfold substitute; simp [Finset.mem_filter, Finset.mem_univ]

@[simp] theorem mem_negSubstitute {k m : Nat} {R : LogRel k} {π : Fin k → Fin m ⊕ Bool}
    {s : Fin m → Bool} :
    s ∈ negSubstitute R π ↔ negSubstApply π s ∈ R := by
  unfold negSubstitute; simp [Finset.mem_filter, Finset.mem_univ]

@[simp] theorem mem_conjoin {k l : Nat} {R : LogRel k} {S : LogRel l}
    {t : Fin (k + l) → Bool} :
    t ∈ conjoin R S ↔ splitLeft t ∈ R ∧ splitRight t ∈ S := by
  unfold conjoin; simp [Finset.mem_filter, Finset.mem_univ]

/-! ## Properties of Specific Relations
-/

@[simp] theorem mem_eqRel {t : Fin 2 → Bool} :
    t ∈ eqRel ↔ t ⟨0, by omega⟩ = t ⟨1, by omega⟩ := by
  unfold eqRel; simp [Finset.mem_filter, Finset.mem_univ]

@[simp] theorem mem_neqRel {t : Fin 2 → Bool} :
    t ∈ neqRel ↔ t ⟨0, by omega⟩ ≠ t ⟨1, by omega⟩ := by
  unfold neqRel; simp [Finset.mem_filter, Finset.mem_univ]

@[simp] theorem mem_allTrueRel {t : Fin 1 → Bool} :
    t ∈ allTrueRel ↔ t ⟨0, by omega⟩ = true := by
  unfold allTrueRel; simp [Finset.mem_filter, Finset.mem_univ]

@[simp] theorem mem_allFalseRel {t : Fin 1 → Bool} :
    t ∈ allFalseRel ↔ t ⟨0, by omega⟩ = false := by
  unfold allFalseRel; simp [Finset.mem_filter, Finset.mem_univ]

@[simp] theorem mem_orRel {t : Fin 2 → Bool} :
    t ∈ orRel ↔ t ⟨0, by omega⟩ || t ⟨1, by omega⟩ := by
  unfold orRel; simp [Finset.mem_filter, Finset.mem_univ]

@[simp] theorem mem_andRel {t : Fin 2 → Bool} :
    t ∈ andRel ↔ t ⟨0, by omega⟩ && t ⟨1, by omega⟩ := by
  unfold andRel; simp [Finset.mem_filter, Finset.mem_univ]

@[simp] theorem mem_exactlyOneRel {t : Fin 3 → Bool} :
    t ∈ exactlyOneRel ↔
      (t ⟨0, by omega⟩ && !t ⟨1, by omega⟩ && !t ⟨2, by omega⟩) ||
      (!t ⟨0, by omega⟩ && t ⟨1, by omega⟩ && !t ⟨2, by omega⟩) ||
      (!t ⟨0, by omega⟩ && !t ⟨1, by omega⟩ && t ⟨2, by omega⟩) := by
  unfold exactlyOneRel; simp [Finset.mem_filter, Finset.mem_univ]

@[simp] theorem mem_or3Rel {t : Fin 3 → Bool} :
    t ∈ or3Rel ↔ t ⟨0, by omega⟩ || t ⟨1, by omega⟩ || t ⟨2, by omega⟩ := by
  unfold or3Rel; simp [Finset.mem_filter, Finset.mem_univ]

@[simp] theorem mem_nand3Rel {t : Fin 3 → Bool} :
    t ∈ nand3Rel ↔ !(t ⟨0, by omega⟩ && t ⟨1, by omega⟩ && t ⟨2, by omega⟩) := by
  unfold nand3Rel; simp [Finset.mem_filter, Finset.mem_univ]

@[simp] theorem mem_fullRel {k : Nat} (t : Fin k → Bool) :
    t ∈ fullRel k := by
  unfold fullRel; exact Finset.mem_univ t

@[simp] theorem mem_emptyRel {k : Nat} (t : Fin k → Bool) :
    t ∈ emptyRel k ↔ False := by
  unfold emptyRel
  constructor <;> intro h <;> cases h

@[simp] theorem mem_implRel {t : Fin 2 → Bool} :
    t ∈ implRel ↔ (!(t ⟨0, by omega⟩) || t ⟨1, by omega⟩) := by
  unfold implRel; simp [Finset.mem_filter, Finset.mem_univ]

/-! ## Auxiliary Tuple Lemmas
-/

theorem existentialQuantify_mono {k : Nat} {R S : LogRel (k + 1)} (h : R ⊆ S) :
    existentialQuantify R ⊆ existentialQuantify S := by
  intro t ht
  rw [mem_existentialQuantify] at ht ⊢
  obtain ⟨b, hb⟩ := ht
  exact ⟨b, h hb⟩

theorem substitute_mono {k m : Nat} {R S : LogRel k} (h : R ⊆ S) (π : Fin k → Fin m ⊕ Bool) :
    substitute R π ⊆ substitute S π := by
  intro s hs
  rw [mem_substitute] at hs ⊢
  exact h hs

theorem conjoin_mono_left {k l : Nat} {R R' : LogRel k} {S : LogRel l}
    (h : R ⊆ R') :
    conjoin R S ⊆ conjoin R' S := by
  intro t ht
  rw [mem_conjoin] at ht ⊢
  exact ⟨h ht.1, ht.2⟩

theorem conjoin_mono_right {k l : Nat} {R : LogRel k} {S S' : LogRel l}
    (h : S ⊆ S') :
    conjoin R S ⊆ conjoin R S' := by
  intro t ht
  rw [mem_conjoin] at ht ⊢
  exact ⟨ht.1, h ht.2⟩

end LocalRep