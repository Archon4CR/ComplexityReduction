/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Schaefer.DichotomyStatement

/-!
Executable Horn-CNF unit-closure solver and an operational bridge from local
`SAT(S)` formulas to direct Horn-CNF syntax.

This module formalizes the classic forward-chaining/unit-closure algorithm for a
direct Horn-CNF syntax, an operational certificate bridge for `SAT(S)`, and the
finite-relation characterization that turns Schaefer's closure-under-meet Horn
predicate into those operational certificates.
-/

namespace ComplexityReduction
namespace Schaefer
namespace Horn

/-- A Horn clause `p₁ ∧ ... ∧ pₙ -> head`; `none` is a goal/contradiction clause. -/
structure Clause where
  premises : Finset Nat
  head : Option Nat
  deriving DecidableEq

/-- A direct Horn-CNF formula is a conjunction of Horn implication clauses. -/
abbrev CNF : Type :=
  List Clause

namespace Clause

/-- Variables mentioned by a Horn clause. -/
def vars (c : Clause) : Finset Nat :=
  c.premises ∪ c.head.elim ∅ (fun x => {x})

/-- Instantiate a local arity-indexed Horn clause by a variable map. -/
def mapVars (f : Nat → Nat) (c : Clause) : Clause where
  premises := c.premises.image f
  head := c.head.map f

/-- Satisfaction of one Horn implication clause by a Boolean assignment. -/
def Satisfies (c : Clause) (a : SAT.Assignment) : Prop :=
  (∀ x ∈ c.premises, a x = true) →
    match c.head with
    | some y => a y = true
    | none => False

/-- A conflict clause is a goal clause whose premises are already known. -/
def IsConflict (c : Clause) (known : Finset Nat) : Prop :=
  c.head = none ∧ c.premises ⊆ known

/-- Boolean conflict check for one goal clause. -/
def conflictBool (c : Clause) (known : Finset Nat) : Bool :=
  match c.head with
  | none => decide (c.premises ⊆ known)
  | some _ => false

theorem conflictBool_eq_true_iff (c : Clause) (known : Finset Nat) :
    c.conflictBool known = true ↔ c.IsConflict known := by
  unfold conflictBool IsConflict
  cases hHead : c.head with
  | none =>
      by_cases hPrem : c.premises ⊆ known
      · simp [hPrem]
      · simp [hPrem]
  | some y =>
      simp

/-- If all premises are known and the clause has a not-yet-known head, return it. -/
def newHead? (c : Clause) (known remaining : Finset Nat) : Option {x : Nat // x ∈ remaining} :=
  if c.premises ⊆ known then
    match c.head with
    | some y =>
        if hRemaining : y ∈ remaining then
          some ⟨y, hRemaining⟩
        else
          none
    | none => none
  else
    none

theorem newHead?_some {c : Clause} {known remaining : Finset Nat}
    {y : {x : Nat // x ∈ remaining}}
    (h : c.newHead? known remaining = some y) :
    c.premises ⊆ known ∧ c.head = some y.val := by
  unfold newHead? at h
  by_cases hPrem : c.premises ⊆ known
  · cases hHead : c.head with
    | none =>
        simp [hPrem, hHead] at h
    | some z =>
        by_cases hRemaining : z ∈ remaining
        · simp [hPrem, hHead, hRemaining] at h
          have hyval : z = y.val := congrArg Subtype.val h
          constructor
          · exact hPrem
          · simp [hyval] at hHead ⊢
        · simp [hPrem, hHead, hRemaining] at h
  · simp [hPrem] at h

theorem newHead?_none {c : Clause} {known remaining : Finset Nat}
    (h : c.newHead? known remaining = none)
    (hPrem : c.premises ⊆ known) {y : Nat} (hHead : c.head = some y) :
    y ∉ remaining := by
  unfold newHead? at h
  simp [hPrem, hHead] at h
  by_cases hRemaining : y ∈ remaining
  · simp [hRemaining] at h
  · exact hRemaining

theorem head_mem_vars {c : Clause} {y : Nat} (hHead : c.head = some y) :
    y ∈ c.vars := by
  simp [vars, hHead]

theorem premise_mem_vars {c : Clause} {x : Nat} (hx : x ∈ c.premises) :
    x ∈ c.vars := by
  simp [vars, hx]

end Clause

namespace CNF

/-- Variables mentioned by a Horn-CNF formula. -/
def vars : CNF → Finset Nat
  | [] => ∅
  | c :: cs => c.vars ∪ vars cs

/-- Satisfaction of a Horn-CNF formula. -/
def Satisfies (φ : CNF) (a : SAT.Assignment) : Prop :=
  ∀ c ∈ φ, c.Satisfies a

/-- Existential satisfiability of a Horn-CNF formula. -/
def Satisfiable (φ : CNF) : Prop :=
  ∃ a : SAT.Assignment, Satisfies φ a

@[simp]
theorem satisfies_nil (a : SAT.Assignment) :
    Satisfies ([] : CNF) a := by
  simp [Satisfies]

@[simp]
theorem satisfies_append (φ ψ : CNF) (a : SAT.Assignment) :
    Satisfies (φ ++ ψ) a ↔ Satisfies φ a ∧ Satisfies ψ a := by
  constructor
  · intro h
    constructor
    · intro c hc
      exact h c (List.mem_append.mpr (Or.inl hc))
    · intro c hc
      exact h c (List.mem_append.mpr (Or.inr hc))
  · intro h c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h.1 c hc
    · exact h.2 c hc

/-- A set of known true variables is closed under all definite Horn clauses. -/
def Closed (φ : CNF) (known : Finset Nat) : Prop :=
  ∀ c ∈ φ, c.premises ⊆ known → ∀ y : Nat, c.head = some y → y ∈ known

/-- A known set triggers a goal/contradiction clause. -/
def HasConflict (φ : CNF) (known : Finset Nat) : Prop :=
  ∃ c ∈ φ, c.IsConflict known

/-- Boolean conflict check for a Horn-CNF formula. -/
def hasConflictBool : CNF → Finset Nat → Bool
  | [], _ => false
  | c :: cs, known => c.conflictBool known || hasConflictBool cs known

theorem hasConflictBool_eq_true_iff (φ : CNF) (known : Finset Nat) :
    hasConflictBool φ known = true ↔ HasConflict φ known := by
  induction φ with
  | nil =>
      simp [hasConflictBool, HasConflict]
  | cons c cs ih =>
      simp [hasConflictBool, HasConflict, ih, Clause.conflictBool_eq_true_iff]

/-- Search the formula for one new head derivable from the current known set. -/
def findNewHead? (φ : CNF) (known remaining : Finset Nat) :
    Option {x : Nat // x ∈ remaining} :=
  match φ with
  | [] => none
  | c :: cs =>
      match c.newHead? known remaining with
      | some y => some y
      | none => findNewHead? cs known remaining

theorem findNewHead?_some {φ : CNF} {known remaining : Finset Nat}
    {y : {x : Nat // x ∈ remaining}}
    (h : findNewHead? φ known remaining = some y) :
    ∃ c ∈ φ, c.premises ⊆ known ∧ c.head = some y.val := by
  induction φ generalizing y with
  | nil =>
      simp [findNewHead?] at h
  | cons c cs ih =>
      simp [findNewHead?] at h
      cases hHead : c.newHead? known remaining with
      | some z =>
          rw [hHead] at h
          injection h with hy
          refine ⟨c, by simp, ?_⟩
          simpa [hy] using Clause.newHead?_some hHead
      | none =>
          rw [hHead] at h
          rcases ih h with ⟨d, hd, hD⟩
          exact ⟨d, by simp [hd], hD⟩

theorem findNewHead?_none {φ : CNF} {known remaining : Finset Nat}
    (h : findNewHead? φ known remaining = none)
    {c : Clause} (hc : c ∈ φ) (hPrem : c.premises ⊆ known)
    {y : Nat} (hHead : c.head = some y) :
    y ∉ remaining := by
  induction φ generalizing c y with
  | nil =>
      simp at hc
  | cons d ds ih =>
      simp [findNewHead?] at h
      cases hNew : d.newHead? known remaining with
      | some z =>
          rw [hNew] at h
          contradiction
      | none =>
          rw [hNew] at h
          simp at hc
          rcases hc with hEq | hc
          · subst hEq
            exact Clause.newHead?_none hNew hPrem hHead
          · exact ih h hc hPrem hHead

theorem clause_vars_subset_vars {φ : CNF} {c : Clause} (hc : c ∈ φ) :
    c.vars ⊆ vars φ := by
  induction φ with
  | nil =>
      simp at hc
  | cons d ds ih =>
      simp [vars] at hc ⊢
      rcases hc with hEq | hc
      · subst hEq
        intro x hx
        exact Finset.mem_union.mpr (Or.inl hx)
      · intro x hx
        exact Finset.mem_union.mpr (Or.inr (ih hc hx))

theorem head_mem_vars {φ : CNF} {c : Clause} (hc : c ∈ φ)
    {y : Nat} (hHead : c.head = some y) :
    y ∈ vars φ :=
  clause_vars_subset_vars hc (Clause.head_mem_vars hHead)

/-- Unit closure with explicit fuel.  Each successful step removes one remaining variable. -/
def saturateFuel : Nat → CNF → Finset Nat → Finset Nat → Finset Nat
  | 0, _, known, _ => known
  | fuel + 1, φ, known, remaining =>
      match findNewHead? φ known remaining with
      | some y => saturateFuel fuel φ (insert y.val known) (remaining.erase y.val)
      | none => known

theorem saturateFuel_model_subset {fuel : Nat} {φ : CNF} {known remaining : Finset Nat}
    {a : SAT.Assignment}
    (hSat : Satisfies φ a)
    (hKnown : ∀ x ∈ known, a x = true) :
    ∀ x ∈ saturateFuel fuel φ known remaining, a x = true := by
  induction fuel generalizing known remaining with
  | zero =>
      simp [saturateFuel]
      intro x hx
      exact hKnown x hx
  | succ fuel ih =>
      simp [saturateFuel]
      cases hFind : findNewHead? φ known remaining with
      | none =>
          simp
          intro x hx
          exact hKnown x hx
      | some y =>
          simp
          apply ih
          intro z hz
          rcases Finset.mem_insert.mp hz with hEq | hzKnown
          · subst hEq
            rcases findNewHead?_some hFind with ⟨c, hc, hPrem, hHead⟩
            have hHeadTrue := hSat c hc (by
              intro p hp
              exact hKnown p (hPrem hp))
            rw [hHead] at hHeadTrue
            exact hHeadTrue
          · exact hKnown z hzKnown

theorem saturateFuel_closed {fuel : Nat} {φ : CNF} {known remaining : Finset Nat}
    (hFuel : remaining.card ≤ fuel)
    (hInv : ∀ y, y ∈ vars φ → y ∉ known → y ∈ remaining) :
    Closed φ (saturateFuel fuel φ known remaining) := by
  induction fuel generalizing known remaining with
  | zero =>
      simp [saturateFuel]
      intro c hc hPrem y hHead
      by_contra hyNot
      have hyVars : y ∈ vars φ := head_mem_vars hc hHead
      have hyRemaining : y ∈ remaining := hInv y hyVars hyNot
      have hCardZero : remaining.card = 0 := Nat.eq_zero_of_le_zero hFuel
      have hEmpty : remaining = ∅ := Finset.card_eq_zero.mp hCardZero
      simp [hEmpty] at hyRemaining
  | succ fuel ih =>
      simp [saturateFuel]
      cases hFind : findNewHead? φ known remaining with
      | none =>
          simp
          intro c hc hPrem y hHead
          by_contra hyNot
          have hyVars : y ∈ vars φ := head_mem_vars hc hHead
          have hyRemaining : y ∈ remaining := hInv y hyVars hyNot
          exact findNewHead?_none hFind hc hPrem hHead hyRemaining
      | some y =>
          simp
          apply ih
          · have hEraseCard : (remaining.erase y.val).card = remaining.card - 1 :=
              Finset.card_erase_of_mem y.property
            omega
          · intro z hzVars hzNotKnown
            have hzNotOld : z ∉ known := by
              intro hz
              exact hzNotKnown (Finset.mem_insert.mpr (Or.inr hz))
            have hzNe : z ≠ y.val := by
              intro hEq
              subst hEq
              exact hzNotKnown (Finset.mem_insert_self _ _)
            exact Finset.mem_erase.mpr ⟨hzNe, hInv z hzVars hzNotOld⟩

/-- Unit closure from the empty set of known variables. -/
def closure (φ : CNF) : Finset Nat :=
  saturateFuel (vars φ).card φ ∅ (vars φ)

theorem closure_model_subset {φ : CNF} {a : SAT.Assignment}
    (hSat : Satisfies φ a) :
    ∀ x ∈ closure φ, a x = true := by
  unfold closure
  exact saturateFuel_model_subset hSat (by simp)

theorem closure_closed (φ : CNF) :
    Closed φ (closure φ) := by
  unfold closure
  apply saturateFuel_closed
  · rfl
  intro y hyVars hyNot
  exact hyVars

/-- The assignment induced by a unit-closed set of true variables. -/
def assignmentOf (known : Finset Nat) : SAT.Assignment :=
  fun x => decide (x ∈ known)

theorem assignmentOf_eq_true_of_mem {known : Finset Nat} {x : Nat}
    (hx : x ∈ known) :
    assignmentOf known x = true := by
  simp [assignmentOf, hx]

theorem mem_of_assignmentOf_eq_true {known : Finset Nat} {x : Nat}
    (hx : assignmentOf known x = true) :
    x ∈ known := by
  by_cases hMem : x ∈ known
  · exact hMem
  · simp [assignmentOf, hMem] at hx

theorem no_satisfying_assignment_of_conflict {φ : CNF} {known : Finset Nat}
    (hConflict : HasConflict φ known)
    (hKnownForced : ∀ a : SAT.Assignment, Satisfies φ a → ∀ x ∈ known, a x = true) :
    ¬ Satisfiable φ := by
  rintro ⟨a, hSat⟩
  rcases hConflict with ⟨c, hc, hHead, hPrem⟩
  have hFalse := hSat c hc (by
    intro x hx
    exact hKnownForced a hSat x (hPrem hx))
  rw [hHead] at hFalse
  exact hFalse

theorem not_satisfiable_of_closure_conflict {φ : CNF}
    (hConflict : HasConflict φ (closure φ)) :
    ¬ Satisfiable φ := by
  apply no_satisfying_assignment_of_conflict hConflict
  intro a hSat
  exact closure_model_subset hSat

theorem satisfiable_of_no_closure_conflict {φ : CNF}
    (hNoConflict : ¬ HasConflict φ (closure φ)) :
    Satisfiable φ := by
  refine ⟨assignmentOf (closure φ), ?_⟩
  intro c hc hPrem
  cases hHead : c.head with
  | some y =>
      apply assignmentOf_eq_true_of_mem
      exact closure_closed φ c hc (by
        intro x hx
        exact mem_of_assignmentOf_eq_true (hPrem x hx)) y hHead
  | none =>
      exfalso
      apply hNoConflict
      exact ⟨c, hc, hHead, by
        intro x hx
        exact mem_of_assignmentOf_eq_true (hPrem x hx)⟩

/-- Boolean Horn-CNF unit-closure solver. -/
def decide (φ : CNF) : Bool :=
  !(hasConflictBool φ (closure φ))

theorem decide_eq_true_iff (φ : CNF) :
    decide φ = true ↔ Satisfiable φ := by
  unfold decide
  cases hConflictBool : hasConflictBool φ (closure φ) with
  | false =>
      have hNoConflict : ¬ HasConflict φ (closure φ) := by
        intro hConflict
        have hTrue := (hasConflictBool_eq_true_iff φ (closure φ)).2 hConflict
        simp [hConflictBool] at hTrue
      simp [satisfiable_of_no_closure_conflict hNoConflict]
  | true =>
      have hConflict : HasConflict φ (closure φ) :=
        (hasConflictBool_eq_true_iff φ (closure φ)).1 hConflictBool
      simp [not_satisfiable_of_closure_conflict hConflict]

theorem decide_eq_false_iff (φ : CNF) :
    decide φ = false ↔ ¬ Satisfiable φ := by
  rw [← decide_eq_true_iff φ]
  cases decide φ <;> simp

/-- Descriptor for the proved direct Horn-CNF unit-closure solver. -/
def unitClosureSolverDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1(c), Horn/weakly-positive tractable route"
    informalClaim := "Horn-CNF formulas are decided by unit closure."
    localTargetSymbol := "ComplexityReduction.Schaefer.Horn.CNF.decide_eq_true_iff"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Horn.CNF.saturateFuel"
      , "ComplexityReduction.Schaefer.Horn.CNF.closure_closed"
      , "ComplexityReduction.Schaefer.Horn.CNF.not_satisfiable_of_closure_conflict"
      , "ComplexityReduction.Schaefer.Horn.CNF.satisfiable_of_no_closure_conflict"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "This proves the direct Horn-CNF/unit-closure solver.  Operational Horn and \
       dual-Horn certificate bridges are provided later in this module; closure-form \
       IsHornLanguage Γ / IsDualHornLanguage Γ characterizations remain separate targets." }

end CNF

/-- Read an arity-indexed tuple as a total assignment on natural-number indices. -/
def tupleAssignment {k : Nat} (t : CSP.BoolTuple k) : SAT.Assignment :=
  fun x => if h : x < k then t ⟨x, h⟩ else false

@[simp]
theorem tupleAssignment_of_lt {k : Nat} (t : CSP.BoolTuple k) {x : Nat} (h : x < k) :
    tupleAssignment t x = t ⟨x, h⟩ := by
  simp [tupleAssignment, h]

/--
An operational Horn-CNF representation of one local Boolean relation.

The clauses are over arity indices `0, ..., R.arity - 1`; `correct` says that
the direct Horn-CNF formula accepts exactly the tuples accepted by `R`.
-/
structure RelationCertificate (R : CSP.BoolRel) where
  clauses : CNF
  withinArity : ∀ c ∈ clauses, c.vars ⊆ Finset.range R.arity
  correct : ∀ t : CSP.BoolTuple R.arity,
    R.Holds t ↔ CNF.Satisfies clauses (tupleAssignment t)

/-- An operational Horn representation for every symbol of a fixed language. -/
abbrev LanguageCertificate (Γ : CSP.BoolLanguage) : Type :=
  ∀ s : Γ.Symbol, RelationCertificate (Γ.relationOf s)

namespace RelationCertificate

/-- A certificate induces the Schaefer closure-under-AND Horn predicate. -/
theorem isHorn {R : CSP.BoolRel} (cert : RelationCertificate R) : IsHorn R := by
  intro a b ha hb
  rw [cert.correct] at ha hb ⊢
  intro c hc hPrem
  have hVars := cert.withinArity c hc
  have hPremA : ∀ x ∈ c.premises, tupleAssignment a x = true := by
    intro x hx
    have hxRange : x ∈ Finset.range R.arity := hVars (Clause.premise_mem_vars hx)
    have hxLt : x < R.arity := by
      simpa using hxRange
    have hAnd := hPrem x hx
    have hAnd' : a ⟨x, hxLt⟩ && b ⟨x, hxLt⟩ = true := by
      simpa [tupleAssignment, BoolTuple.pointwiseAnd, hxLt] using hAnd
    have hA : a ⟨x, hxLt⟩ = true := by
      cases haVal : a ⟨x, hxLt⟩ <;> cases hbVal : b ⟨x, hxLt⟩ <;>
        simp [haVal, hbVal] at hAnd' ⊢
    simpa [tupleAssignment, hxLt] using hA
  have hPremB : ∀ x ∈ c.premises, tupleAssignment b x = true := by
    intro x hx
    have hxRange : x ∈ Finset.range R.arity := hVars (Clause.premise_mem_vars hx)
    have hxLt : x < R.arity := by
      simpa using hxRange
    have hAnd := hPrem x hx
    have hAnd' : a ⟨x, hxLt⟩ && b ⟨x, hxLt⟩ = true := by
      simpa [tupleAssignment, BoolTuple.pointwiseAnd, hxLt] using hAnd
    have hB : b ⟨x, hxLt⟩ = true := by
      cases haVal : a ⟨x, hxLt⟩ <;> cases hbVal : b ⟨x, hxLt⟩ <;>
        simp [haVal, hbVal] at hAnd' ⊢
    simpa [tupleAssignment, hxLt] using hB
  cases hHead : c.head with
  | none =>
      have hFalse := ha c hc hPremA
      simp [hHead] at hFalse
  | some y =>
      have hyRange : y ∈ Finset.range R.arity := hVars (Clause.head_mem_vars hHead)
      have hyLt : y < R.arity := by
        simpa using hyRange
      have haHead := ha c hc hPremA
      have hbHead := hb c hc hPremB
      rw [hHead] at haHead hbHead
      have hA : a ⟨y, hyLt⟩ = true := by
        simpa [tupleAssignment, hyLt] using haHead
      have hB : b ⟨y, hyLt⟩ = true := by
        simpa [tupleAssignment, hyLt] using hbHead
      simp [tupleAssignment, hyLt, hA, hB]

end RelationCertificate

/-- Natural-number indices where an arity-indexed tuple is true. -/
def tuplePremises {k : Nat} (t : CSP.BoolTuple k) : Finset Nat :=
  ((Finset.univ : Finset (Fin k)).filter fun i => t i = true).image fun i => i.val

theorem mem_tuplePremises_of_eq_true {k : Nat} {t : CSP.BoolTuple k} {i : Fin k}
    (hi : t i = true) :
    i.val ∈ tuplePremises t := by
  unfold tuplePremises
  exact Finset.mem_image.mpr ⟨i, by simp [hi], rfl⟩

theorem tuplePremises_subset_range {k : Nat} (t : CSP.BoolTuple k) :
    tuplePremises t ⊆ Finset.range k := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  exact Finset.mem_range.mpr i.isLt

theorem tupleAssignment_true_of_mem_tuplePremises {k : Nat} {t : CSP.BoolTuple k}
    {x : Nat} (hx : x ∈ tuplePremises t) :
    tupleAssignment t x = true := by
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  have hTrue : t i = true := by
    simpa using hi
  simpa [tupleAssignment] using hTrue

theorem tuple_eq_true_of_premise_satisfied {k : Nat} {t u : CSP.BoolTuple k}
    (hPrem : ∀ x ∈ tuplePremises t, tupleAssignment u x = true) :
    ∀ i : Fin k, t i = true → u i = true := by
  intro i hi
  have h := hPrem i.val (mem_tuplePremises_of_eq_true hi)
  simpa [tupleAssignment] using h

/-- Pointwise meet of a finite tuple set, with the empty meet equal to all-true. -/
noncomputable def tupleMeetFinset {k : Nat} (S : Finset (CSP.BoolTuple k)) :
    CSP.BoolTuple k :=
  fun i => by
    classical
    exact decide (∀ t ∈ S, t i = true)

theorem tupleMeetFinset_eq_true_iff {k : Nat} (S : Finset (CSP.BoolTuple k))
    (i : Fin k) :
    tupleMeetFinset S i = true ↔ ∀ t ∈ S, t i = true := by
  classical
  simp [tupleMeetFinset, decide_eq_true_eq]

theorem tupleMeetFinset_insert {k : Nat} (x : CSP.BoolTuple k)
    {S : Finset (CSP.BoolTuple k)} :
    tupleMeetFinset (insert x S) = BoolTuple.pointwiseAnd x (tupleMeetFinset S) := by
  classical
  funext i
  by_cases hxTrue : x i = true
  · by_cases hSTrue : ∀ t ∈ S, t i = true
    · simp [tupleMeetFinset, BoolTuple.pointwiseAnd, hxTrue]
    · simp [tupleMeetFinset, BoolTuple.pointwiseAnd, hxTrue, hSTrue]
  · have hxFalse : x i = false := by
      cases hxi : x i with
      | false => rfl
      | true => exact False.elim (hxTrue hxi)
    simp [tupleMeetFinset, BoolTuple.pointwiseAnd, hxFalse]

theorem tupleMeetFinset_singleton {k : Nat} (x : CSP.BoolTuple k) :
    tupleMeetFinset ({x} : Finset (CSP.BoolTuple k)) = x := by
  classical
  funext i
  by_cases hxTrue : x i = true
  · simp [tupleMeetFinset, hxTrue]
  · have hxFalse : x i = false := by
      cases hxi : x i with
      | false => rfl
      | true => exact False.elim (hxTrue hxi)
    simp [tupleMeetFinset, hxFalse]

theorem isHorn_tupleMeet_holds {R : CSP.BoolRel} (hHorn : IsHorn R)
    {S : Finset (CSP.BoolTuple R.arity)}
    (hNonempty : S.Nonempty) (hS : ∀ t ∈ S, R.Holds t) :
    R.Holds (tupleMeetFinset S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp at hNonempty
  | insert x S hxNotMem ih =>
      by_cases hEmpty : S = ∅
      · subst S
        have hEq : tupleMeetFinset (insert x ∅) = x := by
          simpa using (tupleMeetFinset_singleton x)
        rw [hEq]
        exact hS x (by simp)
      · have hSNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
        have hMeetS : R.Holds (tupleMeetFinset S) :=
          ih hSNonempty (by
            intro t ht
            exact hS t (by simp [ht]))
        have hxHold : R.Holds x := hS x (by simp)
        have hEq :
            tupleMeetFinset (insert x S) = BoolTuple.pointwiseAnd x (tupleMeetFinset S) :=
          tupleMeetFinset_insert x
        simpa [hEq] using hHorn x (tupleMeetFinset S) hxHold hMeetS

/-- Accepted tuples that agree with a falsifying tuple on all true coordinates. -/
noncomputable def candidates (R : CSP.BoolRel) (t : CSP.BoolTuple R.arity) :
    Finset (CSP.BoolTuple R.arity) :=
  R.accepts.filter fun u => ∀ i : Fin R.arity, t i = true → u i = true

theorem mem_candidates_iff (R : CSP.BoolRel) (t u : CSP.BoolTuple R.arity) :
    u ∈ candidates R t ↔
      R.Holds u ∧ ∀ i : Fin R.arity, t i = true → u i = true := by
  classical
  unfold candidates CSP.BoolRel.Holds
  simp

theorem mem_candidates_of_holds_of_premises {R : CSP.BoolRel}
    {t u : CSP.BoolTuple R.arity} (hu : R.Holds u)
    (hPrem : ∀ x ∈ tuplePremises t, tupleAssignment u x = true) :
    u ∈ candidates R t :=
  (mem_candidates_iff R t u).2
    ⟨hu, tuple_eq_true_of_premise_satisfied hPrem⟩

theorem exists_separating_index {R : CSP.BoolRel} (hHorn : IsHorn R)
    (p : {t : CSP.BoolTuple R.arity // t ∈ R.falsifyingTuples})
    (hNonempty : (candidates R p.val).Nonempty) :
    ∃ j : Fin R.arity,
      p.val j = false ∧ tupleMeetFinset (candidates R p.val) j = true := by
  classical
  have htFalse : p.val ∉ R.accepts :=
    (CSP.BoolRel.mem_falsifyingTuples_iff R p.val).1 p.property
  have hMeetHolds : R.Holds (tupleMeetFinset (candidates R p.val)) :=
    isHorn_tupleMeet_holds hHorn hNonempty (by
      intro u hu
      exact ((mem_candidates_iff R p.val u).1 hu).1)
  have hTrueOfT :
      ∀ i : Fin R.arity,
        p.val i = true → tupleMeetFinset (candidates R p.val) i = true := by
    intro i hi
    exact (tupleMeetFinset_eq_true_iff (candidates R p.val) i).2 (by
      intro u hu
      exact ((mem_candidates_iff R p.val u).1 hu).2 i hi)
  by_contra hNoIndex
  have hMeetEq : tupleMeetFinset (candidates R p.val) = p.val := by
    funext i
    by_cases ht : p.val i = true
    · have hm := hTrueOfT i ht
      simp [ht, hm]
    · have htFalseBool : p.val i = false := by
        cases hti : p.val i with
        | false => rfl
        | true => exact False.elim (ht hti)
      by_cases hm : tupleMeetFinset (candidates R p.val) i = true
      · exact False.elim (hNoIndex ⟨i, htFalseBool, hm⟩)
      · have hmFalse : tupleMeetFinset (candidates R p.val) i = false := by
          cases hmi : tupleMeetFinset (candidates R p.val) i with
          | false => rfl
          | true => exact False.elim (hm hmi)
        simp [htFalseBool, hmFalse]
  exact htFalse (by
    simpa [hMeetEq] using hMeetHolds)

noncomputable def separatingHead {R : CSP.BoolRel} (hHorn : IsHorn R)
    (p : {t : CSP.BoolTuple R.arity // t ∈ R.falsifyingTuples}) : Option Nat :=
  if hNonempty : (candidates R p.val).Nonempty then
    some (Classical.choose (exists_separating_index hHorn p hNonempty)).val
  else
    none

/-- Horn clause that separates one falsifying tuple from all accepted tuples. -/
noncomputable def separatingClause {R : CSP.BoolRel} (hHorn : IsHorn R)
    (p : {t : CSP.BoolTuple R.arity // t ∈ R.falsifyingTuples}) : Clause where
  premises := tuplePremises p.val
  head := separatingHead hHorn p

theorem separatingClause_withinArity {R : CSP.BoolRel} (hHorn : IsHorn R)
    (p : {t : CSP.BoolTuple R.arity // t ∈ R.falsifyingTuples}) :
    (separatingClause hHorn p).vars ⊆ Finset.range R.arity := by
  classical
  intro x hx
  have hx' := hx
  simp [separatingClause, Clause.vars] at hx'
  rcases hx' with hxPrem | hxHead
  · exact tuplePremises_subset_range p.val hxPrem
  · unfold separatingHead at hxHead
    by_cases hNonempty : (candidates R p.val).Nonempty
    · simp [hNonempty] at hxHead
      subst x
      exact Finset.mem_range.mpr
        (Classical.choose (exists_separating_index hHorn p hNonempty)).isLt
    · simp [hNonempty] at hxHead

theorem accepted_satisfies_separatingClause {R : CSP.BoolRel} (hHorn : IsHorn R)
    (p : {t : CSP.BoolTuple R.arity // t ∈ R.falsifyingTuples})
    {u : CSP.BoolTuple R.arity} (hu : R.Holds u) :
    Clause.Satisfies (separatingClause hHorn p) (tupleAssignment u) := by
  intro hPrem
  have huCand : u ∈ candidates R p.val :=
    mem_candidates_of_holds_of_premises hu (by
      intro x hx
      exact hPrem x (by simpa [separatingClause] using hx))
  unfold separatingClause separatingHead
  by_cases hNonempty : (candidates R p.val).Nonempty
  · simp [hNonempty]
    let j := Classical.choose (exists_separating_index hHorn p hNonempty)
    have hj := Classical.choose_spec (exists_separating_index hHorn p hNonempty)
    have huj : u j = true :=
      (tupleMeetFinset_eq_true_iff (candidates R p.val) j).1 hj.2 u huCand
    simpa [tupleAssignment] using huj
  · have hEmpty : u ∉ candidates R p.val := by
      intro hu'
      exact hNonempty ⟨u, hu'⟩
    exact False.elim (hEmpty huCand)

theorem falsifying_tuple_violates_separatingClause {R : CSP.BoolRel}
    (hHorn : IsHorn R)
    (p : {t : CSP.BoolTuple R.arity // t ∈ R.falsifyingTuples}) :
    ¬ Clause.Satisfies (separatingClause hHorn p) (tupleAssignment p.val) := by
  intro hSat
  have hPrem :
      ∀ x ∈ (separatingClause hHorn p).premises, tupleAssignment p.val x = true := by
    intro x hx
    exact tupleAssignment_true_of_mem_tuplePremises (by
      simpa [separatingClause] using hx)
  have hResult := hSat hPrem
  unfold separatingClause separatingHead at hResult
  by_cases hNonempty : (candidates R p.val).Nonempty
  · simp [hNonempty] at hResult
    let j := Classical.choose (exists_separating_index hHorn p hNonempty)
    have hj := Classical.choose_spec (exists_separating_index hHorn p hNonempty)
    have htjTrue : p.val j = true := by
      simpa [tupleAssignment] using hResult
    have htjFalse : p.val j = false := hj.1
    simp [htjFalse] at htjTrue
  · simp [hNonempty] at hResult

/-- A finite relation closed under pointwise AND has an operational Horn certificate. -/
noncomputable def relationCertificateOfIsHorn {R : CSP.BoolRel} (hHorn : IsHorn R) :
    RelationCertificate R where
  clauses := R.falsifyingTuples.attach.toList.map (separatingClause hHorn)
  withinArity := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨p, _hp, rfl⟩
    exact separatingClause_withinArity hHorn p
  correct := by
    intro t
    constructor
    · intro ht c hc
      rcases List.mem_map.mp hc with ⟨p, _hp, rfl⟩
      exact accepted_satisfies_separatingClause hHorn p ht
    · intro hCNF
      by_contra ht
      have htFalsifying : t ∈ R.falsifyingTuples :=
        (CSP.BoolRel.mem_falsifyingTuples_iff R t).2 ht
      let p : {t : CSP.BoolTuple R.arity // t ∈ R.falsifyingTuples} :=
        ⟨t, htFalsifying⟩
      have hpMem : p ∈ R.falsifyingTuples.attach.toList := by
        simp [p]
      have hClauseMem :
          separatingClause hHorn p ∈
            R.falsifyingTuples.attach.toList.map (separatingClause hHorn) :=
        List.mem_map.mpr ⟨p, hpMem, rfl⟩
      exact falsifying_tuple_violates_separatingClause hHorn p
        (hCNF (separatingClause hHorn p) hClauseMem)

/-- Lift the Horn closure characterization from one relation to a finite language. -/
noncomputable def languageCertificateOfIsHornLanguage {Γ : CSP.BoolLanguage}
    (hΓ : IsHornLanguage Γ) :
    LanguageCertificate Γ :=
  fun s => relationCertificateOfIsHorn (hΓ s)

@[simp]
theorem boolTuple_complement_involutive {k : Nat} (t : CSP.BoolTuple k) :
    BoolTuple.complement (BoolTuple.complement t) = t := by
  funext i
  cases h : t i <;> simp [BoolTuple.complement, h]

/-- Complement a relation so dual-Horn closure becomes Horn closure. -/
noncomputable def dualToHornRelation (R : CSP.BoolRel) : CSP.BoolRel where
  arity := R.arity
  accepts :=
    (Finset.univ : Finset (CSP.BoolTuple R.arity)).filter fun t =>
      R.Holds (BoolTuple.complement t)

@[simp]
theorem dualToHornRelation_holds_iff (R : CSP.BoolRel)
    (t : CSP.BoolTuple (dualToHornRelation R).arity) :
    (dualToHornRelation R).Holds t ↔ R.Holds (BoolTuple.complement t) := by
  classical
  change
    t ∈ ((Finset.univ : Finset (CSP.BoolTuple R.arity)).filter fun u =>
      R.Holds (BoolTuple.complement u)) ↔ R.Holds (BoolTuple.complement t)
  constructor
  · intro ht
    exact (Finset.mem_filter.mp ht).2
  · intro ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩

theorem isHorn_dualToHornRelation_of_isDualHorn {R : CSP.BoolRel}
    (hDual : IsDualHorn R) :
    IsHorn (dualToHornRelation R) := by
  intro a b ha hb
  rw [dualToHornRelation_holds_iff] at ha hb ⊢
  have hOr := hDual (BoolTuple.complement a) (BoolTuple.complement b) ha hb
  have hEq :
      BoolTuple.complement (BoolTuple.pointwiseAnd a b) =
        BoolTuple.pointwiseOr (BoolTuple.complement a) (BoolTuple.complement b) := by
    funext i
    cases ha : a i <;> cases hb : b i <;>
      simp [BoolTuple.complement, BoolTuple.pointwiseAnd, BoolTuple.pointwiseOr, ha, hb]
  change BoolTuple.complement (BoolTuple.pointwiseAnd a b) ∈ R.accepts
  change BoolTuple.pointwiseOr (BoolTuple.complement a) (BoolTuple.complement b) ∈
    R.accepts at hOr
  rw [hEq]
  exact hOr

/-- Instantiate one arity-indexed certificate variable at the variables of a CSP constraint. -/
def instantiateIndex {Γ : CSP.BoolLanguage} (c : CSP.Constraint Γ) (x : Nat) : Nat :=
  if h : x < (Γ.relationOf c.symbol).arity then c.vars ⟨x, h⟩ else x

theorem tupleAssignment_assignmentTuple_eq {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint Γ) (a : SAT.Assignment) {x : Nat}
    (hx : x < (Γ.relationOf c.symbol).arity) :
    tupleAssignment (c.assignmentTuple a) x = a (instantiateIndex c x) := by
  simp [tupleAssignment, instantiateIndex, hx, CSP.Constraint.assignmentTuple]

theorem assignment_eq_tupleAssignment_of_in_range {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint Γ) (a : SAT.Assignment) {x : Nat}
    (hx : x ∈ Finset.range (Γ.relationOf c.symbol).arity) :
    a (instantiateIndex c x) = tupleAssignment (c.assignmentTuple a) x := by
  have hxLt : x < (Γ.relationOf c.symbol).arity := by
    simpa using hx
  exact (tupleAssignment_assignmentTuple_eq c a hxLt).symm

/-- Instantiate one arity-indexed Horn clause at the variables of a CSP constraint. -/
def instantiateClause {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint Γ) (clause : Clause) : Clause :=
  clause.mapVars (instantiateIndex c)

/-- Instantiate a certificate block at one CSP constraint. -/
def instantiateCNF {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint Γ) (clauses : CNF) : CNF :=
  clauses.map (instantiateClause c)

end Horn
end Schaefer
end ComplexityReduction
