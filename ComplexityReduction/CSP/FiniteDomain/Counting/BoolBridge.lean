/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.Counting.Bijection
import ComplexityReduction.CSP.FiniteDomain.BoolBridge
import ComplexityReduction.CSP.FiniteSupport

/-!
Count-preserving bridges from the existing Boolean CSP surface into the
finite-domain `Bool` and `Fin 2` surfaces.

The Boolean CSP API uses total assignments, so this file mirrors the
finite-domain counting layer by counting valuations on the finite support of a
formula.  The two bridge theorems are exact cardinality equalities induced by
explicit equivalences of finite-support solution valuations.
-/

namespace ComplexityReduction
namespace CSP

namespace Formula

/-- Finite set of satisfying Boolean valuations on the variables mentioned by a formula. -/
noncomputable def solutionSet {Γ : BoolLanguage} (φ : Formula Γ) :
    Finset ({x : Nat // x ∈ FiniteSupport.formulaVars φ} → Bool) := by
  classical
  letI : Fintype {x : Nat // x ∈ FiniteSupport.formulaVars φ} :=
    Finset.Subtype.fintype (FiniteSupport.formulaVars φ)
  exact
    (Finset.univ : Finset ({x : Nat // x ∈ FiniteSupport.formulaVars φ} → Bool)).filter
      fun values => Satisfies φ (FiniteSupport.assignmentOf values)

@[simp]
theorem mem_solutionSet {Γ : BoolLanguage} (φ : Formula Γ)
    (values : {x : Nat // x ∈ FiniteSupport.formulaVars φ} → Bool) :
    values ∈ solutionSet φ ↔ Satisfies φ (FiniteSupport.assignmentOf values) := by
  classical
  unfold solutionSet
  simp

/-- Number of finite-support satisfying valuations of a Boolean CSP formula. -/
noncomputable def solutionCount {Γ : BoolLanguage} (φ : Formula Γ) : Nat :=
  (solutionSet φ).card

/-- A finite-support solution valuation of a Boolean CSP formula. -/
abbrev SolutionValuation {Γ : BoolLanguage} (φ : Formula Γ) : Type :=
  { values : {x : Nat // x ∈ FiniteSupport.formulaVars φ} → Bool // values ∈ solutionSet φ }

/-- Boolean solution valuations are finite because their support is finite. -/
noncomputable instance solutionValuation_fintype {Γ : BoolLanguage} (φ : Formula Γ) :
    Fintype (SolutionValuation φ) := by
  classical
  unfold SolutionValuation
  infer_instance

/-- The Boolean finite-support solution set is nonempty exactly when the formula is satisfiable. -/
theorem solutionSet_nonempty_iff_satisfiable {Γ : BoolLanguage} (φ : Formula Γ) :
    (solutionSet φ).Nonempty ↔ Formula.Satisfiable φ := by
  classical
  constructor
  · rintro ⟨values, hvalues⟩
    exact ⟨FiniteSupport.assignmentOf values, (mem_solutionSet φ values).1 hvalues⟩
  · rintro ⟨a, hSat⟩
    let values : {x : Nat // x ∈ FiniteSupport.formulaVars φ} → Bool := fun x => a x.val
    refine ⟨values, (mem_solutionSet φ values).2 ?_⟩
    exact (FiniteSupport.formula_satisfies_iff_of_agree (φ := φ)
      (a := FiniteSupport.assignmentOf values) (b := a) (by
        intro x hx
        simp [FiniteSupport.assignmentOf, hx, values])).2 hSat

/-- Positive Boolean solution count is the finite-support counting form of satisfiability. -/
theorem solutionCount_pos_iff_satisfiable {Γ : BoolLanguage} (φ : Formula Γ) :
    0 < solutionCount φ ↔ Formula.Satisfiable φ := by
  rw [solutionCount, Finset.card_pos]
  exact solutionSet_nonempty_iff_satisfiable φ

end Formula

namespace FiniteDomain
namespace BoolBridge

@[simp]
theorem constraintVars_constraintOfBoolConstraint {Γ : BoolLanguage} (c : CSP.Constraint Γ) :
    FiniteSupport.constraintVars (constraintOfBoolConstraint c) =
      CSP.FiniteSupport.constraintVars c :=
  rfl

@[simp]
theorem constraintVars_constraintFin2OfBoolConstraint {Γ : BoolLanguage}
    (c : CSP.Constraint Γ) :
    FiniteSupport.constraintVars (constraintFin2OfBoolConstraint c) =
      CSP.FiniteSupport.constraintVars c :=
  rfl

@[simp]
theorem formulaVars_formulaOfBoolFormula {Γ : BoolLanguage} (φ : CSP.Formula Γ) :
    FiniteSupport.formulaVars (formulaOfBoolFormula φ) =
      CSP.FiniteSupport.formulaVars φ := by
  induction φ with
  | nil =>
      rfl
  | cons c φ ih =>
      change
        FiniteSupport.constraintVars (constraintOfBoolConstraint c) ∪
            FiniteSupport.formulaVars (formulaOfBoolFormula φ) =
          CSP.FiniteSupport.constraintVars c ∪ CSP.FiniteSupport.formulaVars φ
      simp [ih]

@[simp]
theorem formulaVars_formulaFin2OfBoolFormula {Γ : BoolLanguage} (φ : CSP.Formula Γ) :
    FiniteSupport.formulaVars (formulaFin2OfBoolFormula φ) =
      CSP.FiniteSupport.formulaVars φ := by
  induction φ with
  | nil =>
      rfl
  | cons c φ ih =>
      change
        FiniteSupport.constraintVars (constraintFin2OfBoolConstraint c) ∪
            FiniteSupport.formulaVars (formulaFin2OfBoolFormula φ) =
          CSP.FiniteSupport.constraintVars c ∪ CSP.FiniteSupport.formulaVars φ
      simp [ih]

/-- Cast a Boolean finite-support valuation to the support of its finite-domain `Bool` image. -/
def valuesToFormulaOfBoolFormula {Γ : BoolLanguage} (φ : CSP.Formula Γ)
    (values : {x : Nat // x ∈ CSP.FiniteSupport.formulaVars φ} → Bool) :
    {x : Nat // x ∈ FiniteSupport.formulaVars (formulaOfBoolFormula φ)} → Bool :=
  fun x => values ⟨x.val, by
    have hvars := formulaVars_formulaOfBoolFormula φ
    simpa [hvars] using x.property⟩

/-- Cast a finite-domain `Bool` bridge valuation back to the source Boolean support. -/
def valuesFromFormulaOfBoolFormula {Γ : BoolLanguage} (φ : CSP.Formula Γ)
    (values : {x : Nat // x ∈ FiniteSupport.formulaVars (formulaOfBoolFormula φ)} → Bool) :
    {x : Nat // x ∈ CSP.FiniteSupport.formulaVars φ} → Bool :=
  fun x => values ⟨x.val, by
    have hvars := formulaVars_formulaOfBoolFormula φ
    simp [hvars]⟩

private theorem assignmentOf_valuesToFormulaOfBoolFormula_eq_of_mem {Γ : BoolLanguage}
    (φ : CSP.Formula Γ)
    (values : {x : Nat // x ∈ CSP.FiniteSupport.formulaVars φ} → Bool)
    {x : Nat} (hx : x ∈ CSP.FiniteSupport.formulaVars φ) :
    FiniteSupport.assignmentOf (valuesToFormulaOfBoolFormula φ values) x =
      CSP.FiniteSupport.assignmentOf values x := by
  have hxfd : x ∈ FiniteSupport.formulaVars (formulaOfBoolFormula φ) := by
    have hvars := formulaVars_formulaOfBoolFormula φ
    simpa [hvars] using hx
  simp
    [ FiniteSupport.assignmentOf
    , CSP.FiniteSupport.assignmentOf
    , valuesToFormulaOfBoolFormula
    , hx ]

private theorem assignmentOf_valuesFromFormulaOfBoolFormula_eq_of_mem {Γ : BoolLanguage}
    (φ : CSP.Formula Γ)
    (values : {x : Nat // x ∈ FiniteSupport.formulaVars (formulaOfBoolFormula φ)} → Bool)
    {x : Nat} (hx : x ∈ CSP.FiniteSupport.formulaVars φ) :
    CSP.FiniteSupport.assignmentOf (valuesFromFormulaOfBoolFormula φ values) x =
      FiniteSupport.assignmentOf values x := by
  have hxfd : x ∈ FiniteSupport.formulaVars (formulaOfBoolFormula φ) := by
    have hvars := formulaVars_formulaOfBoolFormula φ
    simpa [hvars] using hx
  simp
    [ FiniteSupport.assignmentOf
    , CSP.FiniteSupport.assignmentOf
    , valuesFromFormulaOfBoolFormula
    , hx ]

private theorem valuesToFormulaOfBoolFormula_mem_solutionSet {Γ : BoolLanguage}
    (φ : CSP.Formula Γ)
    {values : {x : Nat // x ∈ CSP.FiniteSupport.formulaVars φ} → Bool}
    (hvalues : values ∈ CSP.Formula.solutionSet φ) :
    valuesToFormulaOfBoolFormula φ values ∈
      Formula.solutionSet (formulaOfBoolFormula φ) := by
  have hSource :
      CSP.Formula.Satisfies φ (CSP.FiniteSupport.assignmentOf values) :=
    (CSP.Formula.mem_solutionSet φ values).1 hvalues
  have hAgree :
      ∀ x ∈ CSP.FiniteSupport.formulaVars φ,
        FiniteSupport.assignmentOf (valuesToFormulaOfBoolFormula φ values) x =
          CSP.FiniteSupport.assignmentOf values x := by
    intro x hx
    exact assignmentOf_valuesToFormulaOfBoolFormula_eq_of_mem φ values hx
  have hSource' :
      CSP.Formula.Satisfies φ
        (FiniteSupport.assignmentOf (valuesToFormulaOfBoolFormula φ values)) :=
    (CSP.FiniteSupport.formula_satisfies_iff_of_agree (φ := φ)
      (a := FiniteSupport.assignmentOf (valuesToFormulaOfBoolFormula φ values))
      (b := CSP.FiniteSupport.assignmentOf values) hAgree).2 hSource
  exact (Formula.mem_solutionSet (formulaOfBoolFormula φ)
    (valuesToFormulaOfBoolFormula φ values)).2
      ((formulaOfBoolFormula_satisfies_iff φ
        (FiniteSupport.assignmentOf (valuesToFormulaOfBoolFormula φ values))).2 hSource')

private theorem valuesFromFormulaOfBoolFormula_mem_solutionSet {Γ : BoolLanguage}
    (φ : CSP.Formula Γ)
    {values : {x : Nat // x ∈ FiniteSupport.formulaVars (formulaOfBoolFormula φ)} → Bool}
    (hvalues : values ∈ Formula.solutionSet (formulaOfBoolFormula φ)) :
    valuesFromFormulaOfBoolFormula φ values ∈ CSP.Formula.solutionSet φ := by
  have hTarget :
      Formula.Satisfies (formulaOfBoolFormula φ) (FiniteSupport.assignmentOf values) :=
    (Formula.mem_solutionSet (formulaOfBoolFormula φ) values).1 hvalues
  have hSource :
      CSP.Formula.Satisfies φ (FiniteSupport.assignmentOf values) :=
    (formulaOfBoolFormula_satisfies_iff φ (FiniteSupport.assignmentOf values)).1 hTarget
  have hAgree :
      ∀ x ∈ CSP.FiniteSupport.formulaVars φ,
        CSP.FiniteSupport.assignmentOf (valuesFromFormulaOfBoolFormula φ values) x =
          FiniteSupport.assignmentOf values x := by
    intro x hx
    exact assignmentOf_valuesFromFormulaOfBoolFormula_eq_of_mem φ values hx
  have hSource' :
      CSP.Formula.Satisfies φ
        (CSP.FiniteSupport.assignmentOf (valuesFromFormulaOfBoolFormula φ values)) :=
    (CSP.FiniteSupport.formula_satisfies_iff_of_agree (φ := φ)
      (a := CSP.FiniteSupport.assignmentOf (valuesFromFormulaOfBoolFormula φ values))
      (b := FiniteSupport.assignmentOf values) hAgree).2 hSource
  exact (CSP.Formula.mem_solutionSet φ
    (valuesFromFormulaOfBoolFormula φ values)).2 hSource'

/-- Boolean formulas and their finite-domain `Bool` images have equivalent solution valuations. -/
noncomputable def solutionEquiv_formulaOfBoolFormula {Γ : BoolLanguage}
    (φ : CSP.Formula Γ) :
    CSP.Formula.SolutionValuation φ ≃
      Formula.SolutionValuation (formulaOfBoolFormula φ) where
  toFun sol :=
    ⟨ valuesToFormulaOfBoolFormula φ sol.1
    , valuesToFormulaOfBoolFormula_mem_solutionSet φ sol.2 ⟩
  invFun sol :=
    ⟨ valuesFromFormulaOfBoolFormula φ sol.1
    , valuesFromFormulaOfBoolFormula_mem_solutionSet φ sol.2 ⟩
  left_inv sol := by
    apply Subtype.ext
    funext x
    simp [valuesFromFormulaOfBoolFormula, valuesToFormulaOfBoolFormula]
  right_inv sol := by
    apply Subtype.ext
    funext x
    simp [valuesFromFormulaOfBoolFormula, valuesToFormulaOfBoolFormula]

/-- Transporting a Boolean formula to the finite-domain `Bool` surface preserves solution count. -/
theorem solutionCount_formulaOfBoolFormula {Γ : BoolLanguage} (φ : CSP.Formula Γ) :
    Formula.solutionCount (formulaOfBoolFormula φ) = CSP.Formula.solutionCount φ := by
  classical
  unfold Formula.solutionCount CSP.Formula.solutionCount
  let e := solutionEquiv_formulaOfBoolFormula φ
  have hCard :
      (CSP.Formula.solutionSet φ).card =
        (Formula.solutionSet (formulaOfBoolFormula φ)).card := by
    refine Finset.card_bij
      (fun values hvalues => (e ⟨values, hvalues⟩).1)
      (fun values hvalues => (e ⟨values, hvalues⟩).2)
      ?inj
      ?surj
    · intro a ha b hb h
      have hSubtype : e ⟨a, ha⟩ = e ⟨b, hb⟩ := by
        exact Subtype.ext h
      exact congrArg Subtype.val (e.injective hSubtype)
    · intro b hb
      refine ⟨(e.symm ⟨b, hb⟩).1, (e.symm ⟨b, hb⟩).2, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
  exact hCard.symm

/-- Encode a Boolean finite-support valuation as a `Fin 2` bridge valuation. -/
def valuesToFormulaFin2OfBoolFormula {Γ : BoolLanguage} (φ : CSP.Formula Γ)
    (values : {x : Nat // x ∈ CSP.FiniteSupport.formulaVars φ} → Bool) :
    {x : Nat // x ∈ FiniteSupport.formulaVars (formulaFin2OfBoolFormula φ)} → Fin 2 :=
  fun x => boolToFin2 (values ⟨x.val, by
    have hvars := formulaVars_formulaFin2OfBoolFormula φ
    simpa [hvars] using x.property⟩)

/-- Decode a `Fin 2` bridge valuation back to the Boolean source support. -/
def valuesFromFormulaFin2OfBoolFormula {Γ : BoolLanguage} (φ : CSP.Formula Γ)
    (values : {x : Nat // x ∈ FiniteSupport.formulaVars (formulaFin2OfBoolFormula φ)} → Fin 2) :
    {x : Nat // x ∈ CSP.FiniteSupport.formulaVars φ} → Bool :=
  fun x => fin2ToBool (values ⟨x.val, by
    have hvars := formulaVars_formulaFin2OfBoolFormula φ
    simp [hvars]⟩)

private theorem assignmentOf_valuesToFormulaFin2OfBoolFormula_eq_of_mem {Γ : BoolLanguage}
    (φ : CSP.Formula Γ)
    (values : {x : Nat // x ∈ CSP.FiniteSupport.formulaVars φ} → Bool)
    {x : Nat} (hx : x ∈ CSP.FiniteSupport.formulaVars φ) :
    assignmentFin2ToBool
        (FiniteSupport.assignmentOf (valuesToFormulaFin2OfBoolFormula φ values)) x =
      CSP.FiniteSupport.assignmentOf values x := by
  have hxfd : x ∈ FiniteSupport.formulaVars (formulaFin2OfBoolFormula φ) := by
    have hvars := formulaVars_formulaFin2OfBoolFormula φ
    simpa [hvars] using hx
  simp
    [ assignmentFin2ToBool
    , FiniteSupport.assignmentOf
    , CSP.FiniteSupport.assignmentOf
    , valuesToFormulaFin2OfBoolFormula
    , hx ]

private theorem assignmentOf_valuesFromFormulaFin2OfBoolFormula_eq_of_mem {Γ : BoolLanguage}
    (φ : CSP.Formula Γ)
    (values : {x : Nat // x ∈ FiniteSupport.formulaVars (formulaFin2OfBoolFormula φ)} → Fin 2)
    {x : Nat} (hx : x ∈ CSP.FiniteSupport.formulaVars φ) :
    CSP.FiniteSupport.assignmentOf (valuesFromFormulaFin2OfBoolFormula φ values) x =
      assignmentFin2ToBool (FiniteSupport.assignmentOf values) x := by
  have hxfd : x ∈ FiniteSupport.formulaVars (formulaFin2OfBoolFormula φ) := by
    have hvars := formulaVars_formulaFin2OfBoolFormula φ
    simpa [hvars] using hx
  simp
    [ assignmentFin2ToBool
    , FiniteSupport.assignmentOf
    , CSP.FiniteSupport.assignmentOf
    , valuesFromFormulaFin2OfBoolFormula
    , hx ]

private theorem valuesToFormulaFin2OfBoolFormula_mem_solutionSet {Γ : BoolLanguage}
    (φ : CSP.Formula Γ)
    {values : {x : Nat // x ∈ CSP.FiniteSupport.formulaVars φ} → Bool}
    (hvalues : values ∈ CSP.Formula.solutionSet φ) :
    valuesToFormulaFin2OfBoolFormula φ values ∈
      Formula.solutionSet (formulaFin2OfBoolFormula φ) := by
  have hSource :
      CSP.Formula.Satisfies φ (CSP.FiniteSupport.assignmentOf values) :=
    (CSP.Formula.mem_solutionSet φ values).1 hvalues
  have hAgree :
      ∀ x ∈ CSP.FiniteSupport.formulaVars φ,
        assignmentFin2ToBool
            (FiniteSupport.assignmentOf (valuesToFormulaFin2OfBoolFormula φ values)) x =
          CSP.FiniteSupport.assignmentOf values x := by
    intro x hx
    exact assignmentOf_valuesToFormulaFin2OfBoolFormula_eq_of_mem φ values hx
  have hSource' :
      CSP.Formula.Satisfies φ
        (assignmentFin2ToBool
          (FiniteSupport.assignmentOf (valuesToFormulaFin2OfBoolFormula φ values))) :=
    (CSP.FiniteSupport.formula_satisfies_iff_of_agree (φ := φ)
      (a := assignmentFin2ToBool
        (FiniteSupport.assignmentOf (valuesToFormulaFin2OfBoolFormula φ values)))
      (b := CSP.FiniteSupport.assignmentOf values) hAgree).2 hSource
  exact (Formula.mem_solutionSet (formulaFin2OfBoolFormula φ)
    (valuesToFormulaFin2OfBoolFormula φ values)).2
      ((formulaFin2OfBoolFormula_satisfies_iff φ
        (FiniteSupport.assignmentOf (valuesToFormulaFin2OfBoolFormula φ values))).2 hSource')

private theorem valuesFromFormulaFin2OfBoolFormula_mem_solutionSet {Γ : BoolLanguage}
    (φ : CSP.Formula Γ)
    {values : {x : Nat // x ∈ FiniteSupport.formulaVars (formulaFin2OfBoolFormula φ)} → Fin 2}
    (hvalues : values ∈ Formula.solutionSet (formulaFin2OfBoolFormula φ)) :
    valuesFromFormulaFin2OfBoolFormula φ values ∈ CSP.Formula.solutionSet φ := by
  have hTarget :
      Formula.Satisfies (formulaFin2OfBoolFormula φ) (FiniteSupport.assignmentOf values) :=
    (Formula.mem_solutionSet (formulaFin2OfBoolFormula φ) values).1 hvalues
  have hSource :
      CSP.Formula.Satisfies φ
        (assignmentFin2ToBool (FiniteSupport.assignmentOf values)) :=
    (formulaFin2OfBoolFormula_satisfies_iff φ (FiniteSupport.assignmentOf values)).1 hTarget
  have hAgree :
      ∀ x ∈ CSP.FiniteSupport.formulaVars φ,
        CSP.FiniteSupport.assignmentOf
            (valuesFromFormulaFin2OfBoolFormula φ values) x =
          assignmentFin2ToBool (FiniteSupport.assignmentOf values) x := by
    intro x hx
    exact assignmentOf_valuesFromFormulaFin2OfBoolFormula_eq_of_mem φ values hx
  have hSource' :
      CSP.Formula.Satisfies φ
        (CSP.FiniteSupport.assignmentOf (valuesFromFormulaFin2OfBoolFormula φ values)) :=
    (CSP.FiniteSupport.formula_satisfies_iff_of_agree (φ := φ)
      (a := CSP.FiniteSupport.assignmentOf (valuesFromFormulaFin2OfBoolFormula φ values))
      (b := assignmentFin2ToBool (FiniteSupport.assignmentOf values)) hAgree).2 hSource
  exact (CSP.Formula.mem_solutionSet φ
    (valuesFromFormulaFin2OfBoolFormula φ values)).2 hSource'

/-- Boolean formulas and their finite-domain `Fin 2` images have equivalent solution valuations. -/
noncomputable def solutionEquiv_formulaFin2OfBoolFormula {Γ : BoolLanguage}
    (φ : CSP.Formula Γ) :
    CSP.Formula.SolutionValuation φ ≃
      Formula.SolutionValuation (formulaFin2OfBoolFormula φ) where
  toFun sol :=
    ⟨ valuesToFormulaFin2OfBoolFormula φ sol.1
    , valuesToFormulaFin2OfBoolFormula_mem_solutionSet φ sol.2 ⟩
  invFun sol :=
    ⟨ valuesFromFormulaFin2OfBoolFormula φ sol.1
    , valuesFromFormulaFin2OfBoolFormula_mem_solutionSet φ sol.2 ⟩
  left_inv sol := by
    apply Subtype.ext
    funext x
    simp [valuesFromFormulaFin2OfBoolFormula, valuesToFormulaFin2OfBoolFormula]
  right_inv sol := by
    apply Subtype.ext
    funext x
    simp [valuesFromFormulaFin2OfBoolFormula, valuesToFormulaFin2OfBoolFormula]

/-- Transporting a Boolean formula to the finite-domain `Fin 2` surface preserves solution count. -/
theorem solutionCount_formulaFin2OfBoolFormula {Γ : BoolLanguage} (φ : CSP.Formula Γ) :
    Formula.solutionCount (formulaFin2OfBoolFormula φ) = CSP.Formula.solutionCount φ := by
  classical
  unfold Formula.solutionCount CSP.Formula.solutionCount
  let e := solutionEquiv_formulaFin2OfBoolFormula φ
  have hCard :
      (CSP.Formula.solutionSet φ).card =
        (Formula.solutionSet (formulaFin2OfBoolFormula φ)).card := by
    refine Finset.card_bij
      (fun values hvalues => (e ⟨values, hvalues⟩).1)
      (fun values hvalues => (e ⟨values, hvalues⟩).2)
      ?inj
      ?surj
    · intro a ha b hb h
      have hSubtype : e ⟨a, ha⟩ = e ⟨b, hb⟩ := by
        exact Subtype.ext h
      exact congrArg Subtype.val (e.injective hSubtype)
    · intro b hb
      refine ⟨(e.symm ⟨b, hb⟩).1, (e.symm ⟨b, hb⟩).2, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
  exact hCard.symm

end BoolBridge
end FiniteDomain
end CSP
end ComplexityReduction
