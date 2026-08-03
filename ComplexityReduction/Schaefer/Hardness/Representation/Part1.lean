/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Hardness.NAE3SATNPC
import ComplexityReduction.CSP.Hardness.OneInThreeNPC
import ComplexityReduction.CSP.Hardness.ThreeSATLikeNPC
import ComplexityReduction.CSP.InNP
import ComplexityReduction.Schaefer.DichotomyStatement
import ComplexityReduction.Schaefer.Tractable.FiniteSearch

/-!
Local hard-side representation and certificate route for Schaefer `SAT(S)`.

This file deliberately separates two layers:

* representation syntax/semantics for future local Schaefer classification work;
* a usable hard-side certificate API that packages an already proved hard base
  reduction into conditional NP-completeness through the explicit local 3SAT
  completeness boundary.

It does not prove `HardCaseAssumptions Γ -> HardRelationCertificate Γ`.
-/

namespace ComplexityReduction
namespace Schaefer
namespace Hardness

/-- Extend a free Boolean tuple with a total auxiliary assignment. -/
def extendTupleAssignment {k : Nat} (t : CSP.BoolTuple k) (aux : SAT.Assignment) :
    SAT.Assignment :=
  fun x => if h : x < k then t ⟨x, h⟩ else aux x

@[simp]
theorem extendTupleAssignment_of_lt {k : Nat} (t : CSP.BoolTuple k)
    (aux : SAT.Assignment) {x : Nat} (hx : x < k) :
    extendTupleAssignment t aux x = t ⟨x, hx⟩ := by
  simp [extendTupleAssignment, hx]

/--
A primitive-positive style representation block over a target language `Γ`.

The free variables are expected at indices `0, ..., arity - 1`; any other
variables are auxiliary variables supplied by the existential witness in
`RepresentsRelation`.
-/
structure RelationFormula (Γ : CSP.BoolLanguage) (arity : Nat) where
  constraints : SATFormula Γ
  notes : String := ""

/-- Semantics of a local relation representation block. -/
def RepresentsRelation (Γ : CSP.BoolLanguage) (R : CSP.BoolRel)
    (rep : RelationFormula Γ R.arity) : Prop :=
  ∀ t : CSP.BoolTuple R.arity,
    R.Holds t ↔ ∃ aux : SAT.Assignment,
      CSP.Formula.Satisfies rep.constraints (extendTupleAssignment t aux)

namespace RelationFormula

/-- Largest variable mentioned in a representation block. -/
def maxVar {Γ : CSP.BoolLanguage} {arity : Nat} (rep : RelationFormula Γ arity) : Nat :=
  CSP.Formula.maxVar rep.constraints

end RelationFormula

/-- A representation for every relation symbol of a source language. -/
structure LanguageRepresentation (Δ Γ : CSP.BoolLanguage) where
  block : ∀ s : Δ.Symbol, RelationFormula Γ (Δ.relationOf s).arity
  represents : ∀ s : Δ.Symbol, RepresentsRelation Γ (Δ.relationOf s) (block s)
  notes : String := ""

namespace LanguageRepresentation

/-- A strict upper bound for the variables mentioned in one representation block. -/
noncomputable def blockVarBound {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (s : Δ.Symbol) : Nat :=
  (FiniteSearch.formulaVars (rep.block s).constraints).sup id + 1

/-- Largest variable used by any representation block in a fixed finite source language. -/
noncomputable def maxBlockVar {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) : Nat :=
  (Finset.univ : Finset Δ.Symbol).sup fun s =>
    (FiniteSearch.formulaVars (rep.block s).constraints).sup id

/-- A conservative per-source-constraint auxiliary width for block allocation. -/
noncomputable def auxBlockWidth {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) : Nat :=
  (Finset.univ : Finset Δ.Symbol).sup fun s => rep.blockVarBound s

/-- Maximum number of target constraints used by any representation block. -/
noncomputable def maxBlockConstraints {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) : Nat :=
  (Finset.univ : Finset Δ.Symbol).sup fun s => (rep.block s).constraints.length

theorem var_lt_blockVarBound {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (s : Δ.Symbol) {x : Nat}
    (hx : x ∈ FiniteSearch.formulaVars (rep.block s).constraints) :
    x < rep.blockVarBound s := by
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)

theorem blockVarBound_le_auxBlockWidth {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (s : Δ.Symbol) :
    rep.blockVarBound s ≤ rep.auxBlockWidth := by
  classical
  exact Finset.le_sup
    (s := (Finset.univ : Finset Δ.Symbol))
    (f := fun s => rep.blockVarBound s)
    (b := s)
    (Finset.mem_univ s)

theorem var_lt_auxBlockWidth {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (s : Δ.Symbol) {x : Nat}
    (hx : x ∈ FiniteSearch.formulaVars (rep.block s).constraints) :
    x < rep.auxBlockWidth :=
  lt_of_lt_of_le (rep.var_lt_blockVarBound s hx) (rep.blockVarBound_le_auxBlockWidth s)

theorem block_constraints_length_le_maxBlockConstraints {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (s : Δ.Symbol) :
    (rep.block s).constraints.length ≤ rep.maxBlockConstraints := by
  classical
  exact Finset.le_sup
    (s := (Finset.univ : Finset Δ.Symbol))
    (f := fun s => (rep.block s).constraints.length)
    (b := s)
    (Finset.mem_univ s)

end LanguageRepresentation

/-- A strict upper bound for variables mentioned by a source formula. -/
noncomputable def formulaVarBound {Γ : CSP.BoolLanguage} (φ : SATFormula Γ) : Nat :=
  (FiniteSearch.formulaVars φ).sup id + 1

theorem var_lt_formulaVarBound {Γ : CSP.BoolLanguage} {φ : SATFormula Γ} {x : Nat}
    (hx : x ∈ FiniteSearch.formulaVars φ) :
    x < formulaVarBound φ :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)

theorem constraint_var_lt_formulaVarBound_of_mem {Γ : CSP.BoolLanguage}
    {φ : SATFormula Γ} {c : CSP.Constraint Γ} (hc : c ∈ φ)
    (i : Fin (Γ.relationOf c.symbol).arity) :
    c.vars i < formulaVarBound φ :=
  var_lt_formulaVarBound (FiniteSearch.var_mem_formulaVars_of_constraint_mem hc i)

theorem constraint_var_lt_encodeConstraint_length {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint Γ) (i : Fin (Γ.relationOf c.symbol).arity) :
    c.vars i < (CSP.Encoding.encodeConstraint c).length := by
  rw [CSP.Encoding.encodeConstraint_length]
  have hmem :
      c.vars i + 2 ∈ (List.ofFn c.vars).map (fun n => n + 2) := by
    exact List.mem_map.mpr ⟨c.vars i, List.mem_ofFn.2 ⟨i, rfl⟩, rfl⟩
  have hle : c.vars i + 2 ≤ ((List.ofFn c.vars).map fun n => n + 2).sum :=
    List.le_sum_of_mem hmem
  omega

theorem var_lt_encodeFormula_length_of_mem {Γ : CSP.BoolLanguage}
    {φ : SATFormula Γ} {x : Nat} (hx : x ∈ FiniteSearch.formulaVars φ) :
    x < (CSP.Encoding.encodeFormula φ).length := by
  induction φ with
  | nil =>
      simp [FiniteSearch.formulaVars] at hx
  | cons c φ ih =>
      simp [FiniteSearch.formulaVars] at hx
      rw [CSP.Encoding.encodeFormula_length_cons]
      rcases hx with hx | hx
      · rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
        have hlt := constraint_var_lt_encodeConstraint_length c i
        omega
      · have hlt := ih hx
        omega

theorem formulaVarBound_le_encodeFormula_length_add_one {Γ : CSP.BoolLanguage}
    (φ : SATFormula Γ) :
    formulaVarBound φ ≤ (CSP.Encoding.encodeFormula φ).length + 1 := by
  unfold formulaVarBound
  apply Nat.succ_le_succ
  refine Finset.sup_le ?_
  intro x hx
  exact Nat.le_of_lt (var_lt_encodeFormula_length_of_mem hx)

theorem formula_length_le_encodeFormula_length {Γ : CSP.BoolLanguage}
    (φ : SATFormula Γ) :
    φ.length ≤ (CSP.Encoding.encodeFormula φ).length := by
  induction φ with
  | nil =>
      simp [CSP.Encoding.encodeFormula]
  | cons c φ ih =>
      rw [CSP.Encoding.encodeFormula_length_cons]
      have hc : 1 ≤ (CSP.Encoding.encodeConstraint c).length := by
        rw [CSP.Encoding.encodeConstraint_length]
        omega
      simp
      omega

/-- Uniform encoded-size bound for one target-language constraint when every variable is below `B`. -/
theorem encodeConstraint_length_le_of_vars_lt {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint Γ) (B : Nat)
    (hVars : ∀ i : Fin (Γ.relationOf c.symbol).arity, c.vars i < B) :
    (CSP.Encoding.encodeConstraint c).length ≤ 2 + Γ.maxArity * (B + 2) := by
  rw [CSP.Encoding.encodeConstraint_length]
  have hsum :
      ((List.ofFn c.vars).map fun n => n + 2).sum ≤
        (List.ofFn c.vars).length * (B + 2) := by
    exact CSP.ListBounds.sum_map_le_length_mul
      (List.ofFn c.vars)
      (fun n => n + 2)
      (B + 2)
      (by
        intro n hn
        rcases List.mem_ofFn.mp hn with ⟨i, rfl⟩
        have hi : c.vars i < B := hVars i
        exact Nat.add_le_add_right (Nat.le_of_lt hi) 2)
  have hlen : (List.ofFn c.vars).length ≤ Γ.maxArity := by
    rw [List.length_ofFn]
    exact Γ.arity_le_maxArity c.symbol
  have hmul :
      (List.ofFn c.vars).length * (B + 2) ≤ Γ.maxArity * (B + 2) :=
    Nat.mul_le_mul_right (B + 2) hlen
  omega

/-- Uniform encoded-size bound for a formula when all variables are below `B`. -/
theorem encodeFormula_length_le_of_vars_lt {Γ : CSP.BoolLanguage}
    (φ : SATFormula Γ) (B : Nat)
    (hVars : ∀ c ∈ φ, ∀ i : Fin (Γ.relationOf c.symbol).arity, c.vars i < B) :
    (CSP.Encoding.encodeFormula φ).length ≤
      φ.length * (2 + Γ.maxArity * (B + 2)) := by
  induction φ with
  | nil =>
      simp [CSP.Encoding.encodeFormula]
  | cons c φ ih =>
      rw [CSP.Encoding.encodeFormula_length_cons]
      let K := 2 + Γ.maxArity * (B + 2)
      have hHead := encodeConstraint_length_le_of_vars_lt c B (fun i => hVars c (by simp) i)
      have hTail :
          (CSP.Encoding.encodeFormula φ).length ≤
            φ.length * (2 + Γ.maxArity * (B + 2)) := by
        exact ih (by
          intro d hd i
          exact hVars d (by simp [hd]) i)
      calc
        (CSP.Encoding.encodeConstraint c).length + (CSP.Encoding.encodeFormula φ).length
            ≤ K + φ.length * K := Nat.add_le_add hHead hTail
        _ = (φ.length + 1) * K := by
          rw [Nat.succ_mul]
          omega

/-- Rename all variables in one target-language constraint. -/
def constraintMapVars {Γ : CSP.BoolLanguage} (f : Nat → Nat)
    (c : CSP.Constraint Γ) : CSP.Constraint Γ where
  symbol := c.symbol
  vars := fun i => f (c.vars i)

@[simp]
theorem constraintMapVars_satisfies_iff {Γ : CSP.BoolLanguage} (f : Nat → Nat)
    (c : CSP.Constraint Γ) (a : SAT.Assignment) :
    CSP.Constraint.Satisfies (constraintMapVars f c) a ↔
      CSP.Constraint.Satisfies c (fun x => a (f x)) :=
  Iff.rfl

/-- Rename all variables in a target-language formula. -/
def formulaMapVars {Γ : CSP.BoolLanguage} (f : Nat → Nat)
    (φ : SATFormula Γ) : SATFormula Γ :=
  φ.map (constraintMapVars f)

@[simp]
theorem formulaMapVars_nil {Γ : CSP.BoolLanguage} (f : Nat → Nat) :
    formulaMapVars f ([] : SATFormula Γ) = [] :=
  rfl

@[simp]
theorem formulaMapVars_cons {Γ : CSP.BoolLanguage} (f : Nat → Nat)
    (c : CSP.Constraint Γ) (φ : SATFormula Γ) :
    formulaMapVars f (c :: φ) = constraintMapVars f c :: formulaMapVars f φ :=
  rfl

@[simp]
theorem formulaMapVars_satisfies_iff {Γ : CSP.BoolLanguage} (f : Nat → Nat)
    (φ : SATFormula Γ) (a : SAT.Assignment) :
    CSP.Formula.Satisfies (formulaMapVars f φ) a ↔
      CSP.Formula.Satisfies φ (fun x => a (f x)) := by
  induction φ with
  | nil =>
      simp
  | cons c φ ih =>
      simp [ih]

@[simp]
theorem finiteSearch_formulaVars_append {Γ : CSP.BoolLanguage}
    (φ ψ : SATFormula Γ) :
    FiniteSearch.formulaVars (φ ++ ψ) =
      FiniteSearch.formulaVars φ ∪ FiniteSearch.formulaVars ψ := by
  induction φ with
  | nil =>
      simp [FiniteSearch.formulaVars]
  | cons c φ ih =>
      simp [FiniteSearch.formulaVars, ih, Finset.union_assoc]

theorem mem_formulaVars_formulaMapVars {Γ : CSP.BoolLanguage} {f : Nat → Nat}
    {φ : SATFormula Γ} {y : Nat}
    (hy : y ∈ FiniteSearch.formulaVars (formulaMapVars f φ)) :
    ∃ x : Nat, x ∈ FiniteSearch.formulaVars φ ∧ y = f x := by
  induction φ with
  | nil =>
      simp [formulaMapVars, FiniteSearch.formulaVars] at hy
  | cons c φ ih =>
      rw [formulaMapVars_cons] at hy
      rw [FiniteSearch.formulaVars_cons] at hy
      rw [FiniteSearch.formulaVars_cons]
      rcases Finset.mem_union.mp hy with hHead | hTail
      · unfold FiniteSearch.constraintVars CSP.FiniteSupport.constraintVars at hHead
        rcases Finset.mem_image.mp hHead with ⟨i, _hi, hiy⟩
        refine ⟨c.vars i, ?_, ?_⟩
        · exact Finset.mem_union.mpr (Or.inl (FiniteSearch.mem_constraintVars c i))
        · simpa [constraintMapVars] using hiy.symm
      · rcases ih hTail with ⟨x, hx, hxy⟩
        exact ⟨x, Finset.mem_union.mpr (Or.inr hx), hxy⟩

/--
Variable map for instantiating a representation block against one source
constraint.  Free variables `0, ..., arity - 1` are substituted by the source
constraint variables; all other variables are placed in the auxiliary block
starting at `auxBase`.
-/
def representationBlockVarMap {Δ : CSP.BoolLanguage} (c : CSP.Constraint Δ)
    (auxBase x : Nat) : Nat :=
  if h : x < (Δ.relationOf c.symbol).arity then c.vars ⟨x, h⟩ else auxBase + x

/-- Expand one source constraint through a representation block using a chosen auxiliary base. -/
def constraintViaRepresentationAt {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (c : CSP.Constraint Δ) (auxBase : Nat) :
    SATFormula Γ :=
  formulaMapVars
    (representationBlockVarMap c auxBase)
    (rep.block c.symbol).constraints

theorem mem_formulaVars_constraintViaRepresentationAt
    {Δ Γ : CSP.BoolLanguage} (rep : LanguageRepresentation Δ Γ)
    (c : CSP.Constraint Δ) (auxBase : Nat) {y : Nat}
    (hy : y ∈ FiniteSearch.formulaVars (constraintViaRepresentationAt rep c auxBase)) :
    (∃ i : Fin (Δ.relationOf c.symbol).arity, y = c.vars i) ∨
      ∃ x : Nat,
        x ∈ FiniteSearch.formulaVars (rep.block c.symbol).constraints ∧
          ¬ x < (Δ.relationOf c.symbol).arity ∧ y = auxBase + x := by
  rcases mem_formulaVars_formulaMapVars hy with ⟨x, hx, rfl⟩
  by_cases hFree : x < (Δ.relationOf c.symbol).arity
  · exact Or.inl ⟨⟨x, hFree⟩, by simp [representationBlockVarMap, hFree]⟩
  · exact Or.inr ⟨x, hx, hFree, by simp [representationBlockVarMap, hFree]⟩

/-- Merge a source assignment, one representation-block auxiliary assignment, and a tail assignment. -/
def mergeBlockAssignment (auxBase blockWidth : Nat)
    (source aux tail : SAT.Assignment) : SAT.Assignment :=
  fun x =>
    if x < auxBase then source x
    else if x < auxBase + blockWidth then aux (x - auxBase)
    else tail x

@[simp]
theorem mergeBlockAssignment_source {auxBase blockWidth : Nat}
    {source aux tail : SAT.Assignment} {x : Nat} (hx : x < auxBase) :
    mergeBlockAssignment auxBase blockWidth source aux tail x = source x := by
  simp [mergeBlockAssignment, hx]

theorem mergeBlockAssignment_aux_add {auxBase blockWidth : Nat}
    {source aux tail : SAT.Assignment} {x : Nat} (hx : x < blockWidth) :
    mergeBlockAssignment auxBase blockWidth source aux tail (auxBase + x) = aux x := by
  have hNotSource : ¬ auxBase + x < auxBase := by omega
  have hInBlock : auxBase + x < auxBase + blockWidth := by omega
  simp [mergeBlockAssignment, hNotSource, hInBlock]

theorem mergeBlockAssignment_tail {auxBase blockWidth : Nat}
    {source aux tail : SAT.Assignment} {x : Nat} (hx : auxBase + blockWidth ≤ x) :
    mergeBlockAssignment auxBase blockWidth source aux tail x = tail x := by
  have hNotSource : ¬ x < auxBase := by omega
  have hNotBlock : ¬ x < auxBase + blockWidth := by omega
  simp [mergeBlockAssignment, hNotSource, hNotBlock]

/-- Recursive formula expansion with one fresh auxiliary block per source constraint. -/
noncomputable def formulaViaRepresentationFrom {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (auxBase blockWidth : Nat) :
    SATFormula Δ → SATFormula Γ
  | [] => []
  | c :: φ =>
      constraintViaRepresentationAt rep c auxBase ++
        formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ

theorem formulaViaRepresentationFrom_vars_source_or_aux
    {Δ Γ : CSP.BoolLanguage} (rep : LanguageRepresentation Δ Γ)
    {φ : SATFormula Δ} {sourceBound auxBase blockWidth y : Nat}
    (hSource : ∀ c ∈ φ, ∀ i : Fin (Δ.relationOf c.symbol).arity, c.vars i < sourceBound)
    (hBase : sourceBound ≤ auxBase)
    (hy :
      y ∈ FiniteSearch.formulaVars
        (formulaViaRepresentationFrom rep auxBase blockWidth φ)) :
    y < sourceBound ∨ auxBase ≤ y := by
  induction φ generalizing auxBase with
  | nil =>
      simp [formulaViaRepresentationFrom, FiniteSearch.formulaVars] at hy
  | cons c φ ih =>
      rw [formulaViaRepresentationFrom] at hy
      rw [finiteSearch_formulaVars_append] at hy
      rcases Finset.mem_union.mp hy with hHead | hTail
      · rcases mem_formulaVars_constraintViaRepresentationAt rep c auxBase hHead with hFree | hAux
        · rcases hFree with ⟨i, rfl⟩
          exact Or.inl (hSource c (by simp) i)
        · rcases hAux with ⟨x, _hx, _hNotFree, rfl⟩
          exact Or.inr (Nat.le_add_right auxBase x)
      · have hSourceTail :
            ∀ d ∈ φ, ∀ i : Fin (Δ.relationOf d.symbol).arity, d.vars i < sourceBound := by
          intro d hd i
          exact hSource d (by simp [hd]) i
        have hBaseTail : sourceBound ≤ auxBase + blockWidth := by omega
        have hTailClass :=
          ih hSourceTail hBaseTail hTail
        rcases hTailClass with hSrc | hAux
        · exact Or.inl hSrc
        · exact Or.inr (le_trans (Nat.le_add_right auxBase blockWidth) hAux)

/--
Syntax map for expanding one source constraint through a language
representation, using a block just above the variables of that constraint.

Formula-level certificates should use `formulaViaRepresentation`, which allocates
one block per source constraint.  This single-constraint map is kept as an
tool-facing primitive for generated gadget obligations.
-/
noncomputable def constraintViaRepresentation {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (c : CSP.Constraint Δ) : SATFormula Γ :=
  constraintViaRepresentationAt rep c (CSP.Constraint.maxVar c + 1)

/-- Formula-level expansion induced by a language representation. -/
noncomputable def formulaViaRepresentation {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (φ : SATFormula Δ) : SATFormula Γ :=
  formulaViaRepresentationFrom rep
    (formulaVarBound φ)
    rep.auxBlockWidth
    φ

@[simp]
theorem formulaMapVars_length {Γ : CSP.BoolLanguage} (f : Nat → Nat)
    (φ : SATFormula Γ) :
    (formulaMapVars f φ).length = φ.length := by
  simp [formulaMapVars]

@[simp]
theorem constraintViaRepresentationAt_length {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (c : CSP.Constraint Δ) (auxBase : Nat) :
    (constraintViaRepresentationAt rep c auxBase).length =
      (rep.block c.symbol).constraints.length := by
  simp [constraintViaRepresentationAt]

theorem constraintViaRepresentationAt_vars_lt_bound {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (c : CSP.Constraint Δ)
    (sourceBound auxBase blockWidth : Nat)
    (hSource : ∀ i : Fin (Δ.relationOf c.symbol).arity, c.vars i < sourceBound)
    (hBase : sourceBound ≤ auxBase)
    (hWidth :
      ∀ x ∈ FiniteSearch.formulaVars (rep.block c.symbol).constraints, x < blockWidth)
    {y : Nat}
    (hy : y ∈ FiniteSearch.formulaVars (constraintViaRepresentationAt rep c auxBase)) :
    y < auxBase + blockWidth := by
  rcases mem_formulaVars_constraintViaRepresentationAt rep c auxBase hy with hFree | hAux
  · rcases hFree with ⟨i, rfl⟩
    exact lt_of_lt_of_le (hSource i) (Nat.le_add_right_of_le hBase)
  · rcases hAux with ⟨x, hx, _hNotFree, rfl⟩
    have hxWidth : x < blockWidth := hWidth x hx
    omega

theorem formulaViaRepresentationFrom_length_le_maxBlockConstraints
    {Δ Γ : CSP.BoolLanguage} (rep : LanguageRepresentation Δ Γ)
    (auxBase blockWidth : Nat) (φ : SATFormula Δ) :
    (formulaViaRepresentationFrom rep auxBase blockWidth φ).length ≤
      φ.length * rep.maxBlockConstraints := by
  induction φ generalizing auxBase with
  | nil =>
      simp [formulaViaRepresentationFrom]
  | cons c φ ih =>
      rw [formulaViaRepresentationFrom, List.length_append, constraintViaRepresentationAt_length]
      let M := rep.maxBlockConstraints
      have hHead := rep.block_constraints_length_le_maxBlockConstraints c.symbol
      have hTail :
          (formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ).length ≤
            φ.length * M := by
        simpa [M] using ih (auxBase := auxBase + blockWidth)
      calc
        (rep.block c.symbol).constraints.length +
            (formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ).length
            ≤ M + φ.length * M := Nat.add_le_add hHead hTail
        _ = (φ.length + 1) * M := by
          rw [Nat.succ_mul]
          omega

theorem formulaViaRepresentationFrom_vars_lt_bound
    {Δ Γ : CSP.BoolLanguage} (rep : LanguageRepresentation Δ Γ)
    {φ : SATFormula Δ} {sourceBound auxBase blockWidth y : Nat}
    (hWidth :
      ∀ s : Δ.Symbol, ∀ x ∈ FiniteSearch.formulaVars (rep.block s).constraints,
        x < blockWidth)
    (hSource : ∀ c ∈ φ, ∀ i : Fin (Δ.relationOf c.symbol).arity, c.vars i < sourceBound)
    (hBase : sourceBound ≤ auxBase)
    (hy :
      y ∈ FiniteSearch.formulaVars
        (formulaViaRepresentationFrom rep auxBase blockWidth φ)) :
    y < auxBase + φ.length * blockWidth := by
  induction φ generalizing auxBase with
  | nil =>
      simp [formulaViaRepresentationFrom, FiniteSearch.formulaVars] at hy
  | cons c φ ih =>
      rw [formulaViaRepresentationFrom] at hy
      rw [finiteSearch_formulaVars_append] at hy
      rcases Finset.mem_union.mp hy with hHead | hTail
      · have hHeadBound :
            y < auxBase + blockWidth :=
          constraintViaRepresentationAt_vars_lt_bound rep c
            sourceBound auxBase blockWidth
            (fun i => hSource c (by simp) i)
            hBase
            (hWidth c.symbol)
            hHead
        have hBlock :
            blockWidth ≤ (φ.length + 1) * blockWidth := by
          have hOne : 1 ≤ φ.length + 1 := by omega
          simpa using Nat.mul_le_mul_right blockWidth hOne
        exact lt_of_lt_of_le hHeadBound (Nat.add_le_add_left hBlock auxBase)
      · have hSourceTail :
            ∀ d ∈ φ, ∀ i : Fin (Δ.relationOf d.symbol).arity,
              d.vars i < sourceBound := by
          intro d hd i
          exact hSource d (by simp [hd]) i
        have hBaseTail : sourceBound ≤ auxBase + blockWidth := by
          exact hBase.trans (Nat.le_add_right auxBase blockWidth)
        have hTailBound :
            y < (auxBase + blockWidth) + φ.length * blockWidth :=
          ih (auxBase := auxBase + blockWidth) hSourceTail hBaseTail hTail
        have hTailBound' :
            y < auxBase + (φ.length + 1) * blockWidth := by
          calc
            y < (auxBase + blockWidth) + φ.length * blockWidth := hTailBound
            _ = auxBase + (φ.length + 1) * blockWidth := by
              rw [Nat.succ_mul]
              omega
        simpa using hTailBound'

theorem formulaViaRepresentation_vars_lt_bound {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (φ : SATFormula Δ) {y : Nat}
    (hy : y ∈ FiniteSearch.formulaVars (formulaViaRepresentation rep φ)) :
    y < formulaVarBound φ + φ.length * rep.auxBlockWidth := by
  have hWidth :
      ∀ s : Δ.Symbol, ∀ x ∈ FiniteSearch.formulaVars (rep.block s).constraints,
        x < rep.auxBlockWidth := by
    intro s x hx
    exact rep.var_lt_auxBlockWidth s hx
  have hSource :
      ∀ c ∈ φ, ∀ i : Fin (Δ.relationOf c.symbol).arity,
        c.vars i < formulaVarBound φ := by
    intro c hc i
    exact constraint_var_lt_formulaVarBound_of_mem hc i
  exact formulaViaRepresentationFrom_vars_lt_bound
    (rep := rep)
    (sourceBound := formulaVarBound φ)
    (auxBase := formulaVarBound φ)
    (blockWidth := rep.auxBlockWidth)
    hWidth hSource (le_refl _) hy

theorem formulaViaRepresentationFrom_encodedLength_le
    {Δ Γ : CSP.BoolLanguage} (rep : LanguageRepresentation Δ Γ)
    {φ : SATFormula Δ} {sourceBound auxBase blockWidth : Nat}
    (hWidth :
      ∀ s : Δ.Symbol, ∀ x ∈ FiniteSearch.formulaVars (rep.block s).constraints,
        x < blockWidth)
    (hSource : ∀ c ∈ φ, ∀ i : Fin (Δ.relationOf c.symbol).arity, c.vars i < sourceBound)
    (hBase : sourceBound ≤ auxBase) :
    (CSP.Encoding.encodeFormula
      (formulaViaRepresentationFrom rep auxBase blockWidth φ)).length ≤
      (φ.length * rep.maxBlockConstraints) *
        (2 + Γ.maxArity * ((auxBase + φ.length * blockWidth) + 2)) := by
  let ψ := formulaViaRepresentationFrom rep auxBase blockWidth φ
  let B := auxBase + φ.length * blockWidth
  let K := 2 + Γ.maxArity * (B + 2)
  have hLen : ψ.length ≤ φ.length * rep.maxBlockConstraints := by
    simpa [ψ] using formulaViaRepresentationFrom_length_le_maxBlockConstraints
      rep auxBase blockWidth φ
  have hVars : ∀ c ∈ ψ, ∀ i : Fin (Γ.relationOf c.symbol).arity, c.vars i < B := by
    intro c hc i
    exact formulaViaRepresentationFrom_vars_lt_bound
      (rep := rep)
      (sourceBound := sourceBound)
      (auxBase := auxBase)
      (blockWidth := blockWidth)
      hWidth hSource hBase
      (FiniteSearch.var_mem_formulaVars_of_constraint_mem hc i)
  have hEnc : (CSP.Encoding.encodeFormula ψ).length ≤ ψ.length * K := by
    simpa [K, B] using encodeFormula_length_le_of_vars_lt ψ B hVars
  calc
    (CSP.Encoding.encodeFormula ψ).length ≤ ψ.length * K := hEnc
    _ ≤ (φ.length * rep.maxBlockConstraints) * K := Nat.mul_le_mul_right K hLen

theorem formulaViaRepresentation_encodedLength_le {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (φ : SATFormula Δ) :
    (CSP.Encoding.encodeFormula (formulaViaRepresentation rep φ)).length ≤
      (φ.length * rep.maxBlockConstraints) *
        (2 + Γ.maxArity *
          ((formulaVarBound φ + φ.length * rep.auxBlockWidth) + 2)) := by
  have hWidth :
      ∀ s : Δ.Symbol, ∀ x ∈ FiniteSearch.formulaVars (rep.block s).constraints,
        x < rep.auxBlockWidth := by
    intro s x hx
    exact rep.var_lt_auxBlockWidth s hx
  have hSource :
      ∀ c ∈ φ, ∀ i : Fin (Δ.relationOf c.symbol).arity,
        c.vars i < formulaVarBound φ := by
    intro c hc i
    exact constraint_var_lt_formulaVarBound_of_mem hc i
  simpa [formulaViaRepresentation] using
    formulaViaRepresentationFrom_encodedLength_le
      (rep := rep)
      (sourceBound := formulaVarBound φ)
      (auxBase := formulaVarBound φ)
      (blockWidth := rep.auxBlockWidth)
      hWidth hSource (le_refl _)

theorem formulaViaRepresentation_polynomialSizeBound {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) :
    PolynomialSizeBound
      (fun φ : SATFormula Δ => (satSDecisionProblem Δ).Instance.inputSize φ)
      (fun ψ : SATFormula Γ => (satSDecisionProblem Γ).Instance.inputSize ψ)
      (formulaViaRepresentation rep) :=
  PolynomialSizeBound.intro_with 2
    (rep.maxBlockConstraints * (2 + Γ.maxArity * (rep.auxBlockWidth + 3)) * 4)
    (rep.maxBlockConstraints * (2 + Γ.maxArity * (rep.auxBlockWidth + 3))) (by
      intro φ
      let n := (satSDecisionProblem Δ).Instance.inputSize φ
      let M := rep.maxBlockConstraints
      let W := rep.auxBlockWidth
      let A := 2 + Γ.maxArity * (W + 3)
      have hEncoded := formulaViaRepresentation_encodedLength_le rep φ
      have hLen : φ.length ≤ n := by
        simpa [n, EncodedType.inputSize, satSDecisionProblem, CSP.boolCSPDecisionProblem,
          CSP.boolCSPSatLike, CSP.formulaEncodedType] using
          formula_length_le_encodeFormula_length φ
      have hVar : formulaVarBound φ ≤ n + 1 := by
        simpa [n, EncodedType.inputSize, satSDecisionProblem, CSP.boolCSPDecisionProblem,
          CSP.boolCSPSatLike, CSP.formulaEncodedType] using
          formulaVarBound_le_encodeFormula_length_add_one φ
      have hPhiW : φ.length * W ≤ (n + 1) * W := by
        have hToN : φ.length * W ≤ n * W := Nat.mul_le_mul_right W hLen
        have hNToSucc : n * W ≤ (n + 1) * W :=
          Nat.mul_le_mul_right W (Nat.le_succ n)
        exact hToN.trans hNToSucc
      have hVarBlock :
          (formulaVarBound φ + φ.length * W) + 2 ≤ (W + 3) * (n + 1) := by
        calc
          (formulaVarBound φ + φ.length * W) + 2
              ≤ (n + 1) + (n + 1) * W + 2 := by
            omega
          _ ≤ (n + 1) + (n + 1) * W + 2 * (n + 1) := by
            omega
          _ = (W + 3) * (n + 1) := by
            ring
      have hFactor :
          2 + Γ.maxArity * ((formulaVarBound φ + φ.length * W) + 2) ≤
            A * (n + 1) := by
        have hMul :=
          Nat.mul_le_mul_left Γ.maxArity hVarBlock
        calc
          2 + Γ.maxArity * ((formulaVarBound φ + φ.length * W) + 2)
              ≤ 2 + Γ.maxArity * ((W + 3) * (n + 1)) :=
            Nat.add_le_add_left hMul 2
          _ ≤ 2 * (n + 1) + Γ.maxArity * ((W + 3) * (n + 1)) := by
            omega
          _ = A * (n + 1) := by
            ring
      have hBlocks : φ.length * M ≤ M * n := by
        have h := Nat.mul_le_mul_right M hLen
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
      have hSquare : n * (n + 1) ≤ (n + 1) ^ 2 := by
        have h := Nat.mul_le_mul_right (n + 1) (Nat.le_succ n)
        simp [pow_two] at h ⊢
      calc
        (satSDecisionProblem Γ).Instance.inputSize (formulaViaRepresentation rep φ)
            ≤ (φ.length * M) *
                (2 + Γ.maxArity * ((formulaVarBound φ + φ.length * W) + 2)) := by
          simpa [EncodedType.inputSize, satSDecisionProblem, CSP.boolCSPDecisionProblem,
            CSP.boolCSPSatLike, CSP.formulaEncodedType, M, W] using hEncoded
        _ ≤ (M * n) * (A * (n + 1)) :=
          Nat.mul_le_mul hBlocks hFactor
        _ = M * A * (n * (n + 1)) := by
          ring
        _ ≤ M * A * ((n + 1) ^ 2) :=
          Nat.mul_le_mul_left (M * A) hSquare
        _ ≤ M * A * (4 * n ^ 2 + 1) := by
          exact Nat.mul_le_mul_left (M * A)
            (CSP.Formula.add_one_sq_le_four_sq_add_one n)
        _ = (M * A * 4) * n ^ 2 + M * A := by
          ring
        _ = (rep.maxBlockConstraints *
              (2 + Γ.maxArity * (rep.auxBlockWidth + 3)) * 4) *
              ((satSDecisionProblem Δ).Instance.inputSize φ) ^ 2 +
            rep.maxBlockConstraints *
              (2 + Γ.maxArity * (rep.auxBlockWidth + 3)) := by
          simp [n, M, W, A])

noncomputable def formulaViaRepresentation_polytime {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) :
    CostedPolyTimeModel.IsPolyTimeMap
      (X := (satSDecisionProblem Δ).Instance)
      (Y := (satSDecisionProblem Γ).Instance)
      (formulaViaRepresentation rep) :=
  CostedPolyTimeMap.of_costed
    (CostedMap.of_encodedPolynomialSizeBound
      (formulaViaRepresentation_polynomialSizeBound rep))

theorem constraintViaRepresentationAt_project {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (c : CSP.Constraint Δ)
    (auxBase : Nat) {a : SAT.Assignment}
    (hSat : CSP.Formula.Satisfies (constraintViaRepresentationAt rep c auxBase) a) :
    CSP.Constraint.Satisfies c a := by
  have hMapped :
      CSP.Formula.Satisfies (rep.block c.symbol).constraints
        (fun x => a (representationBlockVarMap c auxBase x)) := by
    exact (formulaMapVars_satisfies_iff
      (representationBlockVarMap c auxBase)
      (rep.block c.symbol).constraints a).1 hSat
  let aux : SAT.Assignment := fun x => a (auxBase + x)
  have hExtend :
      CSP.Formula.Satisfies (rep.block c.symbol).constraints
        (extendTupleAssignment (CSP.Constraint.assignmentTuple c a) aux) := by
    refine (FiniteSearch.formula_satisfies_iff_of_agree
      (φ := (rep.block c.symbol).constraints)
      (a := extendTupleAssignment (CSP.Constraint.assignmentTuple c a) aux)
      (b := fun x => a (representationBlockVarMap c auxBase x)) ?_).2 hMapped
    intro x _hx
    by_cases hFree : x < (Δ.relationOf c.symbol).arity
    · simp [extendTupleAssignment, CSP.Constraint.assignmentTuple,
        representationBlockVarMap, hFree]
    · simp [extendTupleAssignment, representationBlockVarMap, aux, hFree]
  exact (rep.represents c.symbol (CSP.Constraint.assignmentTuple c a)).2 ⟨aux, hExtend⟩

theorem constraintViaRepresentationAt_lift
    {Δ Γ : CSP.BoolLanguage} (rep : LanguageRepresentation Δ Γ)
    (c : CSP.Constraint Δ) (auxBase blockWidth : Nat)
    {source aux tail : SAT.Assignment}
    (hSourceVars : ∀ i : Fin (Δ.relationOf c.symbol).arity, c.vars i < auxBase)
    (hWidth :
      ∀ x ∈ FiniteSearch.formulaVars (rep.block c.symbol).constraints, x < blockWidth)
    (hBlock :
      CSP.Formula.Satisfies (rep.block c.symbol).constraints
        (extendTupleAssignment (CSP.Constraint.assignmentTuple c source) aux)) :
    CSP.Formula.Satisfies (constraintViaRepresentationAt rep c auxBase)
      (mergeBlockAssignment auxBase blockWidth source aux tail) := by
  let target := mergeBlockAssignment auxBase blockWidth source aux tail
  have hMapped :
      CSP.Formula.Satisfies (rep.block c.symbol).constraints
        (fun x => target (representationBlockVarMap c auxBase x)) := by
    refine (FiniteSearch.formula_satisfies_iff_of_agree
      (φ := (rep.block c.symbol).constraints)
      (a := fun x => target (representationBlockVarMap c auxBase x))
      (b := extendTupleAssignment (CSP.Constraint.assignmentTuple c source) aux)
      ?_).2 hBlock
    intro x hx
    by_cases hFree : x < (Δ.relationOf c.symbol).arity
    · have hSrc : c.vars ⟨x, hFree⟩ < auxBase := hSourceVars ⟨x, hFree⟩
      simp [target, representationBlockVarMap, extendTupleAssignment,
        CSP.Constraint.assignmentTuple, hFree, hSrc]
    · have hxWidth : x < blockWidth := hWidth x hx
      simp [target, representationBlockVarMap, extendTupleAssignment, hFree,
        mergeBlockAssignment_aux_add (auxBase := auxBase) (blockWidth := blockWidth)
          (source := source) (aux := aux) (tail := tail) hxWidth]
  exact (formulaMapVars_satisfies_iff
    (representationBlockVarMap c auxBase)
    (rep.block c.symbol).constraints
    (mergeBlockAssignment auxBase blockWidth source aux tail)).2 hMapped

theorem formulaViaRepresentationFrom_project {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (auxBase blockWidth : Nat)
    (φ : SATFormula Δ) {a : SAT.Assignment}
    (hSat :
      CSP.Formula.Satisfies (formulaViaRepresentationFrom rep auxBase blockWidth φ) a) :
    CSP.Formula.Satisfies φ a := by
  induction φ generalizing auxBase with
  | nil =>
      simp [CSP.Formula.Satisfies]
  | cons c φ ih =>
      rw [formulaViaRepresentationFrom] at hSat
      have hBoth :=
        (CSP.Formula.satisfies_append
          (constraintViaRepresentationAt rep c auxBase)
          (formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ)
          a).1 hSat
      exact (CSP.Formula.satisfies_cons c φ a).2
        ⟨constraintViaRepresentationAt_project rep c auxBase hBoth.1,
          ih (auxBase := auxBase + blockWidth) hBoth.2⟩

theorem formulaViaRepresentation_project {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (φ : SATFormula Δ) {a : SAT.Assignment}
    (hSat : CSP.Formula.Satisfies (formulaViaRepresentation rep φ) a) :
    CSP.Formula.Satisfies φ a :=
  formulaViaRepresentationFrom_project rep (formulaVarBound φ) rep.auxBlockWidth φ hSat

theorem formulaViaRepresentationFrom_lift {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (auxBase blockWidth : Nat)
    (φ : SATFormula Δ) {source : SAT.Assignment}
    (hWidth :
      ∀ s : Δ.Symbol, ∀ x ∈ FiniteSearch.formulaVars (rep.block s).constraints,
        x < blockWidth)
    (hSource :
      ∀ c ∈ φ, ∀ i : Fin (Δ.relationOf c.symbol).arity, c.vars i < auxBase)
    (hSat : CSP.Formula.Satisfies φ source) :
    ∃ target : SAT.Assignment,
      CSP.Formula.Satisfies (formulaViaRepresentationFrom rep auxBase blockWidth φ) target ∧
        ∀ x : Nat, x < auxBase → target x = source x := by
  induction φ generalizing auxBase with
  | nil =>
      exact ⟨source, by simp [formulaViaRepresentationFrom, CSP.Formula.Satisfies],
        fun _ _ => rfl⟩
  | cons c φ ih =>
      have hCons := (CSP.Formula.satisfies_cons c φ source).1 hSat
      have hSourceTailNext :
          ∀ d ∈ φ, ∀ i : Fin (Δ.relationOf d.symbol).arity,
            d.vars i < auxBase + blockWidth := by
        intro d hd i
        have hlt : d.vars i < auxBase := hSource d (by simp [hd]) i
        omega
      rcases ih (auxBase := auxBase + blockWidth) hSourceTailNext hCons.2 with
        ⟨tail, hTailSat, hTailAgree⟩
      rcases (rep.represents c.symbol (CSP.Constraint.assignmentTuple c source)).1 hCons.1 with
        ⟨aux, hBlockSat⟩
      let target := mergeBlockAssignment auxBase blockWidth source aux tail
      have hHeadSat :
          CSP.Formula.Satisfies (constraintViaRepresentationAt rep c auxBase) target :=
        constraintViaRepresentationAt_lift rep c auxBase blockWidth
          (source := source) (aux := aux) (tail := tail)
          (fun i => hSource c (by simp) i)
          (hWidth c.symbol)
          hBlockSat
      have hTailSatTarget :
          CSP.Formula.Satisfies
            (formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ) target := by
        refine (FiniteSearch.formula_satisfies_iff_of_agree
          (φ := formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ)
          (a := target) (b := tail) ?_).2 hTailSat
        intro y hy
        have hSourceTailCurrent :
            ∀ d ∈ φ, ∀ i : Fin (Δ.relationOf d.symbol).arity, d.vars i < auxBase := by
          intro d hd i
          exact hSource d (by simp [hd]) i
        have hClass :=
          formulaViaRepresentationFrom_vars_source_or_aux
            (rep := rep)
            (sourceBound := auxBase)
            (auxBase := auxBase + blockWidth)
            (blockWidth := blockWidth)
            hSourceTailCurrent
            (Nat.le_add_right auxBase blockWidth)
            hy
        rcases hClass with hSrc | hAux
        · have hTarget : target y = source y := by
            simp [target, hSrc]
          have hTail : tail y = source y := hTailAgree y (by omega)
          exact hTarget.trans hTail.symm
        · have hTarget : target y = tail y := by
            exact mergeBlockAssignment_tail
              (auxBase := auxBase) (blockWidth := blockWidth)
              (source := source) (aux := aux) (tail := tail) hAux
          exact hTarget
      refine ⟨target, ?_, ?_⟩
      · rw [formulaViaRepresentationFrom]
        exact (CSP.Formula.satisfies_append
          (constraintViaRepresentationAt rep c auxBase)
          (formulaViaRepresentationFrom rep (auxBase + blockWidth) blockWidth φ)
          target).2 ⟨hHeadSat, hTailSatTarget⟩
      · intro x hx
        simp [target, hx]

theorem formulaViaRepresentation_lift {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (φ : SATFormula Δ) {source : SAT.Assignment}
    (hSat : CSP.Formula.Satisfies φ source) :
    ∃ target : SAT.Assignment,
      CSP.Formula.Satisfies (formulaViaRepresentation rep φ) target := by
  have hWidth :
      ∀ s : Δ.Symbol, ∀ x ∈ FiniteSearch.formulaVars (rep.block s).constraints,
        x < rep.auxBlockWidth := by
    intro s x hx
    exact rep.var_lt_auxBlockWidth s hx
  have hSource :
      ∀ c ∈ φ, ∀ i : Fin (Δ.relationOf c.symbol).arity,
        c.vars i < formulaVarBound φ := by
    intro c hc i
    exact constraint_var_lt_formulaVarBound_of_mem hc i
  rcases formulaViaRepresentationFrom_lift rep (formulaVarBound φ) rep.auxBlockWidth
      φ hWidth hSource hSat with
    ⟨target, hTarget, _hAgree⟩
  exact ⟨target, hTarget⟩

end Hardness
end Schaefer
end ComplexityReduction
