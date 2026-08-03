/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.CSP.FiniteDomain.PPDef
import ComplexityReduction.CSP.FiniteDomain.FiniteSupport

/-!
Reusable primitive-positive relation gadgets for finite-domain CSPs.

These constructions formalize the first derived-relation operations used by
Jeavons-Cohen-Gyssens: conjunction of pp formulas, equality selection through
coordinate maps, and projection by turning trailing free coordinates into
existentially quantified variables.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace PPDef

namespace RelationFormula

/-- The relation defined by a pp block, with the block arity as its free arity. -/
def definedRel {D : Type} {Γ : Language D} {arity : Nat}
    (rep : RelationFormula Γ arity) : Rel D where
  arity := arity
  holds := fun t =>
    ∃ aux : Assignment D, Formula.Satisfies rep.constraints (extendTupleAssignment t aux)

/-- Every pp block represents the relation it defines. -/
theorem represents_definedRel {D : Type} {Γ : Language D} {arity : Nat}
    (rep : RelationFormula Γ arity) :
    RepresentsRelation Γ (rep.definedRel) rep := by
  intro t
  rfl

end RelationFormula

/-- Conjunction/product of two pp formulas with the same free variables. -/
def conjunctionFormula {D : Type} {Γ : Language D} {arity : Nat}
    (left right : RelationFormula Γ arity) : RelationFormula Γ arity where
  constraints := left.constraints ++ right.constraints
  notes := "conjunction"

theorem conjunctionFormula_represents_definedRel {D : Type} {Γ : Language D}
    {arity : Nat} (left right : RelationFormula Γ arity) :
    RepresentsRelation Γ (RelationFormula.definedRel (conjunctionFormula left right))
      (conjunctionFormula left right) :=
  RelationFormula.represents_definedRel _

/-- List-folded conjunction of pp blocks with the same exposed arity. -/
def conjunctionListFormula {D : Type} {Γ : Language D} {arity : Nat} :
    List (RelationFormula Γ arity) → RelationFormula Γ arity
  | [] => { constraints := [], notes := "conjunction_list" }
  | block :: blocks =>
      { constraints := block.constraints ++ (conjunctionListFormula blocks).constraints
        notes := "conjunction_list" }

/-- A folded conjunction block represents the relation it definitionally induces. -/
theorem conjunctionListFormula_represents {D : Type} {Γ : Language D} {arity : Nat}
    (blocks : List (RelationFormula Γ arity)) :
    RepresentsRelation Γ (RelationFormula.definedRel (conjunctionListFormula blocks))
      (conjunctionListFormula blocks) :=
  RelationFormula.represents_definedRel _

/-- Constraint count of a list-folded conjunction block. -/
theorem conjunctionListFormula_constraints_length {D : Type} {Γ : Language D}
    {arity : Nat} (blocks : List (RelationFormula Γ arity)) :
    (conjunctionListFormula blocks).constraints.length =
      (blocks.map fun block => block.constraints.length).sum := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      simp [conjunctionListFormula, ih]

/-- Tuple concatenation used by projection gadgets. -/
def appendTuple {D : Type} {k m : Nat} (left : Tuple D k) (right : Tuple D m) :
    Tuple D (k + m) :=
  fun i =>
    if h : i.val < k then
      left ⟨i.val, h⟩
    else
      right ⟨i.val - k, by omega⟩

@[simp]
theorem appendTuple_left {D : Type} {k m : Nat} (left : Tuple D k)
    (right : Tuple D m) (i : Fin k) :
    appendTuple left right ⟨i.val, by omega⟩ = left i := by
  simp [appendTuple]

@[simp]
theorem appendTuple_right {D : Type} {k m : Nat} (left : Tuple D k)
    (right : Tuple D m) (i : Fin m) :
    appendTuple left right ⟨k + i.val, by omega⟩ = right i := by
  have h : ¬ k + i.val < k := by omega
  simp [appendTuple, h]

/-- The first block of coordinates of a concatenated tuple. -/
def productLeftTuple {D : Type} {k m : Nat} (t : Tuple D (k + m)) : Tuple D k :=
  fun i => t ⟨i.val, by omega⟩

/-- The second block of coordinates of a concatenated tuple. -/
def productRightTuple {D : Type} {k m : Nat} (t : Tuple D (k + m)) : Tuple D m :=
  fun i => t ⟨k + i.val, by omega⟩

@[simp]
theorem productLeftTuple_appendTuple {D : Type} {k m : Nat}
    (left : Tuple D k) (right : Tuple D m) :
    productLeftTuple (appendTuple left right) = left := by
  funext i
  simp [productLeftTuple]

@[simp]
theorem productRightTuple_appendTuple {D : Type} {k m : Nat}
    (left : Tuple D k) (right : Tuple D m) :
    productRightTuple (appendTuple left right) = right := by
  funext i
  simp [productRightTuple]

/-- Cartesian product of two relations. -/
def productRel {D : Type} (left right : Rel D) : Rel D where
  arity := left.arity + right.arity
  holds := fun t => left.Holds (productLeftTuple t) ∧ right.Holds (productRightTuple t)

/-- Variable map for the left block of an independent product pp formula. -/
def productLeftVarMap (leftArity rightArity : Nat) (x : Nat) : Nat :=
  if x < leftArity then x else leftArity + rightArity + x

/-- Variable map for the right block of an independent product pp formula. -/
def productRightVarMap (leftArity rightArity leftWidth : Nat) (x : Nat) : Nat :=
  if x < rightArity then leftArity + x else leftArity + rightArity + leftWidth + x

/-- Combine two old auxiliary witnesses into the fresh auxiliary space of a product block. -/
def productAuxFromOld {D : Type} (freeArity leftWidth : Nat)
    (leftAux rightAux : Assignment D) : Assignment D :=
  fun x =>
    if x < freeArity + leftWidth then
      leftAux (x - freeArity)
    else
      rightAux (x - (freeArity + leftWidth))

/-- Cartesian product pp formula with an explicit left auxiliary allocation width. -/
def productFormulaWithLeftWidth {D : Type} {Γ : Language D} {leftArity rightArity : Nat}
    (leftWidth : Nat) (left : RelationFormula Γ leftArity)
    (right : RelationFormula Γ rightArity) :
    RelationFormula Γ (leftArity + rightArity) where
  constraints :=
    Formula.mapVars (productLeftVarMap leftArity rightArity) left.constraints ++
      Formula.mapVars (productRightVarMap leftArity rightArity leftWidth) right.constraints
  notes := "product"

theorem product_left_assignment_from_old {D : Type} {k m : Nat}
    (leftWidth : Nat) (t : Tuple D (k + m)) (leftAux rightAux : Assignment D)
    {x : Nat} (hxAuxBound : ¬ x < k → x < leftWidth) :
    extendTupleAssignment t
        (productAuxFromOld (k + m) leftWidth leftAux rightAux)
        (productLeftVarMap k m x) =
      extendTupleAssignment (productLeftTuple t) leftAux x := by
  by_cases hx : x < k
  · have hxFree : x < k + m := by omega
    simp [productLeftVarMap, extendTupleAssignment, productLeftTuple, hx, hxFree]
  · have hxFree : ¬ k + m + x < k + m := by omega
    have hxWindow : k + m + x < k + m + leftWidth := by
      have hxBound := hxAuxBound hx
      omega
    simp [productLeftVarMap, productAuxFromOld, extendTupleAssignment, hx, hxFree,
      hxWindow]

theorem product_right_assignment_from_old {D : Type} {k m : Nat}
    (leftWidth : Nat) (t : Tuple D (k + m)) (leftAux rightAux : Assignment D)
    (x : Nat) :
    extendTupleAssignment t
        (productAuxFromOld (k + m) leftWidth leftAux rightAux)
        (productRightVarMap k m leftWidth x) =
      extendTupleAssignment (productRightTuple t) rightAux x := by
  by_cases hx : x < m
  · have hxFree : k + x < k + m := by omega
    simp [productRightVarMap, extendTupleAssignment, productRightTuple, hx, hxFree]
  · have hxFree : ¬ k + m + leftWidth + x < k + m := by omega
    have hxWindow : ¬ k + m + leftWidth + x < k + m + leftWidth := by omega
    have hxSub : k + m + leftWidth + x - (k + m + leftWidth) = x := by omega
    simp [productRightVarMap, productAuxFromOld, extendTupleAssignment, hx, hxFree,
      hxWindow, hxSub]

theorem product_left_assignment_to_old {D : Type} {k m : Nat}
    (_leftWidth : Nat) (t : Tuple D (k + m)) (aux : Assignment D) (x : Nat) :
    extendTupleAssignment t aux (productLeftVarMap k m x) =
      extendTupleAssignment (productLeftTuple t) (fun y => aux (k + m + y)) x := by
  by_cases hx : x < k
  · have hxFree : x < k + m := by omega
    simp [productLeftVarMap, extendTupleAssignment, productLeftTuple, hx, hxFree]
  · have hxFree : ¬ k + m + x < k + m := by omega
    simp [productLeftVarMap, extendTupleAssignment, hx, hxFree]

theorem product_right_assignment_to_old {D : Type} {k m : Nat}
    (leftWidth : Nat) (t : Tuple D (k + m)) (aux : Assignment D) (x : Nat) :
    extendTupleAssignment t aux (productRightVarMap k m leftWidth x) =
      extendTupleAssignment (productRightTuple t)
        (fun y => aux (k + m + leftWidth + y)) x := by
  by_cases hx : x < m
  · have hxFree : k + x < k + m := by omega
    simp [productRightVarMap, extendTupleAssignment, productRightTuple, hx, hxFree]
  · have hxFree : ¬ k + m + leftWidth + x < k + m := by omega
    simp [productRightVarMap, extendTupleAssignment, hx, hxFree]

/-- Cartesian product preserves pp-definability with explicit fresh auxiliary allocation. -/
theorem productFormulaWithLeftWidth_represents {D : Type} {Γ : Language D}
    {leftRel rightRel : Rel D}
    (leftWidth : Nat) (left : RelationFormula Γ leftRel.arity)
    (right : RelationFormula Γ rightRel.arity)
    (hLeftRep : RepresentsRelation Γ leftRel left)
    (hRightRep : RepresentsRelation Γ rightRel right)
    (hLeftAuxBound :
      ∀ c ∈ left.constraints, ∀ i : Fin (Γ.relationOf c.symbol).arity,
        ¬ c.vars i < leftRel.arity → c.vars i < leftWidth) :
    RepresentsRelation Γ (productRel leftRel rightRel)
      (productFormulaWithLeftWidth leftWidth left right) := by
  intro t
  constructor
  · intro hProduct
    rcases (hLeftRep (productLeftTuple t)).1 hProduct.1 with ⟨leftAux, hLeftAux⟩
    rcases (hRightRep (productRightTuple t)).1 hProduct.2 with ⟨rightAux, hRightAux⟩
    let aux :=
      productAuxFromOld (leftRel.arity + rightRel.arity) leftWidth leftAux rightAux
    refine ⟨aux, ?_⟩
    have hLeftMapped :
        Formula.Satisfies
          (Formula.mapVars (productLeftVarMap leftRel.arity rightRel.arity)
            left.constraints)
          (extendTupleAssignment t aux) := by
      refine (Formula.mapVars_satisfies_iff
        (productLeftVarMap leftRel.arity rightRel.arity)
        left.constraints (extendTupleAssignment t aux)).2 ?_
      exact Formula.satisfies_of_eq_on_vars left.constraints (by
        intro c hc i
        simpa [aux] using product_left_assignment_from_old leftWidth t leftAux rightAux
          (hLeftAuxBound c hc i)) hLeftAux
    have hRightMapped :
        Formula.Satisfies
          (Formula.mapVars
            (productRightVarMap leftRel.arity rightRel.arity leftWidth)
            right.constraints)
          (extendTupleAssignment t aux) := by
      refine (Formula.mapVars_satisfies_iff
        (productRightVarMap leftRel.arity rightRel.arity leftWidth)
        right.constraints (extendTupleAssignment t aux)).2 ?_
      exact Formula.satisfies_of_eq_on_vars right.constraints (by
        intro c hc i
        simpa [aux] using product_right_assignment_from_old leftWidth t leftAux rightAux
          (c.vars i)) hRightAux
    exact (Formula.satisfies_append _ _ _).2 ⟨hLeftMapped, hRightMapped⟩
  · rintro ⟨aux, hAux⟩
    have hAppend := (Formula.satisfies_append _ _ _).1 hAux
    have hLeftMapped := (Formula.mapVars_satisfies_iff
      (productLeftVarMap leftRel.arity rightRel.arity)
      left.constraints (extendTupleAssignment t aux)).1 hAppend.1
    have hRightMapped := (Formula.mapVars_satisfies_iff
      (productRightVarMap leftRel.arity rightRel.arity leftWidth)
      right.constraints (extendTupleAssignment t aux)).1 hAppend.2
    constructor
    · refine (hLeftRep (productLeftTuple t)).2 ?_
      refine ⟨fun x => aux (leftRel.arity + rightRel.arity + x), ?_⟩
      exact Formula.satisfies_of_eq_on_vars left.constraints (by
        intro c hc i
        exact (product_left_assignment_to_old leftWidth t aux (c.vars i)).symm)
        hLeftMapped
    · refine (hRightRep (productRightTuple t)).2 ?_
      refine ⟨fun x => aux (leftRel.arity + rightRel.arity + leftWidth + x), ?_⟩
      exact Formula.satisfies_of_eq_on_vars right.constraints (by
        intro c hc i
        exact (product_right_assignment_to_old leftWidth t aux (c.vars i)).symm)
        hRightMapped

/-- A relation/formula pair used by folded product constructors. -/
structure ProductBlock {D : Type} (Γ : Language D) where
  rel : Rel D
  formula : RelationFormula Γ rel.arity

/-- The empty product relation over zero exposed variables. -/
def unitProductRel (D : Type) : Rel D where
  arity := 0
  holds := fun _ => True

/-- The empty pp block for the empty product relation. -/
def unitProductFormula {D : Type} (Γ : Language D) : RelationFormula Γ 0 where
  constraints := []
  notes := "unit_product"

/-- Empty product block correctness. -/
theorem unitProductFormula_represents {D : Type} [Inhabited D] {Γ : Language D} :
    RepresentsRelation Γ (unitProductRel D) (unitProductFormula Γ) := by
  intro _t
  constructor
  · intro _h
    exact ⟨fun _ => default, by simp [unitProductFormula]⟩
  · intro _h
    simp [unitProductRel]

/-- Fold a list of relation blocks into an iterated Cartesian-product relation. -/
def foldProductRel {D : Type} {Γ : Language D} :
    List (ProductBlock Γ) → Rel D
  | [] => unitProductRel D
  | block :: blocks => productRel block.rel (foldProductRel blocks)

/-- Fold a list of pp blocks into an iterated Cartesian-product pp formula. -/
noncomputable def foldProductFormula {D : Type} [Inhabited D] {Γ : Language D} :
    (blocks : List (ProductBlock Γ)) → RelationFormula Γ (foldProductRel blocks).arity
  | [] => unitProductFormula Γ
  | block :: blocks =>
      productFormulaWithLeftWidth
        (FiniteSupport.formulaVarBound block.formula.constraints)
        block.formula
        (foldProductFormula blocks)

private theorem block_formula_var_lt_bound {D : Type} {Γ : Language D} {arity : Nat}
    (block : RelationFormula Γ arity) :
    ∀ c ∈ block.constraints,
      ∀ i : Fin (Γ.relationOf c.symbol).arity,
        c.vars i < FiniteSupport.formulaVarBound block.constraints := by
  intro c hc i
  exact FiniteSupport.var_lt_formulaVarBound
    (FiniteSupport.var_mem_formulaVars_of_constraint_mem hc i)

/-- Iterated Cartesian product preserves pp-definability under local block witnesses. -/
theorem foldProductFormula_represents {D : Type} [Inhabited D] {Γ : Language D}
    (blocks : List (ProductBlock Γ))
    (hReps : ∀ block ∈ blocks, RepresentsRelation Γ block.rel block.formula) :
    RepresentsRelation Γ (foldProductRel blocks) (foldProductFormula blocks) := by
  induction blocks with
  | nil =>
      simpa [foldProductRel, foldProductFormula] using
        (unitProductFormula_represents (D := D) (Γ := Γ))
  | cons block blocks ih =>
      have hTail :
          ∀ tailBlock ∈ blocks, RepresentsRelation Γ tailBlock.rel tailBlock.formula := by
        intro tailBlock hmem
        exact hReps tailBlock (List.mem_cons_of_mem block hmem)
      simpa [foldProductRel, foldProductFormula] using
        productFormulaWithLeftWidth_represents
          (FiniteSupport.formulaVarBound block.formula.constraints)
          block.formula
          (foldProductFormula blocks)
          (hReps block (by simp))
          (ih hTail)
          (by
            intro c hc i _hAux
            exact block_formula_var_lt_bound block.formula c hc i)

/-- Equality selection: old coordinate `i` is read from new coordinate `σ i`. -/
def selectedRel {D : Type} (R : Rel D) {arity : Nat}
    (σ : Fin R.arity → Fin arity) : Rel D where
  arity := arity
  holds := fun t => R.Holds (fun i => t (σ i))

/-- Variable renaming for equality selection, preserving auxiliaries after the new free block. -/
def selectionVarMap {oldArity arity : Nat}
    (σ : Fin oldArity → Fin arity) (x : Nat) : Nat :=
  if h : x < oldArity then (σ ⟨x, h⟩).val else arity + x

/-- Apply an equality-selection coordinate map to a pp block. -/
def selectedFormula {D : Type} {Γ : Language D} {oldArity arity : Nat}
    (rep : RelationFormula Γ oldArity)
    (σ : Fin oldArity → Fin arity) : RelationFormula Γ arity where
  constraints := Formula.mapVars (selectionVarMap σ) rep.constraints
  notes := "selection"

/-- Extend an old auxiliary witness into the renamed auxiliary space. -/
def selectionAuxFromOld {D : Type} {arity : Nat}
    (t : Tuple D arity) (aux : Assignment D) : Assignment D :=
  fun x => if h : x < arity then t ⟨x, h⟩ else aux (x - arity)

theorem selection_assignment_from_old {D : Type} {oldArity arity : Nat}
    (σ : Fin oldArity → Fin arity) (t : Tuple D arity) (aux : Assignment D) :
    (fun x =>
      extendTupleAssignment t (selectionAuxFromOld t aux) (selectionVarMap σ x)) =
      extendTupleAssignment (fun i => t (σ i)) aux := by
  funext x
  by_cases hx : x < oldArity
  · have hσ : (σ ⟨x, hx⟩).val < arity := (σ ⟨x, hx⟩).isLt
    simp [selectionVarMap, hx, hσ]
  · have hArity : ¬ arity + x < arity := by omega
    simp [selectionVarMap, selectionAuxFromOld, hx, hArity]

theorem selection_assignment_to_old {D : Type} {oldArity arity : Nat}
    (σ : Fin oldArity → Fin arity) (t : Tuple D arity) (aux : Assignment D) :
    (fun x => extendTupleAssignment t aux (selectionVarMap σ x)) =
      extendTupleAssignment (fun i => t (σ i)) (fun x => aux (arity + x)) := by
  funext x
  by_cases hx : x < oldArity
  · have hσ : (σ ⟨x, hx⟩).val < arity := (σ ⟨x, hx⟩).isLt
    simp [selectionVarMap, hx, hσ]
  · have hArity : ¬ arity + x < arity := by omega
    simp [selectionVarMap, hx, hArity]

/-- Equality selection preserves pp-definability. -/
theorem selectedFormula_represents {D : Type} {Γ : Language D} {R : Rel D}
    {arity : Nat} (rep : RelationFormula Γ R.arity)
    (σ : Fin R.arity → Fin arity)
    (hRep : RepresentsRelation Γ R rep) :
    RepresentsRelation Γ (selectedRel R σ) (selectedFormula rep σ) := by
  intro t
  constructor
  · intro hSelected
    rcases (hRep (fun i => t (σ i))).1 hSelected with ⟨aux, hAux⟩
    refine ⟨selectionAuxFromOld t aux, ?_⟩
    have hAssign := selection_assignment_from_old σ t aux
    exact (Formula.mapVars_satisfies_iff (selectionVarMap σ) rep.constraints
      (extendTupleAssignment t (selectionAuxFromOld t aux))).2 (by
        exact Formula.satisfies_of_eq_on_vars rep.constraints (by
          intro c hc i
          exact congrFun hAssign (c.vars i)) hAux)
  · rintro ⟨aux, hAux⟩
    refine (hRep (fun i => t (σ i))).2 ?_
    refine ⟨fun x => aux (arity + x), ?_⟩
    have hMapped := (Formula.mapVars_satisfies_iff (selectionVarMap σ)
      rep.constraints (extendTupleAssignment t aux)).1 hAux
    have hAssign := selection_assignment_to_old σ t aux
    exact Formula.satisfies_of_eq_on_vars rep.constraints (by
      intro c hc i
      exact (congrFun hAssign (c.vars i)).symm) hMapped

/-- Projection of a relation on `k + m` coordinates onto its first `k` coordinates. -/
def projectFirstRel {D : Type} {k m : Nat}
    (P : Tuple D (k + m) → Prop) : Rel D where
  arity := k
  holds := fun t => ∃ u : Tuple D m, P (appendTuple t u)

/-- Projection leaves the same pp constraints but exposes fewer free variables. -/
def projectFormula {D : Type} {Γ : Language D} {k m : Nat}
    (rep : RelationFormula Γ (k + m)) : RelationFormula Γ k where
  constraints := rep.constraints
  notes := "projection"

def projectionAuxFromOld {D : Type} {k m : Nat}
    (t : Tuple D k) (u : Tuple D m) (aux : Assignment D) : Assignment D :=
  fun x => if h : x < k + m then appendTuple t u ⟨x, h⟩ else aux x

def projectionTupleFromAux {D : Type} (k : Nat) {m : Nat}
    (aux : Assignment D) : Tuple D m :=
  fun i => aux (k + i.val)

theorem projection_assignment_from_old {D : Type} {k m : Nat}
    (t : Tuple D k) (u : Tuple D m) (aux : Assignment D) :
    extendTupleAssignment t (projectionAuxFromOld t u aux) =
      extendTupleAssignment (appendTuple t u) aux := by
  funext x
  by_cases hxk : x < k
  · have hxkm : x < k + m := by omega
    simp [extendTupleAssignment, appendTuple, hxk, hxkm]
  · by_cases hxkm : x < k + m
    · simp [extendTupleAssignment, projectionAuxFromOld, hxk, hxkm]
    · simp [extendTupleAssignment, projectionAuxFromOld, hxk, hxkm]

theorem projection_assignment_to_old {D : Type} {k m : Nat}
    (t : Tuple D k) (aux : Assignment D) :
    extendTupleAssignment
      (appendTuple t (projectionTupleFromAux k (m := m) aux)) aux =
      extendTupleAssignment t aux := by
  funext x
  by_cases hxk : x < k
  · have hxkm : x < k + m := by omega
    simp [extendTupleAssignment, appendTuple, hxk, hxkm]
  · by_cases hxkm : x < k + m
    · have hxle : k ≤ x := Nat.le_of_not_gt hxk
      have hxSub : k + (x - k) = x := Nat.add_sub_of_le hxle
      simp [extendTupleAssignment, appendTuple, projectionTupleFromAux, hxk, hxkm, hxSub]
    · simp [extendTupleAssignment, hxk, hxkm]

/-- Projection/existential quantification preserves pp-definability. -/
theorem projectFormula_represents {D : Type} {Γ : Language D} {k m : Nat}
    {P : Tuple D (k + m) → Prop} (rep : RelationFormula Γ (k + m))
    (hRep : RepresentsRelation Γ (Rel.mk (k + m) P) rep) :
    RepresentsRelation Γ (projectFirstRel P) (projectFormula rep) := by
  intro t
  constructor
  · rintro ⟨u, hP⟩
    rcases (hRep (appendTuple t u)).1 hP with ⟨aux, hAux⟩
    refine ⟨projectionAuxFromOld t u aux, ?_⟩
    have hAssign := projection_assignment_from_old t u aux
    change Formula.Satisfies rep.constraints
      (extendTupleAssignment t (projectionAuxFromOld t u aux))
    exact Formula.satisfies_of_eq_on_vars rep.constraints (by
      intro c hc i
      exact congrFun hAssign (c.vars i)) hAux
  · rintro ⟨aux, hAux⟩
    refine ⟨projectionTupleFromAux k (m := m) aux, ?_⟩
    refine (hRep (appendTuple t (projectionTupleFromAux k (m := m) aux))).2 ?_
    refine ⟨aux, ?_⟩
    have hAssign := projection_assignment_to_old (m := m) t aux
    have hAssign' :
        extendTupleAssignment (appendTuple t (projectionTupleFromAux k (m := m) aux)) aux =
          extendTupleAssignment t aux := by
      simpa [projectFirstRel] using hAssign
    change Formula.Satisfies rep.constraints
      (extendTupleAssignment (appendTuple t (projectionTupleFromAux k (m := m) aux)) aux)
    change Formula.Satisfies rep.constraints (extendTupleAssignment t aux) at hAux
    exact Formula.satisfies_of_eq_on_vars rep.constraints (by
      intro c hc i
      exact congrFun hAssign' (c.vars i)) hAux

end PPDef
end FiniteDomain
end CSP
end ComplexityReduction
