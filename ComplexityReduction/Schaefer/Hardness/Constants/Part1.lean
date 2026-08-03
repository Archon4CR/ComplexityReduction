/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Preprocessing.EmptyRelations
import ComplexityReduction.Schaefer.Hardness.Classification

/-!
Local SAT-with-constants layer for the Schaefer hard-side route.

This module models `SAT_C(S)` by extending a local Boolean language with two
unary pinning relations.  If those two pinning relations are representable over
the original language, the generic representation machinery gives a
syntax-only reduction from the with-constants language back to `SAT(S)`.
-/

namespace ComplexityReduction
namespace Schaefer
namespace Hardness

/-- Symbols for the local `SAT_C(S)` language: original symbols plus unary pins. -/
abbrev SatCWithConstantsSymbol (Γ : CSP.BoolLanguage) : Type :=
  Sum Γ.Symbol Bool

/-- The local language for `SAT_C(S)`, adding `pinFalse` and `pinTrue` relations. -/
noncomputable def satCWithConstantsLanguage (Γ : CSP.BoolLanguage) : CSP.BoolLanguage where
  Symbol := SatCWithConstantsSymbol Γ
  finiteSymbol := inferInstance
  relationOf
    | Sum.inl s => Γ.relationOf s
    | Sum.inr false => CSP.StandardRelations.pinFalseRel
    | Sum.inr true => CSP.StandardRelations.pinTrueRel

/-- Local SAT-with-constants formulas over `Γ`. -/
abbrev SatCFormula (Γ : CSP.BoolLanguage) : Type :=
  SATFormula (satCWithConstantsLanguage Γ)

/-- Satisfiability for local SAT-with-constants formulas. -/
abbrev SatCSatisfiable (Γ : CSP.BoolLanguage) (φ : SatCFormula Γ) : Prop :=
  SATSatisfiable φ

/-- Encoded decision problem for the local `SAT_C(S)` language. -/
noncomputable def satCDecisionProblem (Γ : CSP.BoolLanguage) : EncodedDecisionProblem :=
  satSDecisionProblem (satCWithConstantsLanguage Γ)

/-- Embed an original `SAT(S)` constraint into the with-constants language. -/
def originalConstraint {Γ : CSP.BoolLanguage} (c : CSP.Constraint Γ) :
    CSP.Constraint (satCWithConstantsLanguage Γ) where
  symbol := Sum.inl c.symbol
  vars := c.vars

/-- Unary constraint pinning a variable to true in the with-constants language. -/
def pinTrueConstraint (Γ : CSP.BoolLanguage) (v : Nat) :
    CSP.Constraint (satCWithConstantsLanguage Γ) where
  symbol := Sum.inr true
  vars := fun _ => v

/-- Unary constraint pinning a variable to false in the with-constants language. -/
def pinFalseConstraint (Γ : CSP.BoolLanguage) (v : Nat) :
    CSP.Constraint (satCWithConstantsLanguage Γ) where
  symbol := Sum.inr false
  vars := fun _ => v

@[simp]
theorem originalConstraint_satisfies_iff {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint Γ) (a : SAT.Assignment) :
    CSP.Constraint.Satisfies (originalConstraint c) a ↔ CSP.Constraint.Satisfies c a :=
  Iff.rfl

theorem pinTrueConstraint_satisfies_iff (Γ : CSP.BoolLanguage) (v : Nat)
    (a : SAT.Assignment) :
    CSP.Constraint.Satisfies (pinTrueConstraint Γ v) a ↔ a v = true := by
  simpa [CSP.StandardRelations.pinTrueRel] using
    (CSP.BoolRel.holds_ofPredicate_iff 1
      (fun t : CSP.BoolTuple 1 => t ⟨0, by decide⟩ = true)
      (fun _ : Fin 1 => a v))

theorem pinFalseConstraint_satisfies_iff (Γ : CSP.BoolLanguage) (v : Nat)
    (a : SAT.Assignment) :
    CSP.Constraint.Satisfies (pinFalseConstraint Γ v) a ↔ a v = false := by
  simpa [CSP.StandardRelations.pinFalseRel] using
    (CSP.BoolRel.holds_ofPredicate_iff 1
      (fun t : CSP.BoolTuple 1 => t ⟨0, by decide⟩ = false)
      (fun _ : Fin 1 => a v))

/-- Proof-bearing representations of the two unary constants over the original language. -/
structure ConstantRepresentationWitness (Γ : CSP.BoolLanguage) where
  trueBlock : RelationFormula Γ CSP.StandardRelations.pinTrueRel.arity
  trueRepresents :
    RepresentsRelation Γ CSP.StandardRelations.pinTrueRel trueBlock
  falseBlock : RelationFormula Γ CSP.StandardRelations.pinFalseRel.arity
  falseRepresents :
    RepresentsRelation Γ CSP.StandardRelations.pinFalseRel falseBlock
  notes : String := ""

/-- The PDF's Section 4 proof assumes every relation in `S` is nonempty. -/
abbrev AllRelationsNonempty (Γ : CSP.BoolLanguage) : Prop :=
  CSP.AllRelationsNonempty Γ

/-- Proof-bearing representation of the binary disequality/XOR relation. -/
structure XorRepresentationWitness (Γ : CSP.BoolLanguage) where
  xorBlock : RelationFormula Γ CSP.StandardRelations.xorRel.arity
  xorRepresents :
    RepresentsRelation Γ CSP.StandardRelations.xorRel xorBlock
  notes : String := ""

/-- Lemma 4.3's first split: either constants are represented or disequality is. -/
inductive ConstantOrXorWitness (Γ : CSP.BoolLanguage) where
  | constants : ConstantRepresentationWitness Γ → ConstantOrXorWitness Γ
  | xor : XorRepresentationWitness Γ → ConstantOrXorWitness Γ

/-- Lemma 4.3's no-constants split, phrased over proof-bearing local witnesses. -/
inductive ConstantOrComplementiveWitness (Γ : CSP.BoolLanguage) where
  | constants : ConstantRepresentationWitness Γ → ConstantOrComplementiveWitness Γ
  | complementive :
      XorRepresentationWitness Γ →
        AllRelationsSatisfy Γ IsComplementive →
          ConstantOrComplementiveWitness Γ

theorem pinTrueRel_holds_iff (t : CSP.BoolTuple CSP.StandardRelations.pinTrueRel.arity) :
    CSP.StandardRelations.pinTrueRel.Holds t ↔ t ⟨0, by decide⟩ = true := by
  simpa [CSP.StandardRelations.pinTrueRel] using
    (CSP.BoolRel.holds_ofPredicate_iff 1
      (fun t : CSP.BoolTuple 1 => t ⟨0, by decide⟩ = true)
      t)

theorem pinFalseRel_holds_iff (t : CSP.BoolTuple CSP.StandardRelations.pinFalseRel.arity) :
    CSP.StandardRelations.pinFalseRel.Holds t ↔ t ⟨0, by decide⟩ = false := by
  simpa [CSP.StandardRelations.pinFalseRel] using
    (CSP.BoolRel.holds_ofPredicate_iff 1
      (fun t : CSP.BoolTuple 1 => t ⟨0, by decide⟩ = false)
      t)

theorem xorRel_holds_iff (t : CSP.BoolTuple CSP.StandardRelations.xorRel.arity) :
    CSP.StandardRelations.xorRel.Holds t ↔
      t ⟨0, by decide⟩ ≠ t ⟨1, by decide⟩ := by
  simpa [CSP.StandardRelations.xorRel] using
    (CSP.BoolRel.holds_ofPredicate_iff 2
      (fun t : CSP.BoolTuple 2 => t ⟨0, by decide⟩ ≠ t ⟨1, by decide⟩)
      t)

theorem implicationRel_holds_iff
    (t : CSP.BoolTuple CSP.StandardRelations.implicationRel.arity) :
    CSP.StandardRelations.implicationRel.Holds t ↔
      t ⟨0, by decide⟩ = false ∨ t ⟨1, by decide⟩ = true := by
  simpa [CSP.StandardRelations.implicationRel, CSP.StandardRelations.literalValue] using
    (CSP.BoolRel.holds_ofPredicate_iff 2
      (fun t : CSP.BoolTuple 2 =>
        CSP.StandardRelations.literalValue true (t ⟨0, by decide⟩) = true ∨
          CSP.StandardRelations.literalValue false (t ⟨1, by decide⟩) = true)
      t)

/-- Intermediate language with a false pin and binary disequality. -/
inductive PinFalseXorSymbol where
  | pinFalse
  | xor
  deriving DecidableEq, Repr

instance : Fintype PinFalseXorSymbol where
  elems :=
    { val := [PinFalseXorSymbol.pinFalse, PinFalseXorSymbol.xor]
      nodup := by simp }
  complete := by
    intro s
    cases s <;> simp

/-- Intermediate language `{[¬x], [x ≠ y]}`. -/
noncomputable def pinFalseXorLanguage : CSP.BoolLanguage where
  Symbol := PinFalseXorSymbol
  finiteSymbol := inferInstance
  relationOf
    | PinFalseXorSymbol.pinFalse => CSP.StandardRelations.pinFalseRel
    | PinFalseXorSymbol.xor => CSP.StandardRelations.xorRel

/-- Intermediate language with a true pin and binary disequality. -/
inductive PinTrueXorSymbol where
  | pinTrue
  | xor
  deriving DecidableEq, Repr

instance : Fintype PinTrueXorSymbol where
  elems :=
    { val := [PinTrueXorSymbol.pinTrue, PinTrueXorSymbol.xor]
      nodup := by simp }
  complete := by
    intro s
    cases s <;> simp

/-- Intermediate language `{[x], [x ≠ y]}`. -/
noncomputable def pinTrueXorLanguage : CSP.BoolLanguage where
  Symbol := PinTrueXorSymbol
  finiteSymbol := inferInstance
  relationOf
    | PinTrueXorSymbol.pinTrue => CSP.StandardRelations.pinTrueRel
    | PinTrueXorSymbol.xor => CSP.StandardRelations.xorRel

/-- Intermediate language with implication and binary disequality. -/
inductive ImpXorSymbol where
  | implication
  | xor
  deriving DecidableEq, Repr

instance : Fintype ImpXorSymbol where
  elems :=
    { val := [ImpXorSymbol.implication, ImpXorSymbol.xor]
      nodup := by simp }
  complete := by
    intro s
    cases s <;> simp

/-- Intermediate language `{[x -> y], [x ≠ y]}`. -/
noncomputable def impXorLanguage : CSP.BoolLanguage where
  Symbol := ImpXorSymbol
  finiteSymbol := inferInstance
  relationOf
    | ImpXorSymbol.implication => CSP.StandardRelations.implicationRel
    | ImpXorSymbol.xor => CSP.StandardRelations.xorRel

/-- The intermediate constraint `[¬y]` used to define `[x]` from `[¬y]` and XOR. -/
def pinFalseAuxConstraint : CSP.Constraint pinFalseXorLanguage where
  symbol := PinFalseXorSymbol.pinFalse
  vars := fun _ => 1

/-- The intermediate constraint `x ≠ y` used with a false pin to define `[x]`. -/
def xorFreeAuxConstraintFalse : CSP.Constraint pinFalseXorLanguage where
  symbol := PinFalseXorSymbol.xor
  vars := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1

/-- Over `{[¬x], [x ≠ y]}`, the block `∃y. ¬y ∧ x ≠ y` represents `[x]`. -/
def pinTrueFromPinFalseXorBlock :
    RelationFormula pinFalseXorLanguage CSP.StandardRelations.pinTrueRel.arity where
  constraints := [pinFalseAuxConstraint, xorFreeAuxConstraintFalse]
  notes := "The PP block exists y, pinFalse(y) and xor(x,y)."

theorem pinTrueFromPinFalseXorBlock_represents :
    RepresentsRelation pinFalseXorLanguage CSP.StandardRelations.pinTrueRel
      pinTrueFromPinFalseXorBlock := by
  intro t
  have h0lt : 0 < CSP.StandardRelations.pinTrueRel.arity := by
    rw [CSP.StandardRelations.pinTrueRel_arity]
    decide
  constructor
  · intro ht
    refine ⟨fun _ => false, ?_⟩
    intro c hc
    simp [pinTrueFromPinFalseXorBlock] at hc
    rcases hc with rfl | hc
    · change CSP.StandardRelations.pinFalseRel.Holds
        ((pinFalseAuxConstraint).assignmentTuple
          (extendTupleAssignment t (fun _ => false)))
      have hTuple :
          (pinFalseAuxConstraint).assignmentTuple
              (extendTupleAssignment t (fun _ => false)) =
            BoolTuple.constFalse CSP.StandardRelations.pinFalseRel.arity := by
        funext i
        simp [pinFalseAuxConstraint, CSP.Constraint.assignmentTuple, BoolTuple.constFalse,
          extendTupleAssignment]
      rw [hTuple]
      exact (pinFalseRel_holds_iff _).2 rfl
    · subst c
      change CSP.StandardRelations.xorRel.Holds
        ((xorFreeAuxConstraintFalse).assignmentTuple
          (extendTupleAssignment t (fun _ => false)))
      have ht0 : t ⟨0, h0lt⟩ = true := by
        simpa using (pinTrueRel_holds_iff t).1 ht
      refine (xorRel_holds_iff _).2 ?_
      intro hEq
      have hFalse : t ⟨0, h0lt⟩ = false := by
        simpa [xorFreeAuxConstraintFalse, CSP.Constraint.assignmentTuple,
          extendTupleAssignment] using hEq
      rw [ht0] at hFalse
      cases hFalse
  · rintro ⟨aux, hSat⟩
    have hPin :
        CSP.Constraint.Satisfies pinFalseAuxConstraint (extendTupleAssignment t aux) := by
      exact hSat pinFalseAuxConstraint (by simp [pinTrueFromPinFalseXorBlock])
    have hXor :
        CSP.Constraint.Satisfies xorFreeAuxConstraintFalse (extendTupleAssignment t aux) := by
      exact hSat xorFreeAuxConstraintFalse (by simp [pinTrueFromPinFalseXorBlock])
    change CSP.StandardRelations.pinFalseRel.Holds
      (pinFalseAuxConstraint.assignmentTuple (extendTupleAssignment t aux)) at hPin
    have hAuxFalse : aux 1 = false := by
      have hTuple :
          pinFalseAuxConstraint.assignmentTuple (extendTupleAssignment t aux) =
            fun _ : Fin CSP.StandardRelations.pinFalseRel.arity => aux 1 := by
        funext i
        simp [pinFalseAuxConstraint, CSP.Constraint.assignmentTuple, extendTupleAssignment]
      have hPin' := (pinFalseRel_holds_iff _).1 (by simpa [hTuple] using hPin)
      simpa using hPin'
    change CSP.StandardRelations.xorRel.Holds
      (xorFreeAuxConstraintFalse.assignmentTuple (extendTupleAssignment t aux)) at hXor
    have hNe : t ⟨0, h0lt⟩ ≠ aux 1 := by
      have hTuple :
          xorFreeAuxConstraintFalse.assignmentTuple (extendTupleAssignment t aux) =
            fun
              | ⟨0, _⟩ => t ⟨0, h0lt⟩
              | ⟨1, _⟩ => aux 1 := by
        funext i
        fin_cases i <;>
          simp [xorFreeAuxConstraintFalse, CSP.Constraint.assignmentTuple,
            extendTupleAssignment]
      simpa [hTuple] using (xorRel_holds_iff _).1 hXor
    exact (pinTrueRel_holds_iff t).2 (by
      cases h : t ⟨0, h0lt⟩
      · exact False.elim (hNe (h.trans hAuxFalse.symm))
      · simp)

/-- The intermediate constraint `[y]` used to define `[¬x]` from `[y]` and XOR. -/
def pinTrueAuxConstraint : CSP.Constraint pinTrueXorLanguage where
  symbol := PinTrueXorSymbol.pinTrue
  vars := fun _ => 1

/-- The intermediate constraint `x ≠ y` used with a true pin to define `[¬x]`. -/
def xorFreeAuxConstraintTrue : CSP.Constraint pinTrueXorLanguage where
  symbol := PinTrueXorSymbol.xor
  vars := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1

/-- Over `{[x], [x ≠ y]}`, the block `∃y. y ∧ x ≠ y` represents `[¬x]`. -/
def pinFalseFromPinTrueXorBlock :
    RelationFormula pinTrueXorLanguage CSP.StandardRelations.pinFalseRel.arity where
  constraints := [pinTrueAuxConstraint, xorFreeAuxConstraintTrue]
  notes := "The PP block exists y, pinTrue(y) and xor(x,y)."

theorem pinFalseFromPinTrueXorBlock_represents :
    RepresentsRelation pinTrueXorLanguage CSP.StandardRelations.pinFalseRel
      pinFalseFromPinTrueXorBlock := by
  intro t
  have h0lt : 0 < CSP.StandardRelations.pinFalseRel.arity := by
    rw [CSP.StandardRelations.pinFalseRel_arity]
    decide
  constructor
  · intro ht
    refine ⟨fun _ => true, ?_⟩
    intro c hc
    simp [pinFalseFromPinTrueXorBlock] at hc
    rcases hc with rfl | hc
    · change CSP.StandardRelations.pinTrueRel.Holds
        ((pinTrueAuxConstraint).assignmentTuple
          (extendTupleAssignment t (fun _ => true)))
      have hTuple :
          (pinTrueAuxConstraint).assignmentTuple
              (extendTupleAssignment t (fun _ => true)) =
            BoolTuple.constTrue CSP.StandardRelations.pinTrueRel.arity := by
        funext i
        simp [pinTrueAuxConstraint, CSP.Constraint.assignmentTuple, BoolTuple.constTrue,
          extendTupleAssignment]
      rw [hTuple]
      exact (pinTrueRel_holds_iff _).2 rfl
    · subst c
      change CSP.StandardRelations.xorRel.Holds
        ((xorFreeAuxConstraintTrue).assignmentTuple
          (extendTupleAssignment t (fun _ => true)))
      have ht0 : t ⟨0, h0lt⟩ = false := by
        simpa using (pinFalseRel_holds_iff t).1 ht
      refine (xorRel_holds_iff _).2 ?_
      intro hEq
      have hTrue : t ⟨0, h0lt⟩ = true := by
        simpa [xorFreeAuxConstraintTrue, CSP.Constraint.assignmentTuple,
          extendTupleAssignment] using hEq
      rw [ht0] at hTrue
      cases hTrue
  · rintro ⟨aux, hSat⟩
    have hPin :
        CSP.Constraint.Satisfies pinTrueAuxConstraint (extendTupleAssignment t aux) := by
      exact hSat pinTrueAuxConstraint (by simp [pinFalseFromPinTrueXorBlock])
    have hXor :
        CSP.Constraint.Satisfies xorFreeAuxConstraintTrue (extendTupleAssignment t aux) := by
      exact hSat xorFreeAuxConstraintTrue (by simp [pinFalseFromPinTrueXorBlock])
    change CSP.StandardRelations.pinTrueRel.Holds
      (pinTrueAuxConstraint.assignmentTuple (extendTupleAssignment t aux)) at hPin
    have hAuxTrue : aux 1 = true := by
      have hTuple :
          pinTrueAuxConstraint.assignmentTuple (extendTupleAssignment t aux) =
            fun _ : Fin CSP.StandardRelations.pinTrueRel.arity => aux 1 := by
        funext i
        simp [pinTrueAuxConstraint, CSP.Constraint.assignmentTuple, extendTupleAssignment]
      have hPin' := (pinTrueRel_holds_iff _).1 (by simpa [hTuple] using hPin)
      simpa using hPin'
    change CSP.StandardRelations.xorRel.Holds
      (xorFreeAuxConstraintTrue.assignmentTuple (extendTupleAssignment t aux)) at hXor
    have hNe : t ⟨0, h0lt⟩ ≠ aux 1 := by
      have hTuple :
          xorFreeAuxConstraintTrue.assignmentTuple (extendTupleAssignment t aux) =
            fun
              | ⟨0, _⟩ => t ⟨0, h0lt⟩
              | ⟨1, _⟩ => aux 1 := by
        funext i
        fin_cases i <;>
          simp [xorFreeAuxConstraintTrue, CSP.Constraint.assignmentTuple,
            extendTupleAssignment]
      simpa [hTuple] using (xorRel_holds_iff _).1 hXor
    exact (pinFalseRel_holds_iff t).2 (by
      cases h : t ⟨0, h0lt⟩
      · simp
      · exact False.elim (hNe (h.trans hAuxTrue.symm)))

/-- A `pinFalse + xor` intermediate representation over an arbitrary language. -/
def pinFalseXorLanguageRepresentation {Γ : CSP.BoolLanguage}
    (falseBlock : RelationFormula Γ CSP.StandardRelations.pinFalseRel.arity)
    (falseRepresents : RepresentsRelation Γ CSP.StandardRelations.pinFalseRel falseBlock)
    (xor : XorRepresentationWitness Γ) :
    LanguageRepresentation pinFalseXorLanguage Γ where
  block
    | PinFalseXorSymbol.pinFalse => falseBlock
    | PinFalseXorSymbol.xor => xor.xorBlock
  represents
    | PinFalseXorSymbol.pinFalse => falseRepresents
    | PinFalseXorSymbol.xor => xor.xorRepresents
  notes := "Intermediate representation of pinFalse and XOR."

/-- A `pinTrue + xor` intermediate representation over an arbitrary language. -/
def pinTrueXorLanguageRepresentation {Γ : CSP.BoolLanguage}
    (trueBlock : RelationFormula Γ CSP.StandardRelations.pinTrueRel.arity)
    (trueRepresents : RepresentsRelation Γ CSP.StandardRelations.pinTrueRel trueBlock)
    (xor : XorRepresentationWitness Γ) :
    LanguageRepresentation pinTrueXorLanguage Γ where
  block
    | PinTrueXorSymbol.pinTrue => trueBlock
    | PinTrueXorSymbol.xor => xor.xorBlock
  represents
    | PinTrueXorSymbol.pinTrue => trueRepresents
    | PinTrueXorSymbol.xor => xor.xorRepresents
  notes := "Intermediate representation of pinTrue and XOR."

/-- One false pin plus XOR gives both unary constants. -/
noncomputable def constantsOfPinFalseAndXor {Γ : CSP.BoolLanguage}
    (falseBlock : RelationFormula Γ CSP.StandardRelations.pinFalseRel.arity)
    (falseRepresents : RepresentsRelation Γ CSP.StandardRelations.pinFalseRel falseBlock)
    (xor : XorRepresentationWitness Γ) :
    ConstantRepresentationWitness Γ where
  trueBlock :=
    relationFormulaViaRepresentationComposition
      (pinFalseXorLanguageRepresentation falseBlock falseRepresents xor)
      CSP.StandardRelations.pinTrueRel
      pinTrueFromPinFalseXorBlock
  trueRepresents :=
    relationFormulaViaRepresentationComposition_represents
      (pinFalseXorLanguageRepresentation falseBlock falseRepresents xor)
      CSP.StandardRelations.pinTrueRel
      pinTrueFromPinFalseXorBlock
      pinTrueFromPinFalseXorBlock_represents
  falseBlock := falseBlock
  falseRepresents := falseRepresents
  notes := "A false pin and represented disequality define the true pin."

/-- One true pin plus XOR gives both unary constants. -/
noncomputable def constantsOfPinTrueAndXor {Γ : CSP.BoolLanguage}
    (trueBlock : RelationFormula Γ CSP.StandardRelations.pinTrueRel.arity)
    (trueRepresents : RepresentsRelation Γ CSP.StandardRelations.pinTrueRel trueBlock)
    (xor : XorRepresentationWitness Γ) :
    ConstantRepresentationWitness Γ where
  trueBlock := trueBlock
  trueRepresents := trueRepresents
  falseBlock :=
    relationFormulaViaRepresentationComposition
      (pinTrueXorLanguageRepresentation trueBlock trueRepresents xor)
      CSP.StandardRelations.pinFalseRel
      pinFalseFromPinTrueXorBlock
  falseRepresents :=
    relationFormulaViaRepresentationComposition_represents
      (pinTrueXorLanguageRepresentation trueBlock trueRepresents xor)
      CSP.StandardRelations.pinFalseRel
      pinFalseFromPinTrueXorBlock
      pinFalseFromPinTrueXorBlock_represents
  notes := "A true pin and represented disequality define the false pin."

/-- The intermediate constraint `(y -> x)` for deriving `[x]` from implication and XOR. -/
def implicationAuxFreeConstraint : CSP.Constraint impXorLanguage where
  symbol := ImpXorSymbol.implication
  vars := fun
    | ⟨0, _⟩ => 1
    | ⟨1, _⟩ => 0

/-- The intermediate constraint `y ≠ x` for deriving `[x]` from implication and XOR. -/
def xorAuxFreeConstraint : CSP.Constraint impXorLanguage where
  symbol := ImpXorSymbol.xor
  vars := fun
    | ⟨0, _⟩ => 1
    | ⟨1, _⟩ => 0

/-- Over `{[x -> y], [x ≠ y]}`, the block `∃y. (y -> x) ∧ y ≠ x` represents `[x]`. -/
def pinTrueFromImpXorBlock :
    RelationFormula impXorLanguage CSP.StandardRelations.pinTrueRel.arity where
  constraints := [implicationAuxFreeConstraint, xorAuxFreeConstraint]
  notes := "The PP block exists y, (y -> x) and xor(y,x)."

theorem pinTrueFromImpXorBlock_represents :
    RepresentsRelation impXorLanguage CSP.StandardRelations.pinTrueRel
      pinTrueFromImpXorBlock := by
  intro t
  have h0lt : 0 < CSP.StandardRelations.pinTrueRel.arity := by
    rw [CSP.StandardRelations.pinTrueRel_arity]
    decide
  constructor
  · intro ht
    refine ⟨fun _ => false, ?_⟩
    intro c hc
    simp [pinTrueFromImpXorBlock] at hc
    rcases hc with rfl | hc
    · change CSP.StandardRelations.implicationRel.Holds
        (implicationAuxFreeConstraint.assignmentTuple
          (extendTupleAssignment t (fun _ => false)))
      refine (implicationRel_holds_iff _).2 ?_
      right
      simpa using (pinTrueRel_holds_iff t).1 ht
    · subst c
      change CSP.StandardRelations.xorRel.Holds
        (xorAuxFreeConstraint.assignmentTuple (extendTupleAssignment t (fun _ => false)))
      refine (xorRel_holds_iff _).2 ?_
      intro hEq
      have hFalse : t ⟨0, h0lt⟩ = false := by
        simpa [xorAuxFreeConstraint, CSP.Constraint.assignmentTuple,
          extendTupleAssignment] using hEq.symm
      have ht0 : t ⟨0, h0lt⟩ = true := by
        simpa using (pinTrueRel_holds_iff t).1 ht
      rw [ht0] at hFalse
      cases hFalse
  · rintro ⟨aux, hSat⟩
    have hImp :
        CSP.Constraint.Satisfies implicationAuxFreeConstraint
          (extendTupleAssignment t aux) := by
      exact hSat implicationAuxFreeConstraint (by simp [pinTrueFromImpXorBlock])
    have hXor :
        CSP.Constraint.Satisfies xorAuxFreeConstraint (extendTupleAssignment t aux) := by
      exact hSat xorAuxFreeConstraint (by simp [pinTrueFromImpXorBlock])
    change CSP.StandardRelations.implicationRel.Holds
      (implicationAuxFreeConstraint.assignmentTuple (extendTupleAssignment t aux)) at hImp
    change CSP.StandardRelations.xorRel.Holds
      (xorAuxFreeConstraint.assignmentTuple (extendTupleAssignment t aux)) at hXor
    have hImpSem : aux 1 = false ∨ t ⟨0, h0lt⟩ = true := by
      simpa [implicationAuxFreeConstraint, CSP.Constraint.assignmentTuple,
        extendTupleAssignment] using (implicationRel_holds_iff _).1 hImp
    have hNe : aux 1 ≠ t ⟨0, h0lt⟩ := by
      simpa [xorAuxFreeConstraint, CSP.Constraint.assignmentTuple,
        extendTupleAssignment] using (xorRel_holds_iff _).1 hXor
    exact (pinTrueRel_holds_iff t).2 (by
      rcases hImpSem with hAuxFalse | htTrue
      · cases ht : t ⟨0, h0lt⟩
        · exact False.elim (hNe (hAuxFalse.trans ht.symm))
        · simp
      · exact htTrue)

/-- The intermediate constraint `(x -> y)` for deriving `[¬x]` from implication and XOR. -/
def implicationFreeAuxConstraint : CSP.Constraint impXorLanguage where
  symbol := ImpXorSymbol.implication
  vars := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1

/-- The intermediate constraint `x ≠ y` for deriving `[¬x]` from implication and XOR. -/
def xorFreeAuxConstraintImp : CSP.Constraint impXorLanguage where
  symbol := ImpXorSymbol.xor
  vars := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1

/-- Over `{[x -> y], [x ≠ y]}`, the block `∃y. (x -> y) ∧ x ≠ y` represents `[¬x]`. -/
def pinFalseFromImpXorBlock :
    RelationFormula impXorLanguage CSP.StandardRelations.pinFalseRel.arity where
  constraints := [implicationFreeAuxConstraint, xorFreeAuxConstraintImp]
  notes := "The PP block exists y, (x -> y) and xor(x,y)."

theorem pinFalseFromImpXorBlock_represents :
    RepresentsRelation impXorLanguage CSP.StandardRelations.pinFalseRel
      pinFalseFromImpXorBlock := by
  intro t
  have h0lt : 0 < CSP.StandardRelations.pinFalseRel.arity := by
    rw [CSP.StandardRelations.pinFalseRel_arity]
    decide
  constructor
  · intro ht
    refine ⟨fun _ => true, ?_⟩
    intro c hc
    simp [pinFalseFromImpXorBlock] at hc
    rcases hc with rfl | hc
    · change CSP.StandardRelations.implicationRel.Holds
        (implicationFreeAuxConstraint.assignmentTuple
          (extendTupleAssignment t (fun _ => true)))
      refine (implicationRel_holds_iff _).2 ?_
      right
      rfl
    · subst c
      change CSP.StandardRelations.xorRel.Holds
        (xorFreeAuxConstraintImp.assignmentTuple (extendTupleAssignment t (fun _ => true)))
      refine (xorRel_holds_iff _).2 ?_
      intro hEq
      have hTrue : t ⟨0, h0lt⟩ = true := by
        simpa [xorFreeAuxConstraintImp, CSP.Constraint.assignmentTuple,
          extendTupleAssignment] using hEq
      have ht0 : t ⟨0, h0lt⟩ = false := by
        simpa using (pinFalseRel_holds_iff t).1 ht
      rw [ht0] at hTrue
      cases hTrue
  · rintro ⟨aux, hSat⟩
    have hImp :
        CSP.Constraint.Satisfies implicationFreeAuxConstraint
          (extendTupleAssignment t aux) := by
      exact hSat implicationFreeAuxConstraint (by simp [pinFalseFromImpXorBlock])
    have hXor :
        CSP.Constraint.Satisfies xorFreeAuxConstraintImp (extendTupleAssignment t aux) := by
      exact hSat xorFreeAuxConstraintImp (by simp [pinFalseFromImpXorBlock])
    change CSP.StandardRelations.implicationRel.Holds
      (implicationFreeAuxConstraint.assignmentTuple (extendTupleAssignment t aux)) at hImp
    change CSP.StandardRelations.xorRel.Holds
      (xorFreeAuxConstraintImp.assignmentTuple (extendTupleAssignment t aux)) at hXor
    have hImpSem : t ⟨0, h0lt⟩ = false ∨ aux 1 = true := by
      simpa [implicationFreeAuxConstraint, CSP.Constraint.assignmentTuple,
        extendTupleAssignment] using (implicationRel_holds_iff _).1 hImp
    have hNe : t ⟨0, h0lt⟩ ≠ aux 1 := by
      simpa [xorFreeAuxConstraintImp, CSP.Constraint.assignmentTuple,
        extendTupleAssignment] using (xorRel_holds_iff _).1 hXor
    exact (pinFalseRel_holds_iff t).2 (by
      rcases hImpSem with htFalse | hAuxTrue
      · exact htFalse
      · cases ht : t ⟨0, h0lt⟩
        · simp
        · exact False.elim (hNe (ht.trans hAuxTrue.symm)))

/-- An `implication + xor` intermediate representation over an arbitrary language. -/
def impXorLanguageRepresentation {Γ : CSP.BoolLanguage}
    (impBlock : RelationFormula Γ CSP.StandardRelations.implicationRel.arity)
    (impRepresents : RepresentsRelation Γ CSP.StandardRelations.implicationRel impBlock)
    (xor : XorRepresentationWitness Γ) :
    LanguageRepresentation impXorLanguage Γ where
  block
    | ImpXorSymbol.implication => impBlock
    | ImpXorSymbol.xor => xor.xorBlock
  represents
    | ImpXorSymbol.implication => impRepresents
    | ImpXorSymbol.xor => xor.xorRepresents
  notes := "Intermediate representation of implication and XOR."

/-- A represented implication plus represented XOR gives both unary constants. -/
noncomputable def constantsOfImplicationAndXor {Γ : CSP.BoolLanguage}
    (impBlock : RelationFormula Γ CSP.StandardRelations.implicationRel.arity)
    (impRepresents : RepresentsRelation Γ CSP.StandardRelations.implicationRel impBlock)
    (xor : XorRepresentationWitness Γ) :
    ConstantRepresentationWitness Γ where
  trueBlock :=
    relationFormulaViaRepresentationComposition
      (impXorLanguageRepresentation impBlock impRepresents xor)
      CSP.StandardRelations.pinTrueRel
      pinTrueFromImpXorBlock
  trueRepresents :=
    relationFormulaViaRepresentationComposition_represents
      (impXorLanguageRepresentation impBlock impRepresents xor)
      CSP.StandardRelations.pinTrueRel
      pinTrueFromImpXorBlock
      pinTrueFromImpXorBlock_represents
  falseBlock :=
    relationFormulaViaRepresentationComposition
      (impXorLanguageRepresentation impBlock impRepresents xor)
      CSP.StandardRelations.pinFalseRel
      pinFalseFromImpXorBlock
  falseRepresents :=
    relationFormulaViaRepresentationComposition_represents
      (impXorLanguageRepresentation impBlock impRepresents xor)
      CSP.StandardRelations.pinFalseRel
      pinFalseFromImpXorBlock
      pinFalseFromImpXorBlock_represents
  notes := "Implication and represented disequality define both unary pins."

/-- Substitute the same free variable for every coordinate of a relation symbol. -/
def diagonalConstraint {Γ : CSP.BoolLanguage} (s : Γ.Symbol) (v : Nat) :
    CSP.Constraint Γ where
  symbol := s
  vars := fun _ => v

/-- A unary diagonal block `R(x, ..., x)`. -/
def diagonalUnaryBlock {Γ : CSP.BoolLanguage} (s : Γ.Symbol) :
    RelationFormula Γ 1 where
  constraints := [diagonalConstraint s 0]
  notes := "Unary diagonal block R(x,...,x)."

theorem diagonalUnaryBlock_represents_pinTrue {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    (hOne : IsOneValid (Γ.relationOf s)) (hNotZero : ¬ IsZeroValid (Γ.relationOf s)) :
    RepresentsRelation Γ CSP.StandardRelations.pinTrueRel (diagonalUnaryBlock s) := by
  intro t
  constructor
  · intro ht
    refine ⟨fun _ => false, ?_⟩
    intro c hc
    have hcEq : c = diagonalConstraint s 0 := by
      simpa [diagonalUnaryBlock] using hc
    subst c
    have htVal : t ⟨0, by decide⟩ = true := (pinTrueRel_holds_iff t).1 ht
    have h0lt : 0 < CSP.StandardRelations.pinTrueRel.arity := by
      rw [CSP.StandardRelations.pinTrueRel_arity]
      decide
    have ht0 : t ⟨0, h0lt⟩ = true := by
      simpa using htVal
    have hTuple :
        (diagonalConstraint s 0).assignmentTuple
            (extendTupleAssignment t (fun _ => false)) =
          BoolTuple.constTrue (Γ.relationOf s).arity := by
      funext i
      change extendTupleAssignment t (fun _ => false) 0 = true
      simpa [extendTupleAssignment, h0lt] using ht0
    change (Γ.relationOf s).Holds
      ((diagonalConstraint s 0).assignmentTuple (extendTupleAssignment t (fun _ => false)))
    rw [hTuple]
    exact hOne
  · rintro ⟨aux, hSat⟩
    by_cases htVal : t ⟨0, by decide⟩ = true
    · exact (pinTrueRel_holds_iff t).2 htVal
    · have htFalse : t ⟨0, by decide⟩ = false := by
        cases h : t ⟨0, by decide⟩
        · rfl
        · exact False.elim (htVal h)
      have h0lt : 0 < CSP.StandardRelations.pinTrueRel.arity := by
        rw [CSP.StandardRelations.pinTrueRel_arity]
        decide
      have ht0 : t ⟨0, h0lt⟩ = false := by
        simpa using htFalse
      have hConstraint :
          CSP.Constraint.Satisfies (diagonalConstraint s 0) (extendTupleAssignment t aux) := by
        exact hSat (diagonalConstraint s 0) (by simp [diagonalUnaryBlock])
      have hTuple :
          (diagonalConstraint s 0).assignmentTuple (extendTupleAssignment t aux) =
            BoolTuple.constFalse (Γ.relationOf s).arity := by
        funext i
        change extendTupleAssignment t aux 0 = false
        simpa [extendTupleAssignment, h0lt] using ht0
      change (Γ.relationOf s).Holds
        ((diagonalConstraint s 0).assignmentTuple (extendTupleAssignment t aux)) at hConstraint
      rw [hTuple] at hConstraint
      exact False.elim (hNotZero hConstraint)

theorem diagonalUnaryBlock_represents_pinFalse {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    (hZero : IsZeroValid (Γ.relationOf s)) (hNotOne : ¬ IsOneValid (Γ.relationOf s)) :
    RepresentsRelation Γ CSP.StandardRelations.pinFalseRel (diagonalUnaryBlock s) := by
  intro t
  constructor
  · intro ht
    refine ⟨fun _ => false, ?_⟩
    intro c hc
    have hcEq : c = diagonalConstraint s 0 := by
      simpa [diagonalUnaryBlock] using hc
    subst c
    have htVal : t ⟨0, by decide⟩ = false := (pinFalseRel_holds_iff t).1 ht
    have h0lt : 0 < CSP.StandardRelations.pinFalseRel.arity := by
      rw [CSP.StandardRelations.pinFalseRel_arity]
      decide
    have ht0 : t ⟨0, h0lt⟩ = false := by
      simpa using htVal
    have hTuple :
        (diagonalConstraint s 0).assignmentTuple
            (extendTupleAssignment t (fun _ => false)) =
          BoolTuple.constFalse (Γ.relationOf s).arity := by
      funext i
      change extendTupleAssignment t (fun _ => false) 0 = false
      simpa [extendTupleAssignment, h0lt] using ht0
    change (Γ.relationOf s).Holds
      ((diagonalConstraint s 0).assignmentTuple (extendTupleAssignment t (fun _ => false)))
    rw [hTuple]
    exact hZero
  · rintro ⟨aux, hSat⟩
    by_cases htVal : t ⟨0, by decide⟩ = false
    · exact (pinFalseRel_holds_iff t).2 htVal
    · have htTrue : t ⟨0, by decide⟩ = true := by
        cases h : t ⟨0, by decide⟩
        · exact False.elim (htVal h)
        · rfl
      have h0lt : 0 < CSP.StandardRelations.pinFalseRel.arity := by
        rw [CSP.StandardRelations.pinFalseRel_arity]
        decide
      have ht0 : t ⟨0, h0lt⟩ = true := by
        simpa using htTrue
      have hConstraint :
          CSP.Constraint.Satisfies (diagonalConstraint s 0) (extendTupleAssignment t aux) := by
        exact hSat (diagonalConstraint s 0) (by simp [diagonalUnaryBlock])
      have hTuple :
          (diagonalConstraint s 0).assignmentTuple (extendTupleAssignment t aux) =
            BoolTuple.constTrue (Γ.relationOf s).arity := by
        funext i
        change extendTupleAssignment t aux 0 = true
        simpa [extendTupleAssignment, h0lt] using ht0
      change (Γ.relationOf s).Holds
        ((diagonalConstraint s 0).assignmentTuple (extendTupleAssignment t aux)) at hConstraint
      rw [hTuple] at hConstraint
      exact False.elim (hNotOne hConstraint)

/--
If every relation is either zero-valid or one-valid, the two hard failures pick
one one-valid/not-zero relation and one zero-valid/not-one relation, hence both
constants are represented by diagonal substitution.
-/
noncomputable def constantRepresentationOfAllZeroOrOne {Γ : CSP.BoolLanguage}
    (hHard : HardCaseAssumptions Γ)
    (hAllEither : ∀ s : Γ.Symbol,
      IsZeroValid (Γ.relationOf s) ∨ IsOneValid (Γ.relationOf s)) :
    ConstantRepresentationWitness Γ := by
  classical
  let sTrue := Classical.choose (HardCaseAssumptions.exists_not_zero_valid hHard)
  have hNotZero : ¬ IsZeroValid (Γ.relationOf sTrue) :=
    Classical.choose_spec (HardCaseAssumptions.exists_not_zero_valid hHard)
  let sFalse := Classical.choose (HardCaseAssumptions.exists_not_one_valid hHard)
  have hNotOne : ¬ IsOneValid (Γ.relationOf sFalse) :=
    Classical.choose_spec (HardCaseAssumptions.exists_not_one_valid hHard)
  have hOne : IsOneValid (Γ.relationOf sTrue) := by
    rcases hAllEither sTrue with hZero | hOne
    · exact False.elim (hNotZero hZero)
    · exact hOne
  have hZero : IsZeroValid (Γ.relationOf sFalse) := by
    rcases hAllEither sFalse with hZero | hOne
    · exact hZero
    · exact False.elim (hNotOne hOne)
  exact
    { trueBlock := diagonalUnaryBlock sTrue
      trueRepresents := diagonalUnaryBlock_represents_pinTrue hOne hNotZero
      falseBlock := diagonalUnaryBlock sFalse
      falseRepresents := diagonalUnaryBlock_represents_pinFalse hZero hNotOne
      notes :=
        "Lemma 4.3 case 1: diagonal substitutions through zero/one-validity failures." }

/-- The binary projection used in Lemma 4.3 case 2. -/
def binaryProjectionConstraint {Γ : CSP.BoolLanguage} (s : Γ.Symbol)
    (w : CSP.BoolTuple (Γ.relationOf s).arity) : CSP.Constraint Γ where
  symbol := s
  vars := fun i => if w i then 1 else 0

/-- Binary block `B(x0,x1)` obtained by substituting `x0` on zero coordinates and `x1` on ones. -/
def binaryProjectionBlock {Γ : CSP.BoolLanguage} (s : Γ.Symbol)
    (w : CSP.BoolTuple (Γ.relationOf s).arity) : RelationFormula Γ 2 where
  constraints := [binaryProjectionConstraint s w]
  notes := "Lemma 4.3 binary projection block."

/-- Unary projection of the singleton `(0,1)` block to the false coordinate. -/
def projectionPinFalseBlock {Γ : CSP.BoolLanguage} (s : Γ.Symbol)
    (w : CSP.BoolTuple (Γ.relationOf s).arity) : RelationFormula Γ 1 where
  constraints := [binaryProjectionConstraint s w]
  notes := "Projection of singleton binary block to pin false."

/-- Unary projection of the singleton `(0,1)` block to the true coordinate. -/
def projectionPinTrueConstraint {Γ : CSP.BoolLanguage} (s : Γ.Symbol)
    (w : CSP.BoolTuple (Γ.relationOf s).arity) : CSP.Constraint Γ where
  symbol := s
  vars := fun i => if w i then 0 else 1

def projectionPinTrueBlock {Γ : CSP.BoolLanguage} (s : Γ.Symbol)
    (w : CSP.BoolTuple (Γ.relationOf s).arity) : RelationFormula Γ 1 where
  constraints := [projectionPinTrueConstraint s w]
  notes := "Projection of singleton binary block to pin true."

theorem binaryProjectionConstraint_tuple_w {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    (w : CSP.BoolTuple (Γ.relationOf s).arity) {a : SAT.Assignment}
    (h0 : a 0 = false) (h1 : a 1 = true) :
    (binaryProjectionConstraint s w).assignmentTuple a = w := by
  funext i
  by_cases hw : w i
  · simp [binaryProjectionConstraint, CSP.Constraint.assignmentTuple, hw, h1]
  · have hwi : w i = false := by
      cases h : w i
      · rfl
      · exact False.elim (hw h)
    simp [binaryProjectionConstraint, CSP.Constraint.assignmentTuple, hw, h0]

theorem binaryProjectionConstraint_tuple_complement {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    (w : CSP.BoolTuple (Γ.relationOf s).arity) {a : SAT.Assignment}
    (h0 : a 0 = true) (h1 : a 1 = false) :
    (binaryProjectionConstraint s w).assignmentTuple a = BoolTuple.complement w := by
  funext i
  by_cases hw : w i
  · simp [binaryProjectionConstraint, CSP.Constraint.assignmentTuple, BoolTuple.complement,
      hw, h1]
  · have hwi : w i = false := by
      cases h : w i
      · rfl
      · exact False.elim (hw h)
    simp [binaryProjectionConstraint, CSP.Constraint.assignmentTuple, BoolTuple.complement,
      hw, h0]

theorem binaryProjectionConstraint_tuple_constFalse {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    (w : CSP.BoolTuple (Γ.relationOf s).arity) {a : SAT.Assignment}
    (h0 : a 0 = false) (h1 : a 1 = false) :
    (binaryProjectionConstraint s w).assignmentTuple a =
      BoolTuple.constFalse (Γ.relationOf s).arity := by
  funext i
  by_cases hw : w i <;>
    simp [binaryProjectionConstraint, CSP.Constraint.assignmentTuple, BoolTuple.constFalse,
      hw, h0, h1]

theorem binaryProjectionConstraint_tuple_constTrue {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    (w : CSP.BoolTuple (Γ.relationOf s).arity) {a : SAT.Assignment}
    (h0 : a 0 = true) (h1 : a 1 = true) :
    (binaryProjectionConstraint s w).assignmentTuple a =
      BoolTuple.constTrue (Γ.relationOf s).arity := by
  funext i
  by_cases hw : w i <;>
    simp [binaryProjectionConstraint, CSP.Constraint.assignmentTuple, BoolTuple.constTrue,
      hw, h0, h1]

end Hardness
end Schaefer
end ComplexityReduction
