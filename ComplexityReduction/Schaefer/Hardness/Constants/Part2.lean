import ComplexityReduction.Schaefer.Hardness.Constants.Part1

namespace ComplexityReduction
namespace Schaefer
namespace Hardness

theorem projectionPinTrueConstraint_tuple_w {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    (w : CSP.BoolTuple (Γ.relationOf s).arity) {a : SAT.Assignment}
    (h0 : a 0 = true) (h1 : a 1 = false) :
    (projectionPinTrueConstraint s w).assignmentTuple a = w := by
  funext i
  by_cases hw : w i
  · simp [projectionPinTrueConstraint, CSP.Constraint.assignmentTuple, hw, h0]
  · have hwi : w i = false := by
      cases h : w i
      · rfl
      · exact False.elim (hw h)
    simp [projectionPinTrueConstraint, CSP.Constraint.assignmentTuple, hw, h1]

theorem projectionPinTrueConstraint_tuple_constFalse {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    (w : CSP.BoolTuple (Γ.relationOf s).arity) {a : SAT.Assignment}
    (h0 : a 0 = false) (h1 : a 1 = false) :
    (projectionPinTrueConstraint s w).assignmentTuple a =
      BoolTuple.constFalse (Γ.relationOf s).arity := by
  funext i
  by_cases hw : w i <;>
    simp [projectionPinTrueConstraint, CSP.Constraint.assignmentTuple, BoolTuple.constFalse,
      hw, h0, h1]

theorem projectionPinTrueConstraint_tuple_complement {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    (w : CSP.BoolTuple (Γ.relationOf s).arity) {a : SAT.Assignment}
    (h0 : a 0 = false) (h1 : a 1 = true) :
    (projectionPinTrueConstraint s w).assignmentTuple a = BoolTuple.complement w := by
  funext i
  by_cases hw : w i
  · simp [projectionPinTrueConstraint, CSP.Constraint.assignmentTuple, BoolTuple.complement,
      hw, h0]
  · have hwi : w i = false := by
      cases h : w i
      · rfl
      · exact False.elim (hw h)
    simp [projectionPinTrueConstraint, CSP.Constraint.assignmentTuple, BoolTuple.complement,
      hw, h1]

theorem binaryProjectionBlock_represents_xor {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    {w : CSP.BoolTuple (Γ.relationOf s).arity}
    (hW : (Γ.relationOf s).Holds w)
    (hNotZero : ¬ IsZeroValid (Γ.relationOf s))
    (hNotOne : ¬ IsOneValid (Γ.relationOf s))
    (hComp : (Γ.relationOf s).Holds (BoolTuple.complement w)) :
    RepresentsRelation Γ CSP.StandardRelations.xorRel (binaryProjectionBlock s w) := by
  intro t
  have h0lt : 0 < CSP.StandardRelations.xorRel.arity := by
    rw [CSP.StandardRelations.xorRel_arity]
    decide
  have h1lt : 1 < CSP.StandardRelations.xorRel.arity := by
    rw [CSP.StandardRelations.xorRel_arity]
    decide
  constructor
  · intro ht
    have hneq : t ⟨0, h0lt⟩ ≠ t ⟨1, h1lt⟩ := by
      simpa using (xorRel_holds_iff t).1 ht
    refine ⟨fun _ => false, ?_⟩
    intro c hc
    have hcEq : c = binaryProjectionConstraint s w := by
      simpa [binaryProjectionBlock] using hc
    subst c
    cases h0 : t ⟨0, h0lt⟩ <;> cases h1 : t ⟨1, h1lt⟩
    · exact False.elim (hneq (by rw [h0, h1]))
    · have hTuple :
          (binaryProjectionConstraint s w).assignmentTuple
              (extendTupleAssignment t (fun _ => false)) = w := by
        have hVar0 : extendTupleAssignment t (fun _ => false) 0 = false := by
          simpa [extendTupleAssignment, h0lt] using h0
        have hVar1 : extendTupleAssignment t (fun _ => false) 1 = true := by
          simpa [extendTupleAssignment, h1lt] using h1
        exact binaryProjectionConstraint_tuple_w w hVar0 hVar1
      change (Γ.relationOf s).Holds
        ((binaryProjectionConstraint s w).assignmentTuple
          (extendTupleAssignment t (fun _ => false)))
      rw [hTuple]
      exact hW
    · have hTuple :
          (binaryProjectionConstraint s w).assignmentTuple
              (extendTupleAssignment t (fun _ => false)) =
            BoolTuple.complement w := by
        have hVar0 : extendTupleAssignment t (fun _ => false) 0 = true := by
          simpa [extendTupleAssignment, h0lt] using h0
        have hVar1 : extendTupleAssignment t (fun _ => false) 1 = false := by
          simpa [extendTupleAssignment, h1lt] using h1
        exact binaryProjectionConstraint_tuple_complement w hVar0 hVar1
      change (Γ.relationOf s).Holds
        ((binaryProjectionConstraint s w).assignmentTuple
          (extendTupleAssignment t (fun _ => false)))
      rw [hTuple]
      exact hComp
    · exact False.elim (hneq (by rw [h0, h1]))
  · rintro ⟨aux, hSat⟩
    have hConstraint :
        CSP.Constraint.Satisfies (binaryProjectionConstraint s w)
          (extendTupleAssignment t aux) := by
      exact hSat (binaryProjectionConstraint s w) (by simp [binaryProjectionBlock])
    cases h0 : t ⟨0, h0lt⟩ <;> cases h1 : t ⟨1, h1lt⟩
    · have hTuple :
          (binaryProjectionConstraint s w).assignmentTuple (extendTupleAssignment t aux) =
            BoolTuple.constFalse (Γ.relationOf s).arity := by
        have hVar0 : extendTupleAssignment t aux 0 = false := by
          simpa [extendTupleAssignment, h0lt] using h0
        have hVar1 : extendTupleAssignment t aux 1 = false := by
          simpa [extendTupleAssignment, h1lt] using h1
        exact binaryProjectionConstraint_tuple_constFalse w hVar0 hVar1
      change (Γ.relationOf s).Holds
        ((binaryProjectionConstraint s w).assignmentTuple (extendTupleAssignment t aux))
        at hConstraint
      rw [hTuple] at hConstraint
      exact False.elim (hNotZero hConstraint)
    · exact (xorRel_holds_iff t).2 (by
        intro hEq
        have hEq' : t ⟨0, h0lt⟩ = t ⟨1, h1lt⟩ := by simpa using hEq
        rw [h0, h1] at hEq'
        cases hEq')
    · exact (xorRel_holds_iff t).2 (by
        intro hEq
        have hEq' : t ⟨0, h0lt⟩ = t ⟨1, h1lt⟩ := by simpa using hEq
        rw [h0, h1] at hEq'
        cases hEq')
    · have hTuple :
          (binaryProjectionConstraint s w).assignmentTuple (extendTupleAssignment t aux) =
            BoolTuple.constTrue (Γ.relationOf s).arity := by
        have hVar0 : extendTupleAssignment t aux 0 = true := by
          simpa [extendTupleAssignment, h0lt] using h0
        have hVar1 : extendTupleAssignment t aux 1 = true := by
          simpa [extendTupleAssignment, h1lt] using h1
        exact binaryProjectionConstraint_tuple_constTrue w hVar0 hVar1
      change (Γ.relationOf s).Holds
        ((binaryProjectionConstraint s w).assignmentTuple (extendTupleAssignment t aux))
        at hConstraint
      rw [hTuple] at hConstraint
      exact False.elim (hNotOne hConstraint)

theorem binaryProjectionBlock_represents_implication {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    {w : CSP.BoolTuple (Γ.relationOf s).arity}
    (hW : (Γ.relationOf s).Holds w)
    (hZero : IsZeroValid (Γ.relationOf s))
    (hOne : IsOneValid (Γ.relationOf s))
    (hNotComp : ¬ (Γ.relationOf s).Holds (BoolTuple.complement w)) :
    RepresentsRelation Γ CSP.StandardRelations.implicationRel (binaryProjectionBlock s w) := by
  intro t
  have h0lt : 0 < CSP.StandardRelations.implicationRel.arity := by
    rw [CSP.StandardRelations.implicationRel_arity]
    decide
  have h1lt : 1 < CSP.StandardRelations.implicationRel.arity := by
    rw [CSP.StandardRelations.implicationRel_arity]
    decide
  constructor
  · intro ht
    have hImp : t ⟨0, h0lt⟩ = false ∨ t ⟨1, h1lt⟩ = true := by
      simpa using (implicationRel_holds_iff t).1 ht
    refine ⟨fun _ => false, ?_⟩
    intro c hc
    have hcEq : c = binaryProjectionConstraint s w := by
      simpa [binaryProjectionBlock] using hc
    subst c
    cases h0 : t ⟨0, h0lt⟩ <;> cases h1 : t ⟨1, h1lt⟩
    · have hTuple :
          (binaryProjectionConstraint s w).assignmentTuple
              (extendTupleAssignment t (fun _ => false)) =
            BoolTuple.constFalse (Γ.relationOf s).arity := by
        have hVar0 : extendTupleAssignment t (fun _ => false) 0 = false := by
          simpa [extendTupleAssignment, h0lt] using h0
        have hVar1 : extendTupleAssignment t (fun _ => false) 1 = false := by
          simpa [extendTupleAssignment, h1lt] using h1
        exact binaryProjectionConstraint_tuple_constFalse w hVar0 hVar1
      change (Γ.relationOf s).Holds
        ((binaryProjectionConstraint s w).assignmentTuple
          (extendTupleAssignment t (fun _ => false)))
      rw [hTuple]
      exact hZero
    · have hTuple :
          (binaryProjectionConstraint s w).assignmentTuple
              (extendTupleAssignment t (fun _ => false)) = w := by
        have hVar0 : extendTupleAssignment t (fun _ => false) 0 = false := by
          simpa [extendTupleAssignment, h0lt] using h0
        have hVar1 : extendTupleAssignment t (fun _ => false) 1 = true := by
          simpa [extendTupleAssignment, h1lt] using h1
        exact binaryProjectionConstraint_tuple_w w hVar0 hVar1
      change (Γ.relationOf s).Holds
        ((binaryProjectionConstraint s w).assignmentTuple
          (extendTupleAssignment t (fun _ => false)))
      rw [hTuple]
      exact hW
    · rcases hImp with hImp | hImp
      · rw [h0] at hImp
        cases hImp
      · rw [h1] at hImp
        cases hImp
    · have hTuple :
          (binaryProjectionConstraint s w).assignmentTuple
              (extendTupleAssignment t (fun _ => false)) =
            BoolTuple.constTrue (Γ.relationOf s).arity := by
        have hVar0 : extendTupleAssignment t (fun _ => false) 0 = true := by
          simpa [extendTupleAssignment, h0lt] using h0
        have hVar1 : extendTupleAssignment t (fun _ => false) 1 = true := by
          simpa [extendTupleAssignment, h1lt] using h1
        exact binaryProjectionConstraint_tuple_constTrue w hVar0 hVar1
      change (Γ.relationOf s).Holds
        ((binaryProjectionConstraint s w).assignmentTuple
          (extendTupleAssignment t (fun _ => false)))
      rw [hTuple]
      exact hOne
  · rintro ⟨aux, hSat⟩
    have hConstraint :
        CSP.Constraint.Satisfies (binaryProjectionConstraint s w)
          (extendTupleAssignment t aux) := by
      exact hSat (binaryProjectionConstraint s w) (by simp [binaryProjectionBlock])
    cases h0 : t ⟨0, h0lt⟩ <;> cases h1 : t ⟨1, h1lt⟩
    · exact (implicationRel_holds_iff t).2 (Or.inl (by simpa using h0))
    · exact (implicationRel_holds_iff t).2 (Or.inl (by simpa using h0))
    · have hTuple :
          (binaryProjectionConstraint s w).assignmentTuple (extendTupleAssignment t aux) =
            BoolTuple.complement w := by
        have hVar0 : extendTupleAssignment t aux 0 = true := by
          simpa [extendTupleAssignment, h0lt] using h0
        have hVar1 : extendTupleAssignment t aux 1 = false := by
          simpa [extendTupleAssignment, h1lt] using h1
        exact binaryProjectionConstraint_tuple_complement w hVar0 hVar1
      change (Γ.relationOf s).Holds
        ((binaryProjectionConstraint s w).assignmentTuple (extendTupleAssignment t aux))
        at hConstraint
      rw [hTuple] at hConstraint
      exact False.elim (hNotComp hConstraint)
    · exact (implicationRel_holds_iff t).2 (Or.inr (by simpa using h1))

theorem projectionPinFalseBlock_represents {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    {w : CSP.BoolTuple (Γ.relationOf s).arity}
    (hW : (Γ.relationOf s).Holds w)
    (hNotOne : ¬ IsOneValid (Γ.relationOf s))
    (hNotComp : ¬ (Γ.relationOf s).Holds (BoolTuple.complement w)) :
    RepresentsRelation Γ CSP.StandardRelations.pinFalseRel (projectionPinFalseBlock s w) := by
  intro t
  have h0lt : 0 < CSP.StandardRelations.pinFalseRel.arity := by
    rw [CSP.StandardRelations.pinFalseRel_arity]
    decide
  constructor
  · intro ht
    have ht0 : t ⟨0, h0lt⟩ = false := by
      simpa using (pinFalseRel_holds_iff t).1 ht
    refine ⟨fun _ => true, ?_⟩
    intro c hc
    have hcEq : c = binaryProjectionConstraint s w := by
      simpa [projectionPinFalseBlock] using hc
    subst c
    have hTuple :
        (binaryProjectionConstraint s w).assignmentTuple
            (extendTupleAssignment t (fun _ => true)) = w := by
      have hVar0 : extendTupleAssignment t (fun _ => true) 0 = false := by
        simpa [extendTupleAssignment, h0lt] using ht0
      have hNot : ¬ 1 < CSP.StandardRelations.pinFalseRel.arity := by
        rw [CSP.StandardRelations.pinFalseRel_arity]
        decide
      have hVar1 : extendTupleAssignment t (fun _ => true) 1 = true := by
        simp [extendTupleAssignment]
      exact binaryProjectionConstraint_tuple_w w hVar0 hVar1
    change (Γ.relationOf s).Holds
      ((binaryProjectionConstraint s w).assignmentTuple
        (extendTupleAssignment t (fun _ => true)))
    rw [hTuple]
    exact hW
  · rintro ⟨aux, hSat⟩
    by_cases ht0Raw : t ⟨0, h0lt⟩ = false
    · exact (pinFalseRel_holds_iff t).2 (by simpa using ht0Raw)
    · have ht0 : t ⟨0, h0lt⟩ = true := by
        cases h : t ⟨0, h0lt⟩
        · exact False.elim (ht0Raw h)
        · rfl
      have hConstraint :
          CSP.Constraint.Satisfies (binaryProjectionConstraint s w)
            (extendTupleAssignment t aux) := by
        exact hSat (binaryProjectionConstraint s w) (by simp [projectionPinFalseBlock])
      cases hAux : aux 1
      · have hTuple :
            (binaryProjectionConstraint s w).assignmentTuple (extendTupleAssignment t aux) =
              BoolTuple.complement w := by
          have hVar0 : extendTupleAssignment t aux 0 = true := by
            simpa [extendTupleAssignment, h0lt] using ht0
          have hNot : ¬ 1 < CSP.StandardRelations.pinFalseRel.arity := by
            rw [CSP.StandardRelations.pinFalseRel_arity]
            decide
          have hVar1 : extendTupleAssignment t aux 1 = false := by
            simp [extendTupleAssignment, hAux]
          exact binaryProjectionConstraint_tuple_complement w hVar0 hVar1
        change (Γ.relationOf s).Holds
          ((binaryProjectionConstraint s w).assignmentTuple (extendTupleAssignment t aux))
          at hConstraint
        rw [hTuple] at hConstraint
        exact False.elim (hNotComp hConstraint)
      · have hTuple :
            (binaryProjectionConstraint s w).assignmentTuple (extendTupleAssignment t aux) =
              BoolTuple.constTrue (Γ.relationOf s).arity := by
          have hVar0 : extendTupleAssignment t aux 0 = true := by
            simpa [extendTupleAssignment, h0lt] using ht0
          have hNot : ¬ 1 < CSP.StandardRelations.pinFalseRel.arity := by
            rw [CSP.StandardRelations.pinFalseRel_arity]
            decide
          have hVar1 : extendTupleAssignment t aux 1 = true := by
            simp [extendTupleAssignment, hAux]
          exact binaryProjectionConstraint_tuple_constTrue w hVar0 hVar1
        change (Γ.relationOf s).Holds
          ((binaryProjectionConstraint s w).assignmentTuple (extendTupleAssignment t aux))
          at hConstraint
        rw [hTuple] at hConstraint
        exact False.elim (hNotOne hConstraint)

theorem projectionPinTrueBlock_represents {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    {w : CSP.BoolTuple (Γ.relationOf s).arity}
    (hW : (Γ.relationOf s).Holds w)
    (hNotZero : ¬ IsZeroValid (Γ.relationOf s))
    (hNotComp : ¬ (Γ.relationOf s).Holds (BoolTuple.complement w)) :
    RepresentsRelation Γ CSP.StandardRelations.pinTrueRel (projectionPinTrueBlock s w) := by
  intro t
  have h0lt : 0 < CSP.StandardRelations.pinTrueRel.arity := by
    rw [CSP.StandardRelations.pinTrueRel_arity]
    decide
  constructor
  · intro ht
    have ht0 : t ⟨0, h0lt⟩ = true := by
      simpa using (pinTrueRel_holds_iff t).1 ht
    refine ⟨fun _ => false, ?_⟩
    intro c hc
    have hcEq : c = projectionPinTrueConstraint s w := by
      simpa [projectionPinTrueBlock] using hc
    subst c
    have hTuple :
        (projectionPinTrueConstraint s w).assignmentTuple
            (extendTupleAssignment t (fun _ => false)) = w := by
      have hVar0 : extendTupleAssignment t (fun _ => false) 0 = true := by
        simpa [extendTupleAssignment, h0lt] using ht0
      have hNot : ¬ 1 < CSP.StandardRelations.pinTrueRel.arity := by
        rw [CSP.StandardRelations.pinTrueRel_arity]
        decide
      have hVar1 : extendTupleAssignment t (fun _ => false) 1 = false := by
        simp [extendTupleAssignment]
      exact projectionPinTrueConstraint_tuple_w w hVar0 hVar1
    change (Γ.relationOf s).Holds
      ((projectionPinTrueConstraint s w).assignmentTuple
        (extendTupleAssignment t (fun _ => false)))
    rw [hTuple]
    exact hW
  · rintro ⟨aux, hSat⟩
    by_cases ht0Raw : t ⟨0, h0lt⟩ = true
    · exact (pinTrueRel_holds_iff t).2 (by simpa using ht0Raw)
    · have ht0 : t ⟨0, h0lt⟩ = false := by
        cases h : t ⟨0, h0lt⟩
        · rfl
        · exact False.elim (ht0Raw h)
      have hConstraint :
          CSP.Constraint.Satisfies (projectionPinTrueConstraint s w)
            (extendTupleAssignment t aux) := by
        exact hSat (projectionPinTrueConstraint s w) (by simp [projectionPinTrueBlock])
      cases hAux : aux 1
      · have hTuple :
            (projectionPinTrueConstraint s w).assignmentTuple (extendTupleAssignment t aux) =
              BoolTuple.constFalse (Γ.relationOf s).arity := by
          have hVar0 : extendTupleAssignment t aux 0 = false := by
            simpa [extendTupleAssignment, h0lt] using ht0
          have hNot : ¬ 1 < CSP.StandardRelations.pinTrueRel.arity := by
            rw [CSP.StandardRelations.pinTrueRel_arity]
            decide
          have hVar1 : extendTupleAssignment t aux 1 = false := by
            simp [extendTupleAssignment, hAux]
          exact projectionPinTrueConstraint_tuple_constFalse w hVar0 hVar1
        change (Γ.relationOf s).Holds
          ((projectionPinTrueConstraint s w).assignmentTuple (extendTupleAssignment t aux))
          at hConstraint
        rw [hTuple] at hConstraint
        exact False.elim (hNotZero hConstraint)
      · have hTuple :
            (projectionPinTrueConstraint s w).assignmentTuple (extendTupleAssignment t aux) =
              BoolTuple.complement w := by
          have hVar0 : extendTupleAssignment t aux 0 = false := by
            simpa [extendTupleAssignment, h0lt] using ht0
          have hNot : ¬ 1 < CSP.StandardRelations.pinTrueRel.arity := by
            rw [CSP.StandardRelations.pinTrueRel_arity]
            decide
          have hVar1 : extendTupleAssignment t aux 1 = true := by
            simp [extendTupleAssignment, hAux]
          exact projectionPinTrueConstraint_tuple_complement w hVar0 hVar1
        change (Γ.relationOf s).Holds
          ((projectionPinTrueConstraint s w).assignmentTuple (extendTupleAssignment t aux))
          at hConstraint
        rw [hTuple] at hConstraint
        exact False.elim (hNotComp hConstraint)

/-- A singleton `(0,1)` binary projection gives both unary constants. -/
def constantsOfSingletonProjection {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    {w : CSP.BoolTuple (Γ.relationOf s).arity}
    (hW : (Γ.relationOf s).Holds w)
    (hNotZero : ¬ IsZeroValid (Γ.relationOf s))
    (hNotOne : ¬ IsOneValid (Γ.relationOf s))
    (hNotComp : ¬ (Γ.relationOf s).Holds (BoolTuple.complement w)) :
    ConstantRepresentationWitness Γ where
  trueBlock := projectionPinTrueBlock s w
  trueRepresents := projectionPinTrueBlock_represents hW hNotZero hNotComp
  falseBlock := projectionPinFalseBlock s w
  falseRepresents := projectionPinFalseBlock_represents hW hNotOne hNotComp
  notes := "Lemma 4.3 case 2 singleton projection gives both constants."

/-- A non-complementive tuple and represented XOR force both unary constants. -/
noncomputable def constantsOfNonComplementiveWithXor {Γ : CSP.BoolLanguage} {s : Γ.Symbol}
    {w : CSP.BoolTuple (Γ.relationOf s).arity}
    (xor : XorRepresentationWitness Γ)
    (hW : (Γ.relationOf s).Holds w)
    (hNotComp : ¬ (Γ.relationOf s).Holds (BoolTuple.complement w)) :
    ConstantRepresentationWitness Γ := by
  classical
  by_cases hZero : IsZeroValid (Γ.relationOf s)
  · by_cases hOne : IsOneValid (Γ.relationOf s)
    · exact
        constantsOfImplicationAndXor
          (binaryProjectionBlock s w)
          (binaryProjectionBlock_represents_implication hW hZero hOne hNotComp)
          xor
    · exact
        constantsOfPinFalseAndXor
          (projectionPinFalseBlock s w)
          (projectionPinFalseBlock_represents hW hOne hNotComp)
          xor
  · by_cases hOne : IsOneValid (Γ.relationOf s)
    · exact
        constantsOfPinTrueAndXor
          (projectionPinTrueBlock s w)
          (projectionPinTrueBlock_represents hW hZero hNotComp)
          xor
    · exact constantsOfSingletonProjection hW hZero hOne hNotComp

/-- Failure of complementivity provides a tuple whose complement is rejected. -/
theorem exists_noncomplementive_failure {R : CSP.BoolRel} (h : ¬ IsComplementive R) :
    ∃ w : CSP.BoolTuple R.arity, R.Holds w ∧ ¬ R.Holds (BoolTuple.complement w) := by
  classical
  by_contra hNo
  apply h
  intro w hw
  by_contra hComp
  exact hNo ⟨w, hw, hComp⟩

/-- Case 2 of Lemma 4.3 for one fixed nonempty relation rejecting both all-false and all-true. -/
noncomputable def constantOrXorWitnessOfNeitherZeroNorOne {Γ : CSP.BoolLanguage}
    {s : Γ.Symbol}
    (hNonempty : (Γ.relationOf s).Nonempty)
    (hNotZero : ¬ IsZeroValid (Γ.relationOf s))
    (hNotOne : ¬ IsOneValid (Γ.relationOf s)) :
    ConstantOrXorWitness Γ := by
  classical
  let w := Classical.choose hNonempty
  have hW : (Γ.relationOf s).Holds w := Classical.choose_spec hNonempty
  by_cases hComp : (Γ.relationOf s).Holds (BoolTuple.complement w)
  · exact ConstantOrXorWitness.xor
      { xorBlock := binaryProjectionBlock s w
        xorRepresents := binaryProjectionBlock_represents_xor hW hNotZero hNotOne hComp
        notes := "Lemma 4.3 case 2 disequality projection." }
  · exact ConstantOrXorWitness.constants
      (constantsOfSingletonProjection hW hNotZero hNotOne hComp)

/--
Lemma 4.3 first half under the PDF's nonempty-relation precondition:
hard zero/one failures produce either both constants or a represented XOR.
-/
noncomputable def constantOrXorWitnessOfHardCase {Γ : CSP.BoolLanguage}
    (hNonempty : AllRelationsNonempty Γ) (hHard : HardCaseAssumptions Γ) :
    ConstantOrXorWitness Γ := by
  classical
  by_cases hAllEither : ∀ s : Γ.Symbol,
      IsZeroValid (Γ.relationOf s) ∨ IsOneValid (Γ.relationOf s)
  · exact ConstantOrXorWitness.constants
      (constantRepresentationOfAllZeroOrOne hHard hAllEither)
  · have hExists :
        ∃ s : Γ.Symbol,
          ¬ IsZeroValid (Γ.relationOf s) ∧ ¬ IsOneValid (Γ.relationOf s) := by
      classical
      push Not at hAllEither
      exact hAllEither
    let s := Classical.choose hExists
    have hs : ¬ IsZeroValid (Γ.relationOf s) ∧ ¬ IsOneValid (Γ.relationOf s) :=
      Classical.choose_spec hExists
    exact constantOrXorWitnessOfNeitherZeroNorOne (hNonempty s) hs.1 hs.2

/--
Lemma 4.3 strengthened to the no-constants conclusion used by the final
dichotomy proof: either both constants are PP-representable, or XOR is
represented and all relations are complementive.
-/
noncomputable def constantOrComplementiveWitnessOfHardCase {Γ : CSP.BoolLanguage}
    (hNonempty : AllRelationsNonempty Γ) (hHard : HardCaseAssumptions Γ) :
    ConstantOrComplementiveWitness Γ := by
  classical
  match constantOrXorWitnessOfHardCase hNonempty hHard with
  | ConstantOrXorWitness.constants constants =>
      exact ConstantOrComplementiveWitness.constants constants
  | ConstantOrXorWitness.xor xor =>
      by_cases hAllComp : AllRelationsSatisfy Γ IsComplementive
      · exact ConstantOrComplementiveWitness.complementive xor hAllComp
      · have hExists : ∃ s : Γ.Symbol, ¬ IsComplementive (Γ.relationOf s) := by
          by_contra hNo
          apply hAllComp
          intro s
          by_contra hs
          exact hNo ⟨s, hs⟩
        let s := Classical.choose hExists
        have hs : ¬ IsComplementive (Γ.relationOf s) := Classical.choose_spec hExists
        let w := Classical.choose (exists_noncomplementive_failure hs)
        have hw :
            (Γ.relationOf s).Holds w ∧
              ¬ (Γ.relationOf s).Holds (BoolTuple.complement w) :=
          Classical.choose_spec (exists_noncomplementive_failure hs)
        exact ConstantOrComplementiveWitness.constants
          (constantsOfNonComplementiveWithXor xor hw.1 hw.2)

/-- Descriptor for the locally proved Lemma 4.3 constants-or-XOR split. -/
def lemma43ConstantOrXorDescriptor : StatementDescriptor :=
  { pdfReference := "Section 4, Lemma 4.3"
    informalClaim :=
      "Under the nonempty-relation precondition used in the PDF, hard zero/one \
       failures produce either proof-bearing unary constants or a proof-bearing \
       binary disequality/XOR representation."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.Hardness.constantOrXorWitnessOfHardCase"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Hardness.AllRelationsNonempty"
      , "ComplexityReduction.Schaefer.Hardness.ConstantRepresentationWitness"
      , "ComplexityReduction.Schaefer.Hardness.XorRepresentationWitness"
      , "ComplexityReduction.Schaefer.Hardness.constantRepresentationOfAllZeroOrOne"
      , "ComplexityReduction.Schaefer.Hardness.constantOrXorWitnessOfNeitherZeroNorOne"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "This formalizes the constructive constants-or-disequality part of Lemma 4.3 \
       over primitive-positive LanguageRepresentation blocks.  The later PDF step \
       turning the XOR/no-constants branch into the complementive hard route is still \
       separated as the classifyXor branch." }

/--
If both constants are representable over `Γ`, every with-constants relation
symbol has a representation over `Γ`.
-/
def satCWithConstantsLanguageRepresentation {Γ : CSP.BoolLanguage}
    (w : ConstantRepresentationWitness Γ) :
    LanguageRepresentation (satCWithConstantsLanguage Γ) Γ where
  block
    | Sum.inl s => identityRelationFormula Γ s
    | Sum.inr false => w.falseBlock
    | Sum.inr true => w.trueBlock
  represents
    | Sum.inl s => identityRelationFormula_represents Γ s
    | Sum.inr false => w.falseRepresents
    | Sum.inr true => w.trueRepresents
  notes := "SAT_C(S)-to-SAT(S) representation using explicit pinning witnesses."

/--
Lemma 4.2-shaped certificate: representable constants give a costed
representation reduction from local `SAT_C(S)` to local `SAT(S)`.
-/
noncomputable def satCToSatWhenConstantsRepresentable {Γ : CSP.BoolLanguage}
    (w : ConstantRepresentationWitness Γ) :
    RepresentationReductionCertificate (satCWithConstantsLanguage Γ) Γ :=
  representationReductionCertificateOfLanguageRepresentationAuto
    (satCWithConstantsLanguageRepresentation w)

/-! ### LocalRep PP-closure certificates as proof-bearing representation blocks -/

/--
Lift one original `Γ`-constraint into the with-constants language.  This is the
identity on variables and sends the symbol to the original-symbol summand.
-/
def liftOriginalConstraintToSatC {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint Γ) : CSP.Constraint (satCWithConstantsLanguage Γ) where
  symbol := Sum.inl c.symbol
  vars := c.vars

/-- Lift an original `Γ`-formula into `SAT_C(Γ)`. -/
def liftOriginalFormulaToSatC {Γ : CSP.BoolLanguage}
    (φ : SATFormula Γ) : SATFormula (satCWithConstantsLanguage Γ) :=
  φ.map liftOriginalConstraintToSatC

@[simp]
theorem liftOriginalConstraintToSatC_satisfies_iff {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint Γ) (a : SAT.Assignment) :
    CSP.Constraint.Satisfies (liftOriginalConstraintToSatC c) a ↔
      CSP.Constraint.Satisfies c a :=
  Iff.rfl

@[simp]
theorem liftOriginalFormulaToSatC_satisfies_iff {Γ : CSP.BoolLanguage}
    (φ : SATFormula Γ) (a : SAT.Assignment) :
    CSP.Formula.Satisfies (liftOriginalFormulaToSatC φ) a ↔
      CSP.Formula.Satisfies φ a := by
  induction φ with
  | nil => simp [liftOriginalFormulaToSatC]
  | cons c φ ih =>
      constructor
      · intro h
        have h' :
            CSP.Constraint.Satisfies (liftOriginalConstraintToSatC c) a ∧
              CSP.Formula.Satisfies (liftOriginalFormulaToSatC φ) a := by
          simpa [liftOriginalFormulaToSatC] using
            (CSP.Formula.satisfies_cons (liftOriginalConstraintToSatC c)
              (liftOriginalFormulaToSatC φ) a).1 h
        exact (CSP.Formula.satisfies_cons c φ a).2 ⟨by simpa using h'.1, ih.1 h'.2⟩
      · intro h
        have h' :
            CSP.Constraint.Satisfies c a ∧ CSP.Formula.Satisfies φ a :=
          (CSP.Formula.satisfies_cons c φ a).1 h
        exact
          (CSP.Formula.satisfies_cons (liftOriginalConstraintToSatC c)
            (liftOriginalFormulaToSatC φ) a).2
            ⟨by simpa using h'.1, ih.2 h'.2⟩

/-- A tuple extended by two distinguished parameter coordinates: false then true. -/
def tupleWithFalseTrueParams {k : Nat} (t : CSP.BoolTuple k) :
    CSP.BoolTuple (k + 2) :=
  fun i =>
    if h : i.val < k then
      t ⟨i.val, h⟩
    else if i.val = k then
      false
    else
      true

theorem tupleWithFalseTrueParams_of_lt {k : Nat} (t : CSP.BoolTuple k)
    {x : Nat} (hx : x < k) :
    tupleWithFalseTrueParams t ⟨x, by omega⟩ = t ⟨x, hx⟩ := by
  simp [tupleWithFalseTrueParams, hx]

theorem tupleWithFalseTrueParams_falseParam {k : Nat} (t : CSP.BoolTuple k) :
    tupleWithFalseTrueParams t ⟨k, by omega⟩ = false := by
  simp [tupleWithFalseTrueParams]

theorem tupleWithFalseTrueParams_trueParam {k : Nat} (t : CSP.BoolTuple k) :
    tupleWithFalseTrueParams t ⟨k + 1, by omega⟩ = true := by
  simp [tupleWithFalseTrueParams]

/--
Parameter-aware representation of a LocalRep relation.  The produced block has
two additional free variables: coordinate `k` is the false parameter and
coordinate `k+1` is the true parameter.  Under the canonical assignment
`false,true` to these parameters, the block represents `R`.
-/
def ParamRepresents (Γ : CSP.BoolLanguage) {k : Nat} (R : LocalRep.LogRel k)
    (block : RelationFormula Γ (k + 2)) : Prop :=
  ∀ t : CSP.BoolTuple k,
    t ∈ R ↔ ∃ aux : SAT.Assignment,
      CSP.Formula.Satisfies block.constraints
        (extendTupleAssignment (tupleWithFalseTrueParams t) aux)

/-- Base block for one original relation symbol, leaving the two parameters unused. -/
def localRepBaseParamBlock {Γ : CSP.BoolLanguage} (s : Γ.Symbol) :
    RelationFormula Γ ((Γ.relationOf s).arity + 2) where
  constraints :=
    [ { symbol := s
        vars := fun i => i.val } ]
  notes := "LocalRep base relation, parameterized by false/true coordinates."

theorem localRepBaseParamBlock_paramRepresents {Γ : CSP.BoolLanguage} (s : Γ.Symbol) :
    ParamRepresents Γ (Γ.relationOf s).accepts (localRepBaseParamBlock s) := by
  intro t
  constructor
  · intro ht
    refine ⟨fun _ => false, ?_⟩
    intro c hc
    simp [localRepBaseParamBlock] at hc
    subst c
    change (Γ.relationOf s).Holds
      (fun i : Fin (Γ.relationOf s).arity =>
        extendTupleAssignment (tupleWithFalseTrueParams t) (fun _ => false) i.val)
    have hTuple :
        (fun i : Fin (Γ.relationOf s).arity =>
          extendTupleAssignment (tupleWithFalseTrueParams t) (fun _ => false) i.val) = t := by
      funext i
      have hiParam : i.val < (Γ.relationOf s).arity + 2 := by omega
      rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) (fun _ => false) hiParam]
      simpa using tupleWithFalseTrueParams_of_lt t i.isLt
    rw [hTuple]
    exact ht
  · rintro ⟨aux, hSat⟩
    have hConstraint :
        CSP.Constraint.Satisfies
          ({ symbol := s
             vars := fun i : Fin (Γ.relationOf s).arity => i.val } : CSP.Constraint Γ)
          (extendTupleAssignment (tupleWithFalseTrueParams t) aux) := by
      exact hSat _ (by simp [localRepBaseParamBlock])
    change (Γ.relationOf s).Holds
      (fun i : Fin (Γ.relationOf s).arity =>
        extendTupleAssignment (tupleWithFalseTrueParams t) aux i.val) at hConstraint
    have hTuple :
        (fun i : Fin (Γ.relationOf s).arity =>
          extendTupleAssignment (tupleWithFalseTrueParams t) aux i.val) = t := by
      funext i
      have hiParam : i.val < (Γ.relationOf s).arity + 2 := by omega
      rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) aux hiParam]
      simpa using tupleWithFalseTrueParams_of_lt t i.isLt
    rwa [hTuple] at hConstraint

/--
Variable map for existentially removing the last LocalRep argument.  Inner
layout: `k+1` relation arguments, then false/true parameters.  Outer layout:
`k` relation arguments, then false/true parameters; the removed argument is
stored in the first auxiliary slot `k+2`.
-/
def paramExistentialVarMap (k x : Nat) : Nat :=
  if _h : x < k then x
  else if x = k then k + 2
  else if x = k + 1 then k
  else if x = k + 2 then k + 1
  else x

/-- Existential closure for parameter-aware LocalRep blocks. -/
def paramExistentialBlock {Γ : CSP.BoolLanguage} {k : Nat}
    (block : RelationFormula Γ ((k + 1) + 2)) :
    RelationFormula Γ (k + 2) where
  constraints := formulaMapVars (paramExistentialVarMap k) block.constraints
  notes := "LocalRep existential closure with shared false/true parameters."

theorem paramExistentialBlock_paramRepresents {Γ : CSP.BoolLanguage} {k : Nat}
    {R : LocalRep.LogRel (k + 1)} {block : RelationFormula Γ ((k + 1) + 2)}
    (hBlock : ParamRepresents Γ R block) :
    ParamRepresents Γ (LocalRep.existentialQuantify R) (paramExistentialBlock block) := by
  intro t
  constructor
  · intro ht
    rcases (LocalRep.mem_existentialQuantify).1 ht with ⟨b, hb⟩
    rcases (hBlock (LocalRep.extendWith t b)).1 hb with ⟨innerAux, hInner⟩
    let outerAux : SAT.Assignment := fun x => if x = k + 2 then b else innerAux x
    let outerAssign := extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
    let innerAssign :=
      extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.extendWith t b)) innerAux
    have hMapped :
        CSP.Formula.Satisfies block.constraints
          (fun x => outerAssign (paramExistentialVarMap k x)) := by
      refine (FiniteSearch.formula_satisfies_iff_of_agree
        (φ := block.constraints)
        (a := fun x => outerAssign (paramExistentialVarMap k x))
        (b := innerAssign) ?_).2 hInner
      intro x _hx
      by_cases hxk : x < k
      · have hxInner : x < k + 1 := by omega
        have hxOuter : x < k + 2 := by omega
        have hxInnerParam : x < (k + 1) + 2 := by omega
        change
          extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
              (paramExistentialVarMap k x) =
            extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.extendWith t b))
              innerAux x
        rw [show paramExistentialVarMap k x = x by simp [paramExistentialVarMap, hxk]]
        rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hxOuter]
        rw [extendTupleAssignment_of_lt
          (tupleWithFalseTrueParams (LocalRep.extendWith t b)) innerAux hxInnerParam]
        simp [tupleWithFalseTrueParams, LocalRep.extendWith, hxk, hxInner]
      · by_cases hxEq : x = k
        · subst x
          have hInnerParam : k < (k + 1) + 2 := by omega
          change
            extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                (paramExistentialVarMap k k) =
              extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.extendWith t b))
                innerAux k
          rw [show paramExistentialVarMap k k = k + 2 by
            simp [paramExistentialVarMap]]
          rw [extendTupleAssignment_of_lt
            (tupleWithFalseTrueParams (LocalRep.extendWith t b)) innerAux hInnerParam]
          simp [extendTupleAssignment, outerAux, tupleWithFalseTrueParams,
            LocalRep.extendWith]
        · by_cases hxEq1 : x = k + 1
          · subst x
            have hOuterParam : k < k + 2 := by omega
            have hInnerFalse : ¬ k + 1 < k + 1 := by omega
            simp [outerAssign, innerAssign, paramExistentialVarMap, hxk,
              hOuterParam, tupleWithFalseTrueParams]
          · by_cases hxEq2 : x = k + 2
            · subst x
              have hOuterParam : k + 1 < k + 2 := by omega
              have hInnerParam : k + 2 < (k + 1) + 2 := by omega
              change
                extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                    (paramExistentialVarMap k (k + 2)) =
                  extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.extendWith t b))
                    innerAux (k + 2)
              rw [show paramExistentialVarMap k (k + 2) = k + 1 by
                simp [paramExistentialVarMap]]
              rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux
                hOuterParam]
              rw [extendTupleAssignment_of_lt
                (tupleWithFalseTrueParams (LocalRep.extendWith t b)) innerAux hInnerParam]
              simp [tupleWithFalseTrueParams]
            · have hxOuterAux : ¬ x < k + 2 := by omega
              have hxInnerAux : ¬ x < k + 3 := by omega
              have hxNotAuxSlot : x ≠ k + 2 := hxEq2
              change
                extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                    (paramExistentialVarMap k x) =
                  extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.extendWith t b))
                    innerAux x
              rw [show paramExistentialVarMap k x = x by
                simp [paramExistentialVarMap, hxk, hxEq, hxEq1, hxEq2]]
              simp [extendTupleAssignment, hxOuterAux, hxInnerAux,
                outerAux, hxNotAuxSlot]
    refine ⟨outerAux, ?_⟩
    exact (formulaMapVars_satisfies_iff
      (paramExistentialVarMap k) block.constraints outerAssign).2 hMapped
  · rintro ⟨outerAux, hOuter⟩
    let outerAssign := extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
    have hMapped :
        CSP.Formula.Satisfies block.constraints
          (fun x => outerAssign (paramExistentialVarMap k x)) :=
      (formulaMapVars_satisfies_iff
        (paramExistentialVarMap k) block.constraints outerAssign).1 hOuter
    let b := outerAux (k + 2)
    let innerAux : SAT.Assignment := fun x => outerAssign (paramExistentialVarMap k x)
    let innerAssign :=
      extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.extendWith t b)) innerAux
    have hInner : CSP.Formula.Satisfies block.constraints innerAssign := by
      refine (FiniteSearch.formula_satisfies_iff_of_agree
        (φ := block.constraints)
        (a := innerAssign)
        (b := fun x => outerAssign (paramExistentialVarMap k x)) ?_).2 hMapped
      intro x _hx
      by_cases hxk : x < k
      · have hxInner : x < k + 1 := by omega
        have hxOuter : x < k + 2 := by omega
        have hxInnerParam : x < (k + 1) + 2 := by omega
        change
          extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.extendWith t b))
              innerAux x =
            extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
              (paramExistentialVarMap k x)
        rw [show paramExistentialVarMap k x = x by simp [paramExistentialVarMap, hxk]]
        rw [extendTupleAssignment_of_lt
          (tupleWithFalseTrueParams (LocalRep.extendWith t b)) innerAux hxInnerParam]
        rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hxOuter]
        simp [tupleWithFalseTrueParams, LocalRep.extendWith, hxk, hxInner]
      · by_cases hxEq : x = k
        · subst x
          have hInnerParam : k < (k + 1) + 2 := by omega
          change
            extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.extendWith t b))
                innerAux k =
              extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                (paramExistentialVarMap k k)
          rw [show paramExistentialVarMap k k = k + 2 by simp [paramExistentialVarMap]]
          rw [extendTupleAssignment_of_lt
            (tupleWithFalseTrueParams (LocalRep.extendWith t b)) innerAux hInnerParam]
          have hOuterAux : ¬ k + 2 < k + 2 := by omega
          simp [b, extendTupleAssignment, tupleWithFalseTrueParams,
            LocalRep.extendWith]
        · by_cases hxEq1 : x = k + 1
          · subst x
            have hInnerFalse : ¬ k + 1 < k + 1 := by omega
            have hOuterParam : k < k + 2 := by omega
            simp [outerAssign, innerAssign, innerAux, paramExistentialVarMap,
              hxk, hOuterParam, tupleWithFalseTrueParams]
          · by_cases hxEq2 : x = k + 2
            · subst x
              have hInnerParam : k + 2 < (k + 1) + 2 := by omega
              have hOuterParam : k + 1 < k + 2 := by omega
              change
                extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.extendWith t b))
                    innerAux (k + 2) =
                  extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                    (paramExistentialVarMap k (k + 2))
              rw [show paramExistentialVarMap k (k + 2) = k + 1 by
                simp [paramExistentialVarMap]]
              rw [extendTupleAssignment_of_lt
                (tupleWithFalseTrueParams (LocalRep.extendWith t b)) innerAux hInnerParam]
              rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux
                hOuterParam]
              simp [tupleWithFalseTrueParams]
            · have hxInnerAux : ¬ x < k + 3 := by omega
              have hxOuterAux : ¬ x < k + 2 := by omega
              change
                extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.extendWith t b))
                    innerAux x =
                  extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                    (paramExistentialVarMap k x)
              rw [show paramExistentialVarMap k x = x by
                simp [paramExistentialVarMap, hxk, hxEq, hxEq1, hxEq2]]
              simp [outerAssign, innerAux, extendTupleAssignment, hxInnerAux,
                hxOuterAux, paramExistentialVarMap, hxk, hxEq, hxEq1, hxEq2]
    have hR : LocalRep.extendWith t b ∈ R :=
      (hBlock (LocalRep.extendWith t b)).2 ⟨innerAux, hInner⟩
    exact (LocalRep.mem_existentialQuantify).2 ⟨b, hR⟩


end Hardness
end Schaefer
end ComplexityReduction
