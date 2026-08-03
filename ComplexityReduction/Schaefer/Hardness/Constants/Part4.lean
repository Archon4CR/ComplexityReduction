import ComplexityReduction.Schaefer.Hardness.Constants.Part3

namespace ComplexityReduction
namespace Schaefer
namespace Hardness

/-- The XOR tuple formed by two Boolean parameter values. -/
def xorParamTuple (p q : Bool) : CSP.BoolTuple CSP.StandardRelations.xorRel.arity :=
  fun
    | ⟨0, _⟩ => p
    | ⟨1, _⟩ => q

@[simp]
theorem xorParamTuple_zero (p q : Bool) :
    xorParamTuple p q ⟨0, by decide⟩ = p := rfl

@[simp]
theorem xorParamTuple_one (p q : Bool) :
    xorParamTuple p q ⟨1, by decide⟩ = q := rfl

theorem xorParamTuple_holds_iff (p q : Bool) :
    CSP.StandardRelations.xorRel.Holds (xorParamTuple p q) ↔ p ≠ q := by
  simpa [xorParamTuple] using xorRel_holds_iff (xorParamTuple p q)

/--
The no-constants complementive block: a parameterized exactly-one block plus a
represented XOR constraint on its false/true parameters.
-/
noncomputable def naeBlockOfParamExactlyOneAndXor {Γ : CSP.BoolLanguage}
    (block : RelationFormula Γ (3 + 2)) (xor : XorRepresentationWitness Γ) :
    RelationFormula Γ CSP.Examples.notAllEqual3Rel.arity where
  constraints :=
    block.constraints ++
      formulaMapVars
        (xorParamVarMap 3 (max (3 + 2) (formulaVarBound block.constraints)))
        xor.xorBlock.constraints
  notes :=
    "Complementive no-constants block: exists p q, parameterized exactly-one(x,y,z,p,q) \
     and represented xor(p,q)."

theorem complement_exactlyOne_of_exactlyOne_complement
    (t : CSP.BoolTuple 3) :
    BoolTuple.complement (BoolTuple.complement t) ∈ LocalRep.exactlyOneRel →
      t ∈ LocalRep.exactlyOneRel := by
  intro h
  have hEq : BoolTuple.complement (BoolTuple.complement t) = t := by
    funext i
    simp [BoolTuple.complement]
  simpa [hEq] using h

theorem naeBlockOfParamExactlyOneAndXor_represents_tuple {Γ : CSP.BoolLanguage}
    (hComp : AllRelationsSatisfy Γ IsComplementive)
    {block : RelationFormula Γ (3 + 2)}
    (hBlock : ParamRepresents Γ LocalRep.exactlyOneRel block)
    (xor : XorRepresentationWitness Γ) (t : CSP.BoolTuple 3) :
    CSP.Examples.notAllEqual3Rel.Holds t ↔
      ∃ aux : SAT.Assignment,
        CSP.Formula.Satisfies (naeBlockOfParamExactlyOneAndXor block xor).constraints
          (extendTupleAssignment t aux) := by
  classical
  let offset := max (3 + 2) (formulaVarBound block.constraints)
  have hNAE := notAllEqual3Rel_holds_iff_exactlyOne_or_complement t
  constructor
  · intro ht
    rcases hNAE.1 ht with hOne | hCompOne
    · rcases (hBlock t).1 hOne with ⟨blockAux, hBlockSat⟩
      have hXorRel : CSP.StandardRelations.xorRel.Holds (xorParamTuple false true) :=
        (xorParamTuple_holds_iff false true).2 (by decide)
      rcases (xor.xorRepresents (xorParamTuple false true)).1 hXorRel with
        ⟨xorAux, hXorSat⟩
      let finalAux : SAT.Assignment := fun x =>
        if x = 3 then false
        else if x = 4 then true
        else if offset ≤ x then xorAux (x - offset)
        else blockAux x
      let finalAssign := extendTupleAssignment t finalAux
      refine ⟨finalAux, ?_⟩
      refine (CSP.Formula.satisfies_append _ _ finalAssign).2 ⟨?_, ?_⟩
      · refine (FiniteSearch.formula_satisfies_iff_of_agree
          (φ := block.constraints)
          (a := finalAssign)
          (b := extendTupleAssignment (tupleWithFalseTrueParams t) blockAux) ?_).2
          hBlockSat
        intro x hx
        by_cases hxFree : x < 3
        · have hxParam : x < 3 + 2 := by omega
          rw [show finalAssign x = t ⟨x, hxFree⟩ by
            simp [finalAssign, hxFree]]
          rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) blockAux hxParam]
          exact (tupleWithFalseTrueParams_of_lt t hxFree).symm
        · by_cases hxFalse : x = 3
          · subst x
            have hParam : 3 < 3 + 2 := by omega
            rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) blockAux hParam]
            rw [tupleWithFalseTrueParams_falseParam t]
            simp [finalAssign, finalAux, extendTupleAssignment]
          · by_cases hxTrue : x = 4
            · subst x
              have hParam : 3 + 1 < 3 + 2 := by omega
              rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) blockAux hParam]
              rw [tupleWithFalseTrueParams_trueParam t]
              simp [finalAssign, finalAux, extendTupleAssignment]
            · have hxParam : ¬ x < 3 + 2 := by omega
              have hxBound : x < formulaVarBound block.constraints := var_lt_formulaVarBound hx
              have hxOffset : x < offset :=
                lt_of_lt_of_le hxBound (Nat.le_max_right (3 + 2) (formulaVarBound block.constraints))
              have hNotOffset : ¬ offset ≤ x := by omega
              simp [finalAssign, finalAux, extendTupleAssignment, hxFree, hxParam,
                hxFalse, hxTrue, hNotOffset]
      · exact (formulaMapVars_satisfies_iff
          (xorParamVarMap 3 offset) xor.xorBlock.constraints finalAssign).2 (by
          refine (FiniteSearch.formula_satisfies_iff_of_agree
            (φ := xor.xorBlock.constraints)
            (a := fun x => finalAssign (xorParamVarMap 3 offset x))
            (b := extendTupleAssignment (xorParamTuple false true) xorAux) ?_).2 hXorSat
          intro x _hx
          by_cases hxSmall : x < 2
          · have hxCases : x = 0 ∨ x = 1 := by omega
            rcases hxCases with rfl | rfl
            · simp [finalAssign, finalAux, extendTupleAssignment, xorParamVarMap,
                xorParamTuple]
            · simp [finalAssign, finalAux, extendTupleAssignment, xorParamVarMap,
                xorParamTuple]
          · have hx0 : x ≠ 0 := by omega
            have hx1 : x ≠ 1 := by omega
            have hNotFree : ¬ offset + x < 3 := by omega
            have hOffset : offset ≤ offset + x := by omega
            have hOffsetLower : 5 ≤ offset :=
              Nat.le_max_left (3 + 2) (formulaVarBound block.constraints)
            have hOff3 : offset + x ≠ 3 := by omega
            have hOff4 : offset + x ≠ 4 := by omega
            simp [finalAssign, finalAux, extendTupleAssignment, xorParamVarMap, hx0, hx1,
              hxSmall, hNotFree, hOffset, hOff3, hOff4])
    · rcases (hBlock (BoolTuple.complement t)).1 hCompOne with ⟨blockAux, hBlockSat⟩
      let baseAssign :=
        extendTupleAssignment (tupleWithFalseTrueParams (BoolTuple.complement t)) blockAux
      have hBlockSatComp :
          CSP.Formula.Satisfies block.constraints (assignmentComplement baseAssign) :=
        formula_satisfies_assignmentComplement hComp block.constraints baseAssign hBlockSat
      have hXorRel : CSP.StandardRelations.xorRel.Holds (xorParamTuple true false) :=
        (xorParamTuple_holds_iff true false).2 (by decide)
      rcases (xor.xorRepresents (xorParamTuple true false)).1 hXorRel with
        ⟨xorAux, hXorSat⟩
      let finalAux : SAT.Assignment := fun x =>
        if x = 3 then true
        else if x = 4 then false
        else if offset ≤ x then xorAux (x - offset)
        else !(blockAux x)
      let finalAssign := extendTupleAssignment t finalAux
      refine ⟨finalAux, ?_⟩
      refine (CSP.Formula.satisfies_append _ _ finalAssign).2 ⟨?_, ?_⟩
      · refine (FiniteSearch.formula_satisfies_iff_of_agree
          (φ := block.constraints)
          (a := finalAssign)
          (b := assignmentComplement baseAssign) ?_).2 hBlockSatComp
        intro x hx
        by_cases hxFree : x < 3
        · have hxParam : x < 3 + 2 := by omega
          rw [show finalAssign x = t ⟨x, hxFree⟩ by
            simp [finalAssign, hxFree]]
          rw [show assignmentComplement baseAssign x =
              !(BoolTuple.complement t ⟨x, hxFree⟩) by
            simp [baseAssign, assignmentComplement, hxParam,
              tupleWithFalseTrueParams_of_lt (BoolTuple.complement t) hxFree]]
          simp [BoolTuple.complement]
        · by_cases hxFalse : x = 3
          · subst x
            have hParam : 3 < 3 + 2 := by omega
            have hBase3 : baseAssign 3 = false := by
              change
                extendTupleAssignment
                    (tupleWithFalseTrueParams (BoolTuple.complement t)) blockAux 3 =
                  false
              rw [extendTupleAssignment_of_lt
                (tupleWithFalseTrueParams (BoolTuple.complement t)) blockAux hParam]
              exact tupleWithFalseTrueParams_falseParam (BoolTuple.complement t)
            rw [show assignmentComplement baseAssign 3 = true by
              simp [assignmentComplement, hBase3]]
            simp [finalAssign, finalAux, extendTupleAssignment]
          · by_cases hxTrue : x = 4
            · subst x
              have hParam : 3 + 1 < 3 + 2 := by omega
              have hBase4 : baseAssign 4 = true := by
                change
                  extendTupleAssignment
                      (tupleWithFalseTrueParams (BoolTuple.complement t)) blockAux 4 =
                    true
                rw [extendTupleAssignment_of_lt
                  (tupleWithFalseTrueParams (BoolTuple.complement t)) blockAux hParam]
                exact tupleWithFalseTrueParams_trueParam (BoolTuple.complement t)
              rw [show assignmentComplement baseAssign 4 = false by
                simp [assignmentComplement, hBase4]]
              simp [finalAssign, finalAux, extendTupleAssignment]
            · have hxParam : ¬ x < 3 + 2 := by omega
              have hxBound : x < formulaVarBound block.constraints := var_lt_formulaVarBound hx
              have hxOffset : x < offset :=
                lt_of_lt_of_le hxBound (Nat.le_max_right (3 + 2) (formulaVarBound block.constraints))
              have hNotOffset : ¬ offset ≤ x := by omega
              simp [finalAssign, finalAux, baseAssign, assignmentComplement,
                extendTupleAssignment, hxFree, hxParam, hxFalse, hxTrue, hNotOffset]
      · exact (formulaMapVars_satisfies_iff
          (xorParamVarMap 3 offset) xor.xorBlock.constraints finalAssign).2 (by
          refine (FiniteSearch.formula_satisfies_iff_of_agree
            (φ := xor.xorBlock.constraints)
            (a := fun x => finalAssign (xorParamVarMap 3 offset x))
            (b := extendTupleAssignment (xorParamTuple true false) xorAux) ?_).2 hXorSat
          intro x _hx
          by_cases hxSmall : x < 2
          · have hxCases : x = 0 ∨ x = 1 := by omega
            rcases hxCases with rfl | rfl
            · simp [finalAssign, finalAux, extendTupleAssignment, xorParamVarMap,
                xorParamTuple]
            · simp [finalAssign, finalAux, extendTupleAssignment, xorParamVarMap,
                xorParamTuple]
          · have hx0 : x ≠ 0 := by omega
            have hx1 : x ≠ 1 := by omega
            have hNotFree : ¬ offset + x < 3 := by omega
            have hOffset : offset ≤ offset + x := by omega
            have hOffsetLower : 5 ≤ offset :=
              Nat.le_max_left (3 + 2) (formulaVarBound block.constraints)
            have hOff3 : offset + x ≠ 3 := by omega
            have hOff4 : offset + x ≠ 4 := by omega
            simp [finalAssign, finalAux, extendTupleAssignment, xorParamVarMap, hx0, hx1,
              hxSmall, hNotFree, hOffset, hOff3, hOff4])
  · rintro ⟨aux, hSat⟩
    let a := extendTupleAssignment t aux
    have hParts := (CSP.Formula.satisfies_append
      block.constraints
      (formulaMapVars (xorParamVarMap 3 offset) xor.xorBlock.constraints)
      a).1 hSat
    have hXorMapped :
        CSP.Formula.Satisfies xor.xorBlock.constraints
          (fun x => a (xorParamVarMap 3 offset x)) :=
      (formulaMapVars_satisfies_iff
        (xorParamVarMap 3 offset) xor.xorBlock.constraints a).1 hParts.2
    let xorAux : SAT.Assignment := fun x => a (offset + x)
    have hXorSat :
        CSP.Formula.Satisfies xor.xorBlock.constraints
          (extendTupleAssignment (xorParamTuple (a 3) (a 4)) xorAux) := by
      refine (FiniteSearch.formula_satisfies_iff_of_agree
        (φ := xor.xorBlock.constraints)
        (a := extendTupleAssignment (xorParamTuple (a 3) (a 4)) xorAux)
        (b := fun x => a (xorParamVarMap 3 offset x)) ?_).2 hXorMapped
      intro x _hx
      by_cases hxSmall : x < 2
      · have hxCases : x = 0 ∨ x = 1 := by omega
        rcases hxCases with rfl | rfl
        · simp [extendTupleAssignment, xorParamTuple, xorParamVarMap]
        · simp [extendTupleAssignment, xorParamTuple, xorParamVarMap]
      · have hx0 : x ≠ 0 := by omega
        have hx1 : x ≠ 1 := by omega
        simp [extendTupleAssignment, xorAux, xorParamVarMap, hxSmall, hx0, hx1]
    have hXorRel : CSP.StandardRelations.xorRel.Holds (xorParamTuple (a 3) (a 4)) :=
      (xor.xorRepresents (xorParamTuple (a 3) (a 4))).2 ⟨xorAux, hXorSat⟩
    have hNe : a 3 ≠ a 4 := (xorParamTuple_holds_iff (a 3) (a 4)).1 hXorRel
    cases h3 : a 3 <;> cases h4 : a 4
    · exact False.elim (hNe (by simp [h3, h4]))
    · have hFree : ∀ x : Nat, ∀ hx : x < 3, a x = t ⟨x, hx⟩ := by
        intro x hx
        simp [a, hx]
      have hParamSat :
          CSP.Formula.Satisfies block.constraints
            (extendTupleAssignment (tupleWithFalseTrueParams t) a) :=
        (formula_satisfies_iff_tupleWithFalseTrueParams_of_agree
          (Γ := Γ) (block := block) t a hFree (by simp [h3]) (by simp [h4])).1 hParts.1
      have hOne : t ∈ LocalRep.exactlyOneRel := (hBlock t).2 ⟨a, hParamSat⟩
      exact hNAE.2 (Or.inl hOne)
    · have hCompSat :
          CSP.Formula.Satisfies block.constraints (assignmentComplement a) :=
        formula_satisfies_assignmentComplement hComp block.constraints a hParts.1
      have hFree : ∀ x : Nat, ∀ hx : x < 3,
          assignmentComplement a x = BoolTuple.complement t ⟨x, hx⟩ := by
        intro x hx
        simp [assignmentComplement, BoolTuple.complement, a, hx]
      have hParamSat :
          CSP.Formula.Satisfies block.constraints
            (extendTupleAssignment (tupleWithFalseTrueParams (BoolTuple.complement t))
              (assignmentComplement a)) :=
        (formula_satisfies_iff_tupleWithFalseTrueParams_of_agree
          (Γ := Γ) (block := block) (BoolTuple.complement t) (assignmentComplement a)
          hFree (by simp [assignmentComplement, h3])
          (by simp [assignmentComplement, h4])).1 hCompSat
      have hCompOne : BoolTuple.complement t ∈ LocalRep.exactlyOneRel :=
        (hBlock (BoolTuple.complement t)).2 ⟨assignmentComplement a, hParamSat⟩
      exact hNAE.2 (Or.inr hCompOne)
    · exact False.elim (hNe (by simp [h3, h4]))

theorem naeBlockOfParamExactlyOneAndXor_represents {Γ : CSP.BoolLanguage}
    (hComp : AllRelationsSatisfy Γ IsComplementive)
    {block : RelationFormula Γ (3 + 2)}
    (hBlock : ParamRepresents Γ LocalRep.exactlyOneRel block)
    (xor : XorRepresentationWitness Γ) :
    RepresentsRelation Γ CSP.Examples.notAllEqual3Rel
      (naeBlockOfParamExactlyOneAndXor block xor) := by
  intro t
  let u : CSP.BoolTuple 3 := t
  simpa [u] using
    (naeBlockOfParamExactlyOneAndXor_represents_tuple
      (Γ := Γ) hComp hBlock xor u)

/--
Complementive no-constants hard case: Section 3 supplies the parameterized
exactly-one block; Section 4 supplies XOR for the two parameter variables, so
ordinary NAE-3SAT is represented over `Γ`.
-/
noncomputable def repNAEWitnessOfComplementiveHardCase {Γ : CSP.BoolLanguage}
    (hHard : HardCaseAssumptions Γ)
    (xor : XorRepresentationWitness Γ)
    (hComp : AllRelationsSatisfy Γ IsComplementive) :
    RepNAEWitness Γ := by
  classical
  let packed :=
    paramBlockOfLanguageInRep
      (Γ := Γ)
      (LocalRepBridge.exactlyOneInLocalRepOfHardCase hHard)
  exact
    RepNAEWitness.ofBlock
      (naeBlockOfParamExactlyOneAndXor packed.1 xor)
      (naeBlockOfParamExactlyOneAndXor_represents hComp packed.2 xor)
      "Section 3 parameterized exactly-one plus represented XOR in the \
       complementive no-constants branch."

/-- Section 3: hard-case counterexamples produce one-in-three over `SAT_C(Γ)`. -/
noncomputable def repOneInThreeWitnessWithConstantsOfHardCase {Γ : CSP.BoolLanguage}
    (hHard : HardCaseAssumptions Γ) :
    RepOneInThreeWitness (satCWithConstantsLanguage Γ) := by
  classical
  let packed :=
    paramBlockOfLanguageInRep
      (Γ := Γ)
      (LocalRepBridge.exactlyOneInLocalRepOfHardCase hHard)
  exact
    RepOneInThreeWitness.ofBlock
      (relationFormulaOfParamBlockWithConstants CSP.Examples.oneInThreeRel packed.1)
      (relationFormulaOfParamBlockWithConstants_represents
        packed.2 oneInThreeRel_holds_iff_exactlyOneRel)
      "Section 3 LocalRep exactly-one witness, with SAT_C pins for constants."

/-- Package the SAT_C one-in-three witness as a supported hard-base witness. -/
noncomputable def hardBaseRepresentationWitnessWithConstantsOfHardCase
    {Γ : CSP.BoolLanguage} (hHard : HardCaseAssumptions Γ) :
    HardBaseRepresentationWitness (satCWithConstantsLanguage Γ) :=
  HardBaseRepresentationWitness.oneInThree
    (repOneInThreeWitnessWithConstantsOfHardCase hHard)

/-- Remove constants from a 3SAT-like representation witness using explicit constant blocks. -/
noncomputable def repThreeSATLikeWitnessWithoutConstants {Γ : CSP.BoolLanguage}
    (constants : ConstantRepresentationWitness Γ)
    (w : RepThreeSATLikeWitness (satCWithConstantsLanguage Γ)) :
    RepThreeSATLikeWitness Γ where
  representation :=
    composeLanguageRepresentation
      CSP.Examples.threeSATLikeLanguage
      (satCWithConstantsLanguage Γ)
      Γ
      w.representation
      (satCWithConstantsLanguageRepresentation constants)
  notes := "3SAT-like with-constants witness composed with constant representations."

/-- Remove constants from a one-in-three representation witness using explicit constant blocks. -/
noncomputable def repOneInThreeWitnessWithoutConstants {Γ : CSP.BoolLanguage}
    (constants : ConstantRepresentationWitness Γ)
    (w : RepOneInThreeWitness (satCWithConstantsLanguage Γ)) :
    RepOneInThreeWitness Γ where
  representation :=
    composeLanguageRepresentation
      CSP.Examples.oneInThreeLanguage
      (satCWithConstantsLanguage Γ)
      Γ
      w.representation
      (satCWithConstantsLanguageRepresentation constants)
  notes := "One-in-three with-constants witness composed with constant representations."

/-- Remove constants from a NAE-3SAT representation witness using explicit constant blocks. -/
noncomputable def repNAEWitnessWithoutConstants {Γ : CSP.BoolLanguage}
    (constants : ConstantRepresentationWitness Γ)
    (w : RepNAEWitness (satCWithConstantsLanguage Γ)) :
    RepNAEWitness Γ where
  representation :=
    composeLanguageRepresentation
      CSP.Examples.notAllEqual3Language
      (satCWithConstantsLanguage Γ)
      Γ
      w.representation
      (satCWithConstantsLanguageRepresentation constants)
  notes := "NAE-3SAT with-constants witness composed with constant representations."

/-- Remove constants from any supported hard-base witness using explicit constant blocks. -/
noncomputable def hardBaseRepresentationWitnessWithoutConstants {Γ : CSP.BoolLanguage}
    (constants : ConstantRepresentationWitness Γ) :
    HardBaseRepresentationWitness (satCWithConstantsLanguage Γ) →
      HardBaseRepresentationWitness Γ
  | HardBaseRepresentationWitness.threeSATLike w =>
      HardBaseRepresentationWitness.threeSATLike
        (repThreeSATLikeWitnessWithoutConstants constants w)
  | HardBaseRepresentationWitness.oneInThree w =>
      HardBaseRepresentationWitness.oneInThree
        (repOneInThreeWitnessWithoutConstants constants w)
  | HardBaseRepresentationWitness.nae3 w =>
      HardBaseRepresentationWitness.nae3
        (repNAEWitnessWithoutConstants constants w)

/--
With-constants version of the Section 3/4 witness-producing theorem, still
indexed by the original hard assumptions.
-/
abbrev SatCSection34ClassificationWitness (Γ : CSP.BoolLanguage) : Type :=
  HardCaseAssumptions Γ → HardBaseRepresentationWitness (satCWithConstantsLanguage Γ)

/--
Section 4 composition: a constants witness builder plus a with-constants hard
base witness builder yields the no-constants Section 3/4 witness expected by the
hard-side wrappers.
-/
noncomputable def section34WitnessOfSatCAndConstants {Γ : CSP.BoolLanguage}
    (constants : HardCaseAssumptions Γ → ConstantRepresentationWitness Γ)
    (classifyWithConstants : SatCSection34ClassificationWitness Γ) :
    Section34ClassificationWitness Γ :=
  fun hHard =>
    hardBaseRepresentationWitnessWithoutConstants
      (constants hHard)
      (classifyWithConstants hHard)

/-- Hard-side statement from the with-constants route and explicit constant representations. -/
theorem hardSideStatement_ofSatCAndConstants {Γ : CSP.BoolLanguage}
    (constants : HardCaseAssumptions Γ → ConstantRepresentationWitness Γ)
    (classifyWithConstants : SatCSection34ClassificationWitness Γ) :
    hardSideStatement Γ :=
  hardSideStatement_ofSection34Classification
    (section34WitnessOfSatCAndConstants constants classifyWithConstants)

/--
Section 4 hard-case split over the currently formalized no-constants witness:
the constants branch is discharged by the existing with-constants classifier;
the XOR/complementive branch is supplied as a separate proof-bearing hard-base
witness builder.
-/
noncomputable def section34WitnessOfConstantOrXorSplit {Γ : CSP.BoolLanguage}
    (hNonempty : AllRelationsNonempty Γ)
    (classifyWithConstants : SatCSection34ClassificationWitness Γ)
    (classifyXor :
      ∀ _ : HardCaseAssumptions Γ,
        XorRepresentationWitness Γ → HardBaseRepresentationWitness Γ) :
    Section34ClassificationWitness Γ := fun hHard =>
  match constantOrXorWitnessOfHardCase hNonempty hHard with
  | ConstantOrXorWitness.constants constants =>
      hardBaseRepresentationWitnessWithoutConstants constants (classifyWithConstants hHard)
  | ConstantOrXorWitness.xor xor =>
      classifyXor hHard xor

/-- Hard-side statement from the formalized constants/XOR split and explicit branch classifiers. -/
theorem hardSideStatement_ofConstantOrXorSplit {Γ : CSP.BoolLanguage}
    (hNonempty : AllRelationsNonempty Γ)
    (classifyWithConstants : SatCSection34ClassificationWitness Γ)
    (classifyXor :
      ∀ _ : HardCaseAssumptions Γ,
        XorRepresentationWitness Γ → HardBaseRepresentationWitness Γ) :
    hardSideStatement Γ :=
  hardSideStatement_ofSection34Classification
    (section34WitnessOfConstantOrXorSplit hNonempty classifyWithConstants classifyXor)

/--
The local Section 3/4 hard witness theorem under the PDF's nonempty-relation
precondition.  Constants are eliminated through explicit constant blocks; the
no-constants complementive branch uses the proof-bearing NAE construction above.
-/
noncomputable def hardBaseRepresentationWitnessOfHardCase {Γ : CSP.BoolLanguage}
    (hNonempty : AllRelationsNonempty Γ)
    (hHard : HardCaseAssumptions Γ) :
    HardBaseRepresentationWitness Γ := by
  classical
  match constantOrComplementiveWitnessOfHardCase hNonempty hHard with
  | ConstantOrComplementiveWitness.constants constants =>
      exact
        hardBaseRepresentationWitnessWithoutConstants
          constants
          (hardBaseRepresentationWitnessWithConstantsOfHardCase hHard)
  | ConstantOrComplementiveWitness.complementive xor hComp =>
      exact
        HardBaseRepresentationWitness.nae3
          (repNAEWitnessOfComplementiveHardCase hHard xor hComp)

/-- Section 3/4 witness builder from the formalized hard-case split. -/
noncomputable def section34WitnessOfHardCase {Γ : CSP.BoolLanguage}
    (hNonempty : AllRelationsNonempty Γ) :
    Section34ClassificationWitness Γ :=
  fun hHard => hardBaseRepresentationWitnessOfHardCase hNonempty hHard

/-- Hard-case assumptions produce a typed hard-classification route. -/
noncomputable def hardClassificationRouteOfHardCase {Γ : CSP.BoolLanguage}
    (hNonempty : AllRelationsNonempty Γ) :
    HardCaseAssumptions Γ → HardClassificationRoute Γ :=
  hardClassificationRouteOfSection34 (section34WitnessOfHardCase hNonempty)

/-- Hard-case assumptions produce the local hard relation certificate. -/
noncomputable def hardRelationCertificateOfHardCase {Γ : CSP.BoolLanguage}
    (hNonempty : AllRelationsNonempty Γ) :
    HardCaseAssumptions Γ → HardRelationCertificate Γ :=
  hardRelationCertificateOfSection34 (section34WitnessOfHardCase hNonempty)

/-- Boundary-explicit hard-side statement from the completed local Section 3/4 witness. -/
theorem hardSideStatement_ofHardCase {Γ : CSP.BoolLanguage}
    (hNonempty : AllRelationsNonempty Γ) :
    hardSideStatement Γ :=
  hardSideStatement_ofSection34Classification (section34WitnessOfHardCase hNonempty)

/-- Descriptor for the local constants layer and Lemma 4.2-shaped reduction. -/
def satCConstantsDescriptor : StatementDescriptor :=
  { pdfReference := "Section 4, Lemma 4.2"
    informalClaim :=
      "If the two unary constants are representable over S, the local SAT_C(S) \
       language reduces to SAT(S) through the generic representation route."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.Hardness.satCToSatWhenConstantsRepresentable"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Hardness.satCWithConstantsLanguage"
      , "ComplexityReduction.Schaefer.Hardness.ConstantRepresentationWitness"
      , "ComplexityReduction.Schaefer.Hardness.satCWithConstantsLanguageRepresentation"
      , "ComplexityReduction.Schaefer.Hardness.representationReductionCertificateOfLanguageRepresentationAuto"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "This proves the typed constants-elimination certificate only when explicit \
       constant representations are supplied.  Lemma 4.3's construction of those \
       witnesses from hard-case assumptions remains future work." }

end Hardness
end Schaefer
end ComplexityReduction
