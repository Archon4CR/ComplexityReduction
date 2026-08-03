import ComplexityReduction.Schaefer.Hardness.Constants.Part2

namespace ComplexityReduction
namespace Schaefer
namespace Hardness

/--
Variable map for LocalRep substitution.  The source free variables are mapped
by `π`; Boolean constants are sent to the shared false/true parameters.
Existing auxiliary variables are shifted above the new free variables and the
two parameters.
-/

def paramSubstVarMap {k m : Nat} (π : Fin k → Fin m ⊕ Bool) (x : Nat) : Nat :=
  if h : x < k then
    match π ⟨x, h⟩ with
    | Sum.inl j => j.val
    | Sum.inr false => m
    | Sum.inr true => m + 1
  else if x = k then
    m
  else if x = k + 1 then
    m + 1
  else
    m + 2 + x

/-- Substitution closure for parameter-aware LocalRep blocks. -/
def paramSubstBlock {Γ : CSP.BoolLanguage} {k m : Nat}
    (π : Fin k → Fin m ⊕ Bool) (block : RelationFormula Γ (k + 2)) :
    RelationFormula Γ (m + 2) where
  constraints := formulaMapVars (paramSubstVarMap π) block.constraints
  notes := "LocalRep substitution with constants routed through false/true parameters."

theorem paramSubstBlock_paramRepresents {Γ : CSP.BoolLanguage} {k m : Nat}
    {R : LocalRep.LogRel k} {block : RelationFormula Γ (k + 2)}
    (π : Fin k → Fin m ⊕ Bool)
    (hBlock : ParamRepresents Γ R block) :
    ParamRepresents Γ (LocalRep.substitute R π) (paramSubstBlock π block) := by
  intro t
  constructor
  · intro ht
    have hR : LocalRep.substApply π t ∈ R := (LocalRep.mem_substitute).1 ht
    rcases (hBlock (LocalRep.substApply π t)).1 hR with ⟨innerAux, hInner⟩
    let outerAux : SAT.Assignment :=
      fun y => if h : m + 2 ≤ y then innerAux (y - (m + 2)) else false
    let outerAssign := extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
    let innerAssign :=
      extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.substApply π t)) innerAux
    have hMapped :
        CSP.Formula.Satisfies block.constraints
          (fun x => outerAssign (paramSubstVarMap π x)) := by
      refine (FiniteSearch.formula_satisfies_iff_of_agree
        (φ := block.constraints)
        (a := fun x => outerAssign (paramSubstVarMap π x))
        (b := innerAssign) ?_).2 hInner
      intro x _hx
      by_cases hxk : x < k
      · have hxInnerParam : x < k + 2 := by omega
        have hInnerAt :
            tupleWithFalseTrueParams (LocalRep.substApply π t) ⟨x, hxInnerParam⟩ =
              LocalRep.substApply π t ⟨x, hxk⟩ := by
          simpa using tupleWithFalseTrueParams_of_lt (LocalRep.substApply π t) hxk
        change
          extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
              (paramSubstVarMap π x) =
            extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.substApply π t))
              innerAux x
        rw [extendTupleAssignment_of_lt
          (tupleWithFalseTrueParams (LocalRep.substApply π t)) innerAux hxInnerParam]
        cases hπ : π ⟨x, hxk⟩ with
        | inl j =>
            have hj : j.val < m := j.isLt
            have hjParam : j.val < m + 2 := by omega
            have hOuterAt : tupleWithFalseTrueParams t ⟨j.val, hjParam⟩ = t j := by
              simpa using tupleWithFalseTrueParams_of_lt t hj
            rw [show paramSubstVarMap π x = j.val by
              simp [paramSubstVarMap, hxk, hπ]]
            rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hjParam]
            rw [hOuterAt, hInnerAt]
            simp [LocalRep.substApply, hπ]
        | inr b =>
            cases b
            · have hmParam : m < m + 2 := by omega
              rw [show paramSubstVarMap π x = m by
                simp [paramSubstVarMap, hxk, hπ]]
              rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hmParam]
              rw [tupleWithFalseTrueParams_falseParam t, hInnerAt]
              simp [LocalRep.substApply, hπ]
            · have hmParam : m + 1 < m + 2 := by omega
              rw [show paramSubstVarMap π x = m + 1 by
                simp [paramSubstVarMap, hxk, hπ]]
              rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hmParam]
              rw [tupleWithFalseTrueParams_trueParam t, hInnerAt]
              simp [LocalRep.substApply, hπ]
      · by_cases hxEq : x = k
        · subst x
          have hInnerFalse : k < k + 2 := by omega
          change
            extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                (paramSubstVarMap π k) =
              extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.substApply π t))
                innerAux k
          rw [show paramSubstVarMap π k = m by simp [paramSubstVarMap]]
          rw [extendTupleAssignment_of_lt
            (tupleWithFalseTrueParams (LocalRep.substApply π t)) innerAux hInnerFalse]
          have hmParam : m < m + 2 := by omega
          rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hmParam]
          simp [tupleWithFalseTrueParams]
        · by_cases hxEq1 : x = k + 1
          · subst x
            have hInnerTrue : k + 1 < k + 2 := by omega
            change
              extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                  (paramSubstVarMap π (k + 1)) =
                extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.substApply π t))
                  innerAux (k + 1)
            rw [show paramSubstVarMap π (k + 1) = m + 1 by
              simp [paramSubstVarMap]]
            rw [extendTupleAssignment_of_lt
              (tupleWithFalseTrueParams (LocalRep.substApply π t)) innerAux hInnerTrue]
            have hmParam : m + 1 < m + 2 := by omega
            rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hmParam]
            simp [tupleWithFalseTrueParams]
          · have hxInnerAux : ¬ x < k + 2 := by omega
            have hMappedVar : paramSubstVarMap π x = m + 2 + x := by
              simp [paramSubstVarMap, hxk, hxEq, hxEq1]
            have hxOuterAux : ¬ m + 2 + x < m + 2 := by omega
            change
              extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                  (paramSubstVarMap π x) =
                extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.substApply π t))
                  innerAux x
            rw [hMappedVar]
            simp [extendTupleAssignment, hxInnerAux, hxOuterAux,
              outerAux]
  -- Finish the forward direction by applying the variable-map satisfaction lemma.
    refine ⟨outerAux, ?_⟩
    exact (formulaMapVars_satisfies_iff
      (paramSubstVarMap π) block.constraints outerAssign).2 hMapped
  · rintro ⟨outerAux, hOuter⟩
    let outerAssign := extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
    have hMapped :
        CSP.Formula.Satisfies block.constraints
          (fun x => outerAssign (paramSubstVarMap π x)) :=
      (formulaMapVars_satisfies_iff
        (paramSubstVarMap π) block.constraints outerAssign).1 hOuter
    let innerAux : SAT.Assignment := fun x => outerAssign (m + 2 + x)
    let innerAssign :=
      extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.substApply π t)) innerAux
    have hInner : CSP.Formula.Satisfies block.constraints innerAssign := by
      refine (FiniteSearch.formula_satisfies_iff_of_agree
        (φ := block.constraints)
        (a := innerAssign)
        (b := fun x => outerAssign (paramSubstVarMap π x)) ?_).2 hMapped
      intro x _hx
      by_cases hxk : x < k
      · have hxInnerParam : x < k + 2 := by omega
        have hInnerAt :
            tupleWithFalseTrueParams (LocalRep.substApply π t) ⟨x, hxInnerParam⟩ =
              LocalRep.substApply π t ⟨x, hxk⟩ := by
          simpa using tupleWithFalseTrueParams_of_lt (LocalRep.substApply π t) hxk
        change
          extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.substApply π t))
              innerAux x =
            extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
              (paramSubstVarMap π x)
        rw [extendTupleAssignment_of_lt
          (tupleWithFalseTrueParams (LocalRep.substApply π t)) innerAux hxInnerParam]
        cases hπ : π ⟨x, hxk⟩ with
        | inl j =>
            have hj : j.val < m := j.isLt
            have hjParam : j.val < m + 2 := by omega
            have hOuterAt : tupleWithFalseTrueParams t ⟨j.val, hjParam⟩ = t j := by
              simpa using tupleWithFalseTrueParams_of_lt t hj
            rw [show paramSubstVarMap π x = j.val by
              simp [paramSubstVarMap, hxk, hπ]]
            rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hjParam]
            rw [hInnerAt, hOuterAt]
            simp [LocalRep.substApply, hπ]
        | inr b =>
            cases b
            · have hmParam : m < m + 2 := by omega
              rw [show paramSubstVarMap π x = m by
                simp [paramSubstVarMap, hxk, hπ]]
              rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hmParam]
              rw [hInnerAt, tupleWithFalseTrueParams_falseParam t]
              simp [LocalRep.substApply, hπ]
            · have hmParam : m + 1 < m + 2 := by omega
              rw [show paramSubstVarMap π x = m + 1 by
                simp [paramSubstVarMap, hxk, hπ]]
              rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hmParam]
              rw [hInnerAt, tupleWithFalseTrueParams_trueParam t]
              simp [LocalRep.substApply, hπ]
      · by_cases hxEq : x = k
        · subst x
          have hInnerFalse : k < k + 2 := by omega
          change
            extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.substApply π t))
                innerAux k =
              extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                (paramSubstVarMap π k)
          rw [show paramSubstVarMap π k = m by simp [paramSubstVarMap]]
          rw [extendTupleAssignment_of_lt
            (tupleWithFalseTrueParams (LocalRep.substApply π t)) innerAux hInnerFalse]
          have hmParam : m < m + 2 := by omega
          rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hmParam]
          simp [tupleWithFalseTrueParams]
        · by_cases hxEq1 : x = k + 1
          · subst x
            have hInnerTrue : k + 1 < k + 2 := by omega
            change
              extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.substApply π t))
                  innerAux (k + 1) =
                extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                  (paramSubstVarMap π (k + 1))
            rw [show paramSubstVarMap π (k + 1) = m + 1 by
              simp [paramSubstVarMap]]
            rw [extendTupleAssignment_of_lt
              (tupleWithFalseTrueParams (LocalRep.substApply π t)) innerAux hInnerTrue]
            have hmParam : m + 1 < m + 2 := by omega
            rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hmParam]
            simp [tupleWithFalseTrueParams]
          · have hxInnerAux : ¬ x < k + 2 := by omega
            have hMappedVar : paramSubstVarMap π x = m + 2 + x := by
              simp [paramSubstVarMap, hxk, hxEq, hxEq1]
            have hxOuterAux : ¬ m + 2 + x < m + 2 := by omega
            change
              extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.substApply π t))
                  innerAux x =
                extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                  (paramSubstVarMap π x)
            rw [hMappedVar]
            simp [outerAssign, extendTupleAssignment, hxInnerAux, hxOuterAux, innerAux]
    have hR : LocalRep.substApply π t ∈ R :=
      (hBlock (LocalRep.substApply π t)).2 ⟨innerAux, hInner⟩
    exact (LocalRep.mem_substitute).2 hR

/--
Variable map for the left side of a LocalRep conjunction.  Left free variables
occupy the first `k` final variables; the shared parameters move to
`k+l,k+l+1`; left auxiliary variables move above the final free/parameter
zone.
-/
def paramConjLeftVarMap (k l x : Nat) : Nat :=
  if _h : x < k then x
  else if x = k then k + l
  else if x = k + 1 then k + l + 1
  else k + l + 2 + x

/--
Variable map for the right side of a LocalRep conjunction.  Right free
variables are placed after the left free variables.  Right auxiliary variables
start after the left formula's syntactic variable bound to avoid collisions.
-/
def paramConjRightVarMap (k l offset x : Nat) : Nat :=
  if _h : x < l then k + x
  else if x = l then k + l
  else if x = l + 1 then k + l + 1
  else k + l + 2 + offset + x

/-- Conjunction closure for parameter-aware LocalRep blocks. -/
noncomputable def paramConjBlock {Γ : CSP.BoolLanguage} {k l : Nat}
    (left : RelationFormula Γ (k + 2)) (right : RelationFormula Γ (l + 2)) :
    RelationFormula Γ (k + l + 2) where
  constraints :=
    formulaMapVars (paramConjLeftVarMap k l) left.constraints ++
      formulaMapVars
        (paramConjRightVarMap k l (formulaVarBound left.constraints))
        right.constraints
  notes := "LocalRep conjunction with shared false/true parameters."

theorem paramConjBlock_paramRepresents {Γ : CSP.BoolLanguage} {k l : Nat}
    {R : LocalRep.LogRel k} {T : LocalRep.LogRel l}
    {left : RelationFormula Γ (k + 2)} {right : RelationFormula Γ (l + 2)}
    (hLeft : ParamRepresents Γ R left)
    (hRight : ParamRepresents Γ T right) :
    ParamRepresents Γ (LocalRep.conjoin R T) (paramConjBlock left right) := by
  intro t
  let offset := formulaVarBound left.constraints
  let base := k + l + 2
  constructor
  · intro ht
    have hParts := (LocalRep.mem_conjoin).1 ht
    rcases (hLeft (LocalRep.splitLeft t)).1 hParts.1 with ⟨leftAux, hLeftSat⟩
    rcases (hRight (LocalRep.splitRight t)).1 hParts.2 with ⟨rightAux, hRightSat⟩
    let outerAux : SAT.Assignment := fun y =>
      if hBase : base ≤ y then
        if hLeftRange : y < base + offset then
          leftAux (y - base)
        else
          rightAux (y - (base + offset))
      else
        false
    let outerAssign := extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
    have hLeftMapped :
        CSP.Formula.Satisfies left.constraints
          (fun x => outerAssign (paramConjLeftVarMap k l x)) := by
      refine (FiniteSearch.formula_satisfies_iff_of_agree
        (φ := left.constraints)
        (a := fun x => outerAssign (paramConjLeftVarMap k l x))
        (b := extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitLeft t))
          leftAux) ?_).2 hLeftSat
      intro x hx
      by_cases hxk : x < k
      · have hFinal : x < k + l + 2 := by omega
        have hLeftParam : x < k + 2 := by omega
        change
          extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
              (paramConjLeftVarMap k l x) =
            extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitLeft t))
              leftAux x
        rw [show paramConjLeftVarMap k l x = x by simp [paramConjLeftVarMap, hxk]]
        rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hFinal]
        rw [extendTupleAssignment_of_lt
          (tupleWithFalseTrueParams (LocalRep.splitLeft t)) leftAux hLeftParam]
        have hFinalAt : tupleWithFalseTrueParams t ⟨x, hFinal⟩ = t ⟨x, by omega⟩ := by
          simpa using tupleWithFalseTrueParams_of_lt t (by omega : x < k + l)
        have hLeftAt :
            tupleWithFalseTrueParams (LocalRep.splitLeft t) ⟨x, hLeftParam⟩ =
              LocalRep.splitLeft t ⟨x, hxk⟩ := by
          simpa using tupleWithFalseTrueParams_of_lt (LocalRep.splitLeft t) hxk
        rw [hFinalAt, hLeftAt]
        simp [LocalRep.splitLeft]
      · by_cases hxEq : x = k
        · subst x
          have hFinal : k + l < k + l + 2 := by omega
          have hLeftParam : k < k + 2 := by omega
          change
            extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                (paramConjLeftVarMap k l k) =
              extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitLeft t))
                leftAux k
          rw [show paramConjLeftVarMap k l k = k + l by
            simp [paramConjLeftVarMap]]
          rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hFinal]
          rw [extendTupleAssignment_of_lt
            (tupleWithFalseTrueParams (LocalRep.splitLeft t)) leftAux hLeftParam]
          rw [tupleWithFalseTrueParams_falseParam (LocalRep.splitLeft t)]
          have hFinalFalse :
              tupleWithFalseTrueParams t ⟨k + l, hFinal⟩ = false := by
            simpa [Nat.add_assoc] using tupleWithFalseTrueParams_falseParam t
          exact hFinalFalse
        · by_cases hxEq1 : x = k + 1
          · subst x
            have hFinal : k + l + 1 < k + l + 2 := by omega
            have hLeftParam : k + 1 < k + 2 := by omega
            change
              extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                  (paramConjLeftVarMap k l (k + 1)) =
                extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitLeft t))
                  leftAux (k + 1)
            rw [show paramConjLeftVarMap k l (k + 1) = k + l + 1 by
              simp [paramConjLeftVarMap]]
            rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hFinal]
            rw [extendTupleAssignment_of_lt
              (tupleWithFalseTrueParams (LocalRep.splitLeft t)) leftAux hLeftParam]
            rw [tupleWithFalseTrueParams_trueParam (LocalRep.splitLeft t)]
            have hFinalTrue :
                tupleWithFalseTrueParams t ⟨k + l + 1, hFinal⟩ = true := by
              simpa [Nat.add_assoc] using tupleWithFalseTrueParams_trueParam t
            exact hFinalTrue
          · have hxLeftAux : ¬ x < k + 2 := by omega
            have hxBound : x < offset := var_lt_formulaVarBound hx
            have hMappedVar : paramConjLeftVarMap k l x = base + x := by
              simp [paramConjLeftVarMap, base, hxk, hxEq, hxEq1, Nat.add_assoc]
            have hOuterAux : ¬ base + x < k + l + 2 := by omega
            have hBase : base ≤ base + x := by omega
            have hLeftRange : base + x < base + offset := by omega
            change
              extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                  (paramConjLeftVarMap k l x) =
                extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitLeft t))
                  leftAux x
            rw [hMappedVar]
            simp [extendTupleAssignment, hxLeftAux, hOuterAux, outerAux, hBase, hLeftRange]
    have hRightMapped :
        CSP.Formula.Satisfies right.constraints
          (fun x => outerAssign (paramConjRightVarMap k l offset x)) := by
      refine (FiniteSearch.formula_satisfies_iff_of_agree
        (φ := right.constraints)
        (a := fun x => outerAssign (paramConjRightVarMap k l offset x))
        (b := extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitRight t))
          rightAux) ?_).2 hRightSat
      intro x hx
      by_cases hxl : x < l
      · have hFinalFree : k + x < k + l := by omega
        have hFinalParam : k + x < k + l + 2 := by omega
        have hRightParam : x < l + 2 := by omega
        change
          extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
              (paramConjRightVarMap k l offset x) =
            extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitRight t))
              rightAux x
        rw [show paramConjRightVarMap k l offset x = k + x by
          simp [paramConjRightVarMap, hxl]]
        rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hFinalParam]
        rw [extendTupleAssignment_of_lt
          (tupleWithFalseTrueParams (LocalRep.splitRight t)) rightAux hRightParam]
        have hFinalAt :
            tupleWithFalseTrueParams t ⟨k + x, hFinalParam⟩ =
              t ⟨k + x, hFinalFree⟩ := by
          simpa using tupleWithFalseTrueParams_of_lt t hFinalFree
        have hRightAt :
            tupleWithFalseTrueParams (LocalRep.splitRight t) ⟨x, hRightParam⟩ =
              LocalRep.splitRight t ⟨x, hxl⟩ := by
          simpa using tupleWithFalseTrueParams_of_lt (LocalRep.splitRight t) hxl
        rw [hFinalAt, hRightAt]
        apply congrArg t
        apply Fin.ext
        simp [Nat.add_comm]
      · by_cases hxEq : x = l
        · subst x
          have hFinal : k + l < k + l + 2 := by omega
          have hRightParam : l < l + 2 := by omega
          change
            extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                (paramConjRightVarMap k l offset l) =
              extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitRight t))
                rightAux l
          rw [show paramConjRightVarMap k l offset l = k + l by
            simp [paramConjRightVarMap]]
          rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hFinal]
          rw [extendTupleAssignment_of_lt
            (tupleWithFalseTrueParams (LocalRep.splitRight t)) rightAux hRightParam]
          rw [tupleWithFalseTrueParams_falseParam (LocalRep.splitRight t)]
          simpa [Nat.add_assoc] using tupleWithFalseTrueParams_falseParam t
        · by_cases hxEq1 : x = l + 1
          · subst x
            have hFinal : k + l + 1 < k + l + 2 := by omega
            have hRightParam : l + 1 < l + 2 := by omega
            change
              extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                  (paramConjRightVarMap k l offset (l + 1)) =
                extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitRight t))
                  rightAux (l + 1)
            rw [show paramConjRightVarMap k l offset (l + 1) = k + l + 1 by
              simp [paramConjRightVarMap]]
            rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hFinal]
            rw [extendTupleAssignment_of_lt
              (tupleWithFalseTrueParams (LocalRep.splitRight t)) rightAux hRightParam]
            rw [tupleWithFalseTrueParams_trueParam (LocalRep.splitRight t)]
            simpa [Nat.add_assoc] using tupleWithFalseTrueParams_trueParam t
          · have hxRightAux : ¬ x < l + 2 := by omega
            have hMappedVar :
                paramConjRightVarMap k l offset x = base + offset + x := by
              simp [paramConjRightVarMap, base, hxl, hxEq, hxEq1, Nat.add_assoc]
            have hOuterAux : ¬ base + offset + x < k + l + 2 := by omega
            have hBase : base ≤ base + offset + x := by omega
            have hNotLeftRange : ¬ base + offset + x < base + offset := by omega
            change
              extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                  (paramConjRightVarMap k l offset x) =
                extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitRight t))
                  rightAux x
            rw [hMappedVar]
            simp [extendTupleAssignment, hxRightAux, hOuterAux, outerAux, hBase,
              hNotLeftRange]
    refine ⟨outerAux, ?_⟩
    exact (CSP.Formula.satisfies_append _ _ outerAssign).2
      ⟨(formulaMapVars_satisfies_iff
          (paramConjLeftVarMap k l) left.constraints outerAssign).2 hLeftMapped,
        (formulaMapVars_satisfies_iff
          (paramConjRightVarMap k l offset) right.constraints outerAssign).2 hRightMapped⟩
  · rintro ⟨outerAux, hOuter⟩
    let outerAssign := extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
    have hSplit := (CSP.Formula.satisfies_append
      (formulaMapVars (paramConjLeftVarMap k l) left.constraints)
      (formulaMapVars (paramConjRightVarMap k l offset) right.constraints)
      outerAssign).1 hOuter
    have hLeftMapped :
        CSP.Formula.Satisfies left.constraints
          (fun x => outerAssign (paramConjLeftVarMap k l x)) :=
      (formulaMapVars_satisfies_iff
        (paramConjLeftVarMap k l) left.constraints outerAssign).1 hSplit.1
    have hRightMapped :
        CSP.Formula.Satisfies right.constraints
          (fun x => outerAssign (paramConjRightVarMap k l offset x)) :=
      (formulaMapVars_satisfies_iff
        (paramConjRightVarMap k l offset) right.constraints outerAssign).1 hSplit.2
    let leftAux : SAT.Assignment := fun x => outerAssign (base + x)
    let rightAux : SAT.Assignment := fun x => outerAssign (base + offset + x)
    have hLeftSat :
        CSP.Formula.Satisfies left.constraints
          (extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitLeft t))
            leftAux) := by
      refine (FiniteSearch.formula_satisfies_iff_of_agree
        (φ := left.constraints)
        (a := extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitLeft t))
          leftAux)
        (b := fun x => outerAssign (paramConjLeftVarMap k l x)) ?_).2 hLeftMapped
      intro x hx
      by_cases hxk : x < k
      · have hFinal : x < k + l + 2 := by omega
        have hLeftParam : x < k + 2 := by omega
        change
          extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitLeft t))
              leftAux x =
            extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
              (paramConjLeftVarMap k l x)
        rw [show paramConjLeftVarMap k l x = x by simp [paramConjLeftVarMap, hxk]]
        rw [extendTupleAssignment_of_lt
          (tupleWithFalseTrueParams (LocalRep.splitLeft t)) leftAux hLeftParam]
        rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hFinal]
        have hLeftAt :
            tupleWithFalseTrueParams (LocalRep.splitLeft t) ⟨x, hLeftParam⟩ =
              LocalRep.splitLeft t ⟨x, hxk⟩ := by
          simpa using tupleWithFalseTrueParams_of_lt (LocalRep.splitLeft t) hxk
        have hFinalAt : tupleWithFalseTrueParams t ⟨x, hFinal⟩ = t ⟨x, by omega⟩ := by
          simpa using tupleWithFalseTrueParams_of_lt t (by omega : x < k + l)
        rw [hLeftAt, hFinalAt]
        simp [LocalRep.splitLeft]
      · by_cases hxEq : x = k
        · subst x
          have hLeftParam : k < k + 2 := by omega
          have hFinal : k + l < k + l + 2 := by omega
          change
            extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitLeft t))
                leftAux k =
              extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                (paramConjLeftVarMap k l k)
          rw [show paramConjLeftVarMap k l k = k + l by
            simp [paramConjLeftVarMap]]
          rw [extendTupleAssignment_of_lt
            (tupleWithFalseTrueParams (LocalRep.splitLeft t)) leftAux hLeftParam]
          rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hFinal]
          rw [tupleWithFalseTrueParams_falseParam (LocalRep.splitLeft t)]
          simpa [Nat.add_assoc] using tupleWithFalseTrueParams_falseParam t
        · by_cases hxEq1 : x = k + 1
          · subst x
            have hLeftParam : k + 1 < k + 2 := by omega
            have hFinal : k + l + 1 < k + l + 2 := by omega
            change
              extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitLeft t))
                  leftAux (k + 1) =
                extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                  (paramConjLeftVarMap k l (k + 1))
            rw [show paramConjLeftVarMap k l (k + 1) = k + l + 1 by
              simp [paramConjLeftVarMap]]
            rw [extendTupleAssignment_of_lt
              (tupleWithFalseTrueParams (LocalRep.splitLeft t)) leftAux hLeftParam]
            rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hFinal]
            rw [tupleWithFalseTrueParams_trueParam (LocalRep.splitLeft t)]
            simpa [Nat.add_assoc] using tupleWithFalseTrueParams_trueParam t
          · have hxLeftAux : ¬ x < k + 2 := by omega
            have hMappedVar : paramConjLeftVarMap k l x = base + x := by
              simp [paramConjLeftVarMap, base, hxk, hxEq, hxEq1, Nat.add_assoc]
            have hOuterAux : ¬ base + x < k + l + 2 := by omega
            change
              extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitLeft t))
                  leftAux x =
                extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                  (paramConjLeftVarMap k l x)
            rw [hMappedVar]
            simp [outerAssign, extendTupleAssignment, hxLeftAux, hOuterAux, leftAux]
    have hRightSat :
        CSP.Formula.Satisfies right.constraints
          (extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitRight t))
            rightAux) := by
      refine (FiniteSearch.formula_satisfies_iff_of_agree
        (φ := right.constraints)
        (a := extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitRight t))
          rightAux)
        (b := fun x => outerAssign (paramConjRightVarMap k l offset x)) ?_).2 hRightMapped
      intro x hx
      by_cases hxl : x < l
      · have hFinalFree : k + x < k + l := by omega
        have hFinalParam : k + x < k + l + 2 := by omega
        have hRightParam : x < l + 2 := by omega
        change
          extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitRight t))
              rightAux x =
            extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
              (paramConjRightVarMap k l offset x)
        rw [show paramConjRightVarMap k l offset x = k + x by
          simp [paramConjRightVarMap, hxl]]
        rw [extendTupleAssignment_of_lt
          (tupleWithFalseTrueParams (LocalRep.splitRight t)) rightAux hRightParam]
        rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hFinalParam]
        have hRightAt :
            tupleWithFalseTrueParams (LocalRep.splitRight t) ⟨x, hRightParam⟩ =
              LocalRep.splitRight t ⟨x, hxl⟩ := by
          simpa using tupleWithFalseTrueParams_of_lt (LocalRep.splitRight t) hxl
        have hFinalAt :
            tupleWithFalseTrueParams t ⟨k + x, hFinalParam⟩ =
              t ⟨k + x, hFinalFree⟩ := by
          simpa using tupleWithFalseTrueParams_of_lt t hFinalFree
        rw [hRightAt, hFinalAt]
        apply congrArg t
        apply Fin.ext
        simp [Nat.add_comm]
      · by_cases hxEq : x = l
        · subst x
          have hRightParam : l < l + 2 := by omega
          have hFinal : k + l < k + l + 2 := by omega
          change
            extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitRight t))
                rightAux l =
              extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                (paramConjRightVarMap k l offset l)
          rw [show paramConjRightVarMap k l offset l = k + l by
            simp [paramConjRightVarMap]]
          rw [extendTupleAssignment_of_lt
            (tupleWithFalseTrueParams (LocalRep.splitRight t)) rightAux hRightParam]
          rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hFinal]
          rw [tupleWithFalseTrueParams_falseParam (LocalRep.splitRight t)]
          simpa [Nat.add_assoc] using tupleWithFalseTrueParams_falseParam t
        · by_cases hxEq1 : x = l + 1
          · subst x
            have hRightParam : l + 1 < l + 2 := by omega
            have hFinal : k + l + 1 < k + l + 2 := by omega
            change
              extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitRight t))
                  rightAux (l + 1) =
                extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                  (paramConjRightVarMap k l offset (l + 1))
            rw [show paramConjRightVarMap k l offset (l + 1) = k + l + 1 by
              simp [paramConjRightVarMap]]
            rw [extendTupleAssignment_of_lt
              (tupleWithFalseTrueParams (LocalRep.splitRight t)) rightAux hRightParam]
            rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) outerAux hFinal]
            rw [tupleWithFalseTrueParams_trueParam (LocalRep.splitRight t)]
            simpa [Nat.add_assoc] using tupleWithFalseTrueParams_trueParam t
          · have hxRightAux : ¬ x < l + 2 := by omega
            have hMappedVar :
                paramConjRightVarMap k l offset x = base + offset + x := by
              simp [paramConjRightVarMap, base, hxl, hxEq, hxEq1, Nat.add_assoc]
            have hOuterAux : ¬ base + offset + x < k + l + 2 := by omega
            change
              extendTupleAssignment (tupleWithFalseTrueParams (LocalRep.splitRight t))
                  rightAux x =
                extendTupleAssignment (tupleWithFalseTrueParams t) outerAux
                  (paramConjRightVarMap k l offset x)
            rw [hMappedVar]
            simp [outerAssign, extendTupleAssignment, hxRightAux, hOuterAux, rightAux]
    have hLeftRel : LocalRep.splitLeft t ∈ R :=
      (hLeft (LocalRep.splitLeft t)).2 ⟨leftAux, hLeftSat⟩
    have hRightRel : LocalRep.splitRight t ∈ T :=
      (hRight (LocalRep.splitRight t)).2 ⟨rightAux, hRightSat⟩
    exact (LocalRep.mem_conjoin).2 ⟨hLeftRel, hRightRel⟩

/-! ### Turning LocalRep derivations into proof-bearing SAT_C representation blocks -/

/--
Existence form of the interpretation from LocalRep `InRep` derivations to
parameter-aware primitive-positive blocks over `Γ`.

The two extra free variables are the false/true parameters used to realize
LocalRep's constant substitutions.
-/
theorem exists_paramBlockOfLanguageInRep {Γ : CSP.BoolLanguage} {k : Nat}
    {R : LocalRep.LogRel k}
    (h : LocalRep.InRep (LocalRepBridge.languageRelFinset Γ) k R) :
    ∃ block : RelationFormula Γ (k + 2), ParamRepresents Γ R block := by
  classical
  induction h with
  | base r hm =>
      rcases Finset.mem_image.mp hm with ⟨s, _hs, hsr⟩
      subst r
      exact ⟨localRepBaseParamBlock s, localRepBaseParamBlock_paramRepresents s⟩
  | existential R h ih =>
      rcases ih with ⟨block, hBlock⟩
      exact ⟨paramExistentialBlock block, paramExistentialBlock_paramRepresents hBlock⟩
  | conj R T hLeft hRight ihLeft ihRight =>
      rcases ihLeft with ⟨leftBlock, hLeftBlock⟩
      rcases ihRight with ⟨rightBlock, hRightBlock⟩
      exact ⟨paramConjBlock leftBlock rightBlock,
        paramConjBlock_paramRepresents hLeftBlock hRightBlock⟩
  | subst R π h ih =>
      rcases ih with ⟨block, hBlock⟩
      exact ⟨paramSubstBlock π block, paramSubstBlock_paramRepresents π hBlock⟩

/--
Choose a proof-bearing parameter-aware block from a LocalRep derivation.
This is noncomputable only because it packages the existence proof.
-/
noncomputable def paramBlockOfLanguageInRep {Γ : CSP.BoolLanguage} {k : Nat}
    {R : LocalRep.LogRel k}
    (h : LocalRep.InRep (LocalRepBridge.languageRelFinset Γ) k R) :
    { block : RelationFormula Γ (k + 2) // ParamRepresents Γ R block } :=
  ⟨Classical.choose (exists_paramBlockOfLanguageInRep h),
    Classical.choose_spec (exists_paramBlockOfLanguageInRep h)⟩

/-- Auxiliary assignment that pins the two LocalRep parameter variables. -/
def pinnedParamAux (k : Nat) (aux : SAT.Assignment) : SAT.Assignment :=
  fun x => if x = k then false else if x = k + 1 then true else aux x

theorem extendTupleAssignment_pinnedParamAux_eq {k : Nat}
    (t : CSP.BoolTuple k) (aux : SAT.Assignment) (x : Nat) :
    extendTupleAssignment t (pinnedParamAux k aux) x =
      extendTupleAssignment (tupleWithFalseTrueParams t) aux x := by
  by_cases hx : x < k
  · have hxParam : x < k + 2 := by omega
    rw [extendTupleAssignment_of_lt t (pinnedParamAux k aux) hx]
    rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) aux hxParam]
    exact (tupleWithFalseTrueParams_of_lt t hx).symm
  · by_cases hxEq : x = k
    · subst x
      have hParam : k < k + 2 := by omega
      rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) aux hParam]
      simp [extendTupleAssignment, pinnedParamAux, tupleWithFalseTrueParams]
    · by_cases hxEq1 : x = k + 1
      · subst x
        have hParam : k + 1 < k + 2 := by omega
        rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) aux hParam]
        simp [extendTupleAssignment, pinnedParamAux, tupleWithFalseTrueParams]
      · have hxParam : ¬ x < k + 2 := by omega
        simp [extendTupleAssignment, pinnedParamAux, hx, hxParam, hxEq, hxEq1]

/-- Add SAT_C pins for the false/true parameters of a LocalRep-derived block. -/
def relationFormulaOfParamBlockWithConstants {Γ : CSP.BoolLanguage}
    (R : CSP.BoolRel) (block : RelationFormula Γ (R.arity + 2)) :
    RelationFormula (satCWithConstantsLanguage Γ) R.arity where
  constraints :=
    liftOriginalFormulaToSatC block.constraints ++
      [pinFalseConstraint Γ R.arity, pinTrueConstraint Γ (R.arity + 1)]
  notes := "LocalRep parameter block with explicit SAT_C pins for false and true."

theorem relationFormulaOfParamBlockWithConstants_represents {Γ : CSP.BoolLanguage}
    {R : CSP.BoolRel} {RLocal : LocalRep.LogRel R.arity}
    {block : RelationFormula Γ (R.arity + 2)}
    (hBlock : ParamRepresents Γ RLocal block)
    (hEquiv : ∀ t : CSP.BoolTuple R.arity, R.Holds t ↔ t ∈ RLocal) :
    RepresentsRelation (satCWithConstantsLanguage Γ) R
      (relationFormulaOfParamBlockWithConstants R block) := by
  intro t
  constructor
  · intro hR
    rcases (hBlock t).1 ((hEquiv t).1 hR) with ⟨aux, hBlockSat⟩
    let actualAux := pinnedParamAux R.arity aux
    let actualAssign := extendTupleAssignment t actualAux
    refine ⟨actualAux, ?_⟩
    refine (CSP.Formula.satisfies_append _ _ actualAssign).2 ⟨?_, ?_⟩
    · rw [liftOriginalFormulaToSatC_satisfies_iff]
      refine (FiniteSearch.formula_satisfies_iff_of_agree
        (φ := block.constraints)
        (a := actualAssign)
        (b := extendTupleAssignment (tupleWithFalseTrueParams t) aux) ?_).2 hBlockSat
      intro x _hx
      exact extendTupleAssignment_pinnedParamAux_eq t aux x
    · intro c hc
      simp at hc
      rcases hc with rfl | rfl
      · exact (pinFalseConstraint_satisfies_iff Γ R.arity actualAssign).2 (by
          simp [actualAssign, actualAux, extendTupleAssignment, pinnedParamAux])
      · exact (pinTrueConstraint_satisfies_iff Γ (R.arity + 1) actualAssign).2 (by
          have hNot : ¬ R.arity + 1 < R.arity := by omega
          simp [actualAssign, actualAux, extendTupleAssignment, pinnedParamAux, hNot])
  · rintro ⟨aux, hSat⟩
    let actualAssign := extendTupleAssignment t aux
    have hParts := (CSP.Formula.satisfies_append
      (liftOriginalFormulaToSatC block.constraints)
      [pinFalseConstraint Γ R.arity, pinTrueConstraint Γ (R.arity + 1)]
      actualAssign).1 hSat
    have hFalse : actualAssign R.arity = false := by
      have hPin : CSP.Constraint.Satisfies (pinFalseConstraint Γ R.arity) actualAssign :=
        hParts.2 (pinFalseConstraint Γ R.arity) (by simp)
      exact (pinFalseConstraint_satisfies_iff Γ R.arity actualAssign).1 hPin
    have hTrue : actualAssign (R.arity + 1) = true := by
      have hPin : CSP.Constraint.Satisfies (pinTrueConstraint Γ (R.arity + 1)) actualAssign :=
        hParts.2 (pinTrueConstraint Γ (R.arity + 1)) (by simp)
      exact (pinTrueConstraint_satisfies_iff Γ (R.arity + 1) actualAssign).1 hPin
    have hBlockSat :
        CSP.Formula.Satisfies block.constraints
          (extendTupleAssignment (tupleWithFalseTrueParams t) actualAssign) := by
      rw [liftOriginalFormulaToSatC_satisfies_iff] at hParts
      refine (FiniteSearch.formula_satisfies_iff_of_agree
        (φ := block.constraints)
        (a := extendTupleAssignment (tupleWithFalseTrueParams t) actualAssign)
        (b := actualAssign) ?_).2 hParts.1
      intro x _hx
      by_cases hx : x < R.arity
      · have hxParam : x < R.arity + 2 := by omega
        rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) actualAssign hxParam]
        rw [tupleWithFalseTrueParams_of_lt t hx]
        simp [actualAssign, hx]
      · by_cases hxEq : x = R.arity
        · subst x
          have hParam : R.arity < R.arity + 2 := by omega
          rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) actualAssign hParam]
          rw [tupleWithFalseTrueParams_falseParam t]
          exact hFalse.symm
        · by_cases hxEq1 : x = R.arity + 1
          · subst x
            have hParam : R.arity + 1 < R.arity + 2 := by omega
            rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) actualAssign hParam]
            rw [tupleWithFalseTrueParams_trueParam t]
            exact hTrue.symm
          · have hxParam : ¬ x < R.arity + 2 := by omega
            simp [extendTupleAssignment, hxParam]
    exact (hEquiv t).2 ((hBlock t).2 ⟨actualAssign, hBlockSat⟩)

theorem oneInThreeRel_holds_iff_exactlyOneRel
    (t : CSP.BoolTuple CSP.Examples.oneInThreeRel.arity) :
    CSP.Examples.oneInThreeRel.Holds t ↔ t ∈ LocalRep.exactlyOneRel := by
  let u : CSP.BoolTuple 3 := t
  change
    u ∈ (Finset.univ.filter fun t : CSP.BoolTuple 3 =>
      CSP.Examples.trueCount3 t = 1) ↔ u ∈ LocalRep.exactlyOneRel
  simp only [LocalRep.exactlyOneRel, Finset.mem_filter, Finset.mem_univ, true_and,
    CSP.Examples.trueCount3]
  cases h0 : u ⟨0, by decide⟩ <;>
    cases h1 : u ⟨1, by decide⟩ <;>
      cases h2 : u ⟨2, by decide⟩ <;>
        simp

theorem notAllEqual3Rel_holds_iff_exactlyOne_or_complement
    (t : CSP.BoolTuple CSP.Examples.notAllEqual3Rel.arity) :
    CSP.Examples.notAllEqual3Rel.Holds t ↔
      t ∈ LocalRep.exactlyOneRel ∨ BoolTuple.complement t ∈ LocalRep.exactlyOneRel := by
  let u : CSP.BoolTuple 3 := t
  change
    u ∈ (Finset.univ.filter fun t : CSP.BoolTuple 3 =>
      ∃ i j : Fin 3, t i ≠ t j) ↔
      u ∈ LocalRep.exactlyOneRel ∨ BoolTuple.complement u ∈ LocalRep.exactlyOneRel
  simp only [LocalRep.exactlyOneRel, Finset.mem_filter, Finset.mem_univ, true_and,
    BoolTuple.complement]
  cases h0 : u 0 <;>
    cases h1 : u 1 <;>
      cases h2 : u 2
  · simp [h0, h1, h2]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]
  · simp [h0, h1, h2]
    exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by simp [h0, h2]⟩
  · simp [h0, h1, h2]
    exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by simp [h0, h1]⟩
  · simp [h0, h1, h2]
    exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by simp [h0, h1]⟩
  · simp [h0, h1, h2]
    exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by simp [h0, h1]⟩
  · simp [h0, h1, h2]
    exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by simp [h0, h1]⟩
  · simp [h0, h1, h2]
    exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by simp [h0, h2]⟩
  · simp [h0, h1, h2]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]

/-- Pointwise complement of a total SAT assignment. -/
def assignmentComplement (a : SAT.Assignment) : SAT.Assignment :=
  fun x => !a x

theorem constraint_satisfies_assignmentComplement {Γ : CSP.BoolLanguage}
    (hComp : AllRelationsSatisfy Γ IsComplementive) (c : CSP.Constraint Γ)
    (a : SAT.Assignment) :
    CSP.Constraint.Satisfies c a →
      CSP.Constraint.Satisfies c (assignmentComplement a) := by
  intro hSat
  change (Γ.relationOf c.symbol).Holds (c.assignmentTuple (assignmentComplement a))
  have hTuple :
      c.assignmentTuple (assignmentComplement a) =
        BoolTuple.complement (c.assignmentTuple a) := by
    funext i
    simp [CSP.Constraint.assignmentTuple, assignmentComplement, BoolTuple.complement]
  rw [hTuple]
  exact hComp c.symbol (c.assignmentTuple a) hSat

theorem formula_satisfies_assignmentComplement {Γ : CSP.BoolLanguage}
    (hComp : AllRelationsSatisfy Γ IsComplementive) (φ : SATFormula Γ)
    (a : SAT.Assignment) :
    CSP.Formula.Satisfies φ a → CSP.Formula.Satisfies φ (assignmentComplement a) := by
  intro hSat c hc
  exact constraint_satisfies_assignmentComplement hComp c a (hSat c hc)

theorem formula_satisfies_iff_tupleWithFalseTrueParams_of_agree {Γ : CSP.BoolLanguage}
    {k : Nat} {block : RelationFormula Γ (k + 2)}
    (t : CSP.BoolTuple k) (a : SAT.Assignment)
    (hFree : ∀ x : Nat, ∀ hx : x < k, a x = t ⟨x, hx⟩)
    (hFalse : a k = false) (hTrue : a (k + 1) = true) :
    CSP.Formula.Satisfies block.constraints a ↔
      CSP.Formula.Satisfies block.constraints
        (extendTupleAssignment (tupleWithFalseTrueParams t) a) := by
  refine FiniteSearch.formula_satisfies_iff_of_agree
    (φ := block.constraints)
    (a := a)
    (b := extendTupleAssignment (tupleWithFalseTrueParams t) a) ?_
  intro x _hx
  by_cases hxFree : x < k
  · have hxParam : x < k + 2 := by omega
    rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) a hxParam]
    rw [tupleWithFalseTrueParams_of_lt t hxFree]
    exact hFree x hxFree
  · by_cases hxFalse : x = k
    · subst x
      have hParam : k < k + 2 := by omega
      rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) a hParam]
      rw [tupleWithFalseTrueParams_falseParam t]
      exact hFalse
    · by_cases hxTrue : x = k + 1
      · subst x
        have hParam : k + 1 < k + 2 := by omega
        rw [extendTupleAssignment_of_lt (tupleWithFalseTrueParams t) a hParam]
        rw [tupleWithFalseTrueParams_trueParam t]
        exact hTrue
      · have hxParam : ¬ x < k + 2 := by omega
        simp [extendTupleAssignment, hxParam]

/-- Variable map for applying a represented XOR block to the two parameter variables. -/
def xorParamVarMap (k offset x : Nat) : Nat :=
  if x = 0 then k else if x = 1 then k + 1 else offset + x

theorem xorParamVarMap_zero (k offset : Nat) :
    xorParamVarMap k offset 0 = k := by
  simp [xorParamVarMap]

theorem xorParamVarMap_one (k offset : Nat) :
    xorParamVarMap k offset 1 = k + 1 := by
  simp [xorParamVarMap]

theorem xorParamVarMap_aux {k offset x : Nat} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    xorParamVarMap k offset x = offset + x := by
  simp [xorParamVarMap, hx0, hx1]

end Hardness
end Schaefer
end ComplexityReduction
