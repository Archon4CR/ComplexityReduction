import ComplexityReduction.CSP.Hardness.OneInThree.Part1

namespace ComplexityReduction
namespace CSP
namespace Hardness
namespace OneInThree
open SAT

theorem setClauseAux_aux0_same {φ : ThreeCNF} {i : Nat} {c : Clause}
    {source target : Assignment} :
    setClauseAux φ i c source target (aux0Var φ i) =
      gadgetAux0 (sourceClauseXValue source c) (sourceClauseYValue source c)
        (sourceClauseZValue source c) := by
  simp [setClauseAux,
    SAT.Clause.setVar_ne (aux0Var_ne_aux3Var (φ := φ) (i := i) (j := i)),
    SAT.Clause.setVar_ne (aux0Var_ne_aux2Var (φ := φ) (i := i) (j := i)),
    SAT.Clause.setVar_ne (aux0Var_ne_aux1Var (φ := φ) (i := i) (j := i))]

theorem setClauseAux_aux1_same {φ : ThreeCNF} {i : Nat} {c : Clause}
    {source target : Assignment} :
    setClauseAux φ i c source target (aux1Var φ i) =
      gadgetAux1 (sourceClauseXValue source c) (sourceClauseYValue source c)
        (sourceClauseZValue source c) := by
  simp [setClauseAux,
    SAT.Clause.setVar_ne (aux1Var_ne_aux3Var (φ := φ) (i := i) (j := i)),
    SAT.Clause.setVar_ne (aux1Var_ne_aux2Var (φ := φ) (i := i) (j := i))]

theorem setClauseAux_aux2_same {φ : ThreeCNF} {i : Nat} {c : Clause}
    {source target : Assignment} :
    setClauseAux φ i c source target (aux2Var φ i) =
      gadgetAux2 (sourceClauseXValue source c) (sourceClauseYValue source c)
        (sourceClauseZValue source c) := by
  simp [setClauseAux,
    SAT.Clause.setVar_ne (aux2Var_ne_aux3Var (φ := φ) (i := i) (j := i))]

theorem setClauseAux_aux3_same {φ : ThreeCNF} {i : Nat} {c : Clause}
    {source target : Assignment} :
    setClauseAux φ i c source target (aux3Var φ i) =
      gadgetAux3 (sourceClauseXValue source c) (sourceClauseYValue source c)
        (sourceClauseZValue source c) := by
  simp [setClauseAux]

theorem setClauseAux_aux0_of_ne {φ : ThreeCNF} {i j : Nat} {c : Clause}
    {source target : Assignment} (hij : i ≠ j) :
    setClauseAux φ j c source target (aux0Var φ i) = target (aux0Var φ i) := by
  have h0 : aux0Var φ i ≠ aux0Var φ j := by
    intro h
    exact hij (aux0Var_injective h)
  simp [setClauseAux, SAT.Clause.setVar_ne (aux0Var_ne_aux3Var (φ := φ)),
    SAT.Clause.setVar_ne (aux0Var_ne_aux2Var (φ := φ)),
    SAT.Clause.setVar_ne (aux0Var_ne_aux1Var (φ := φ)), SAT.Clause.setVar_ne h0]

theorem setClauseAux_aux1_of_ne {φ : ThreeCNF} {i j : Nat} {c : Clause}
    {source target : Assignment} (hij : i ≠ j) :
    setClauseAux φ j c source target (aux1Var φ i) = target (aux1Var φ i) := by
  have h1 : aux1Var φ i ≠ aux1Var φ j := by
    intro h
    exact hij (aux1Var_injective h)
  simp [setClauseAux, SAT.Clause.setVar_ne (aux1Var_ne_aux3Var (φ := φ)),
    SAT.Clause.setVar_ne (aux1Var_ne_aux2Var (φ := φ)), SAT.Clause.setVar_ne h1,
    SAT.Clause.setVar_ne (aux1Var_ne_aux0Var (φ := φ))]

theorem setClauseAux_aux2_of_ne {φ : ThreeCNF} {i j : Nat} {c : Clause}
    {source target : Assignment} (hij : i ≠ j) :
    setClauseAux φ j c source target (aux2Var φ i) = target (aux2Var φ i) := by
  have h2 : aux2Var φ i ≠ aux2Var φ j := by
    intro h
    exact hij (aux2Var_injective h)
  simp [setClauseAux, SAT.Clause.setVar_ne (aux2Var_ne_aux3Var (φ := φ)),
    SAT.Clause.setVar_ne h2, SAT.Clause.setVar_ne (aux2Var_ne_aux1Var (φ := φ)),
    SAT.Clause.setVar_ne (aux2Var_ne_aux0Var (φ := φ))]

theorem setClauseAux_aux3_of_ne {φ : ThreeCNF} {i j : Nat} {c : Clause}
    {source target : Assignment} (hij : i ≠ j) :
    setClauseAux φ j c source target (aux3Var φ i) = target (aux3Var φ i) := by
  have h3 : aux3Var φ i ≠ aux3Var φ j := by
    intro h
    exact hij (aux3Var_injective h)
  simp [setClauseAux, SAT.Clause.setVar_ne h3,
    SAT.Clause.setVar_ne (aux3Var_ne_aux2Var (φ := φ)),
    SAT.Clause.setVar_ne (aux3Var_ne_aux1Var (φ := φ)),
    SAT.Clause.setVar_ne (aux3Var_ne_aux0Var (φ := φ))]

theorem auxValues_setClauseAux_before {φ : ThreeCNF} {clauses : CNF}
    {source target : Assignment} {setAt start : Nat} {c : Clause}
    (hBefore : setAt < start) :
    AuxValues φ start clauses source (setClauseAux φ setAt c source target) ↔
      AuxValues φ start clauses source target := by
  induction clauses generalizing start with
  | nil =>
      simp [AuxValues]
  | cons head tail ih =>
      have hne : start ≠ setAt := ne_of_gt hBefore
      have h0 := setClauseAux_aux0_of_ne (φ := φ) (i := start) (j := setAt)
        (c := c) (source := source) (target := target) hne
      have h1 := setClauseAux_aux1_of_ne (φ := φ) (i := start) (j := setAt)
        (c := c) (source := source) (target := target) hne
      have h2 := setClauseAux_aux2_of_ne (φ := φ) (i := start) (j := setAt)
        (c := c) (source := source) (target := target) hne
      have h3 := setClauseAux_aux3_of_ne (φ := φ) (i := start) (j := setAt)
        (c := c) (source := source) (target := target) hne
      have htail := ih (start := start + 1)
        (Nat.lt_trans hBefore (Nat.lt_succ_self start))
      constructor
      · intro h
        exact ⟨by simpa [h0] using h.1,
          by simpa [h1] using h.2.1,
          by simpa [h2] using h.2.2.1,
          by simpa [h3] using h.2.2.2.1,
          htail.1 h.2.2.2.2⟩
      · intro h
        exact ⟨by simpa [h0] using h.1,
          by simpa [h1] using h.2.1,
          by simpa [h2] using h.2.2.1,
          by simpa [h3] using h.2.2.2.1,
          htail.2 h.2.2.2.2⟩

theorem extendAssignmentAux_falseVar {φ : ThreeCNF} {clauses : CNF}
    {i : Nat} {source base : Assignment} :
    extendAssignmentAux φ i clauses source base (falseVar φ) = base (falseVar φ) := by
  induction clauses generalizing i with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [extendAssignmentAux, setClauseAux_falseVar, ih]

theorem extendAssignmentAux_trueVar {φ : ThreeCNF} {clauses : CNF}
    {i : Nat} {source base : Assignment} :
    extendAssignmentAux φ i clauses source base (trueVar φ) = base (trueVar φ) := by
  induction clauses generalizing i with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [extendAssignmentAux, setClauseAux_trueVar, ih]

theorem extendAssignmentAux_source {φ : ThreeCNF} {clauses : CNF}
    {i x : Nat} {source base : Assignment} (hx : x < falseVar φ) :
    extendAssignmentAux φ i clauses source base x = base x := by
  induction clauses generalizing i with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [extendAssignmentAux, setClauseAux_source hx, ih]

theorem extendAssignmentAux_negVar {φ : ThreeCNF} {clauses : CNF}
    {i x : Nat} {source base : Assignment} (hx : x < falseVar φ) :
    extendAssignmentAux φ i clauses source base (negVar φ x) = base (negVar φ x) := by
  induction clauses generalizing i with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [extendAssignmentAux, setClauseAux_negVar hx, ih]

theorem extendAssignmentAux_auxValues {φ : ThreeCNF} {clauses : CNF}
    {i : Nat} {source base : Assignment} :
    AuxValues φ i clauses source (extendAssignmentAux φ i clauses source base) := by
  induction clauses generalizing i with
  | nil =>
      trivial
  | cons c cs ih =>
      constructor
      · simp [extendAssignmentAux, setClauseAux_aux0_same]
      · constructor
        · simp [extendAssignmentAux, setClauseAux_aux1_same]
        · constructor
          · simp [extendAssignmentAux, setClauseAux_aux2_same]
          · constructor
            · simp [extendAssignmentAux, setClauseAux_aux3_same]
            · exact (auxValues_setClauseAux_before
                (φ := φ) (clauses := cs) (source := source)
                (target := extendAssignmentAux φ (i + 1) cs source base)
                (setAt := i) (start := i + 1) (c := c)
                (Nat.lt_succ_self i)).2 (ih (i := i + 1))

theorem sourceVar_ne_falseVar {φ : ThreeCNF} {x : Nat} (hx : x < falseVar φ) :
    x ≠ falseVar φ := by
  exact ne_of_lt hx

theorem sourceVar_ne_trueVar {φ : ThreeCNF} {x : Nat} (hx : x < falseVar φ) :
    x ≠ trueVar φ := by
  unfold trueVar
  omega

theorem sourceVar_not_negVar {φ : ThreeCNF} {x : Nat} (hx : x < falseVar φ) :
    ¬(∃ z, z < falseVar φ ∧ x = negVar φ z) := by
  rintro ⟨z, _hz, hxz⟩
  unfold negVar at hxz
  omega

theorem extendBaseAssignment_falseVar (φ : ThreeCNF) (a : Assignment) :
    extendBaseAssignment φ a (falseVar φ) = false := by
  simp [extendBaseAssignment]

theorem extendBaseAssignment_trueVar (φ : ThreeCNF) (a : Assignment) :
    extendBaseAssignment φ a (trueVar φ) = true := by
  simp [extendBaseAssignment, trueVar]

theorem extendBaseAssignment_source {φ : ThreeCNF} {a : Assignment} {x : Nat}
    (hx : x < falseVar φ) :
    extendBaseAssignment φ a x = a x := by
  unfold extendBaseAssignment
  rw [if_neg (sourceVar_ne_falseVar hx), if_neg (sourceVar_ne_trueVar hx),
    dif_neg (sourceVar_not_negVar hx)]

theorem extendBaseAssignment_negVar {φ : ThreeCNF} {a : Assignment} {x : Nat}
    (hx : x < falseVar φ) :
    extendBaseAssignment φ a (negVar φ x) = !(a x) := by
  have hExists : ∃ z, z < falseVar φ ∧ negVar φ x = negVar φ z := ⟨x, hx, rfl⟩
  unfold extendBaseAssignment
  rw [if_neg negVar_ne_falseVar, if_neg negVar_ne_trueVar]
  rw [dif_pos hExists]
  have hxchoose : (Classical.choose hExists) = x := by
    have hspec := Classical.choose_spec hExists
    rcases hspec with ⟨_, hEq⟩
    exact (negVar_injective hEq.symm)
  simp [hxchoose]

theorem extendAssignment_falseVar (φ : ThreeCNF) (a : Assignment) :
    extendAssignment φ a (falseVar φ) = false := by
  simp [extendAssignment, extendAssignmentAux_falseVar, extendBaseAssignment_falseVar]

theorem extendAssignment_trueVar (φ : ThreeCNF) (a : Assignment) :
    extendAssignment φ a (trueVar φ) = true := by
  simp [extendAssignment, extendAssignmentAux_trueVar, extendBaseAssignment_trueVar]

theorem extendAssignment_source {φ : ThreeCNF} {a : Assignment} {x : Nat}
    (hx : x < falseVar φ) :
    extendAssignment φ a x = a x := by
  simp [extendAssignment, extendAssignmentAux_source hx, extendBaseAssignment_source hx]

theorem extendAssignment_negVar {φ : ThreeCNF} {a : Assignment} {x : Nat}
    (hx : x < falseVar φ) :
    extendAssignment φ a (negVar φ x) = !(a x) := by
  simp [extendAssignment, extendAssignmentAux_negVar hx, extendBaseAssignment_negVar hx]

theorem extendAssignment_litVar {φ : ThreeCNF} {a : Assignment}
    {l : Literal} (hl : l.var < falseVar φ) :
    extendAssignment φ a (litVar φ l) = l.eval a := by
  cases l with
  | mk v neg =>
      cases neg <;>
        simp [litVar, Literal.eval, extendAssignment_source (φ := φ) (a := a) hl,
          extendAssignment_negVar (φ := φ) (a := a) hl]

theorem extendAssignment_litNegVar {φ : ThreeCNF} {a : Assignment}
    {l : Literal} (hl : l.var < falseVar φ) :
    extendAssignment φ a (litNegVar φ l) = !(l.eval a) := by
  cases l with
  | mk v neg =>
      cases neg <;>
        simp [litNegVar, Literal.eval, extendAssignment_source (φ := φ) (a := a) hl,
          extendAssignment_negVar (φ := φ) (a := a) hl]

theorem sourceComplementConstraints_extend {φ : ThreeCNF} {a : Assignment} :
    Formula.Satisfies (sourceComplementConstraints φ) (extendAssignment φ a) := by
  unfold sourceComplementConstraints
  exact sourceComplementConstraintsAux_extend
    (extendAssignment_falseVar φ a)
    (by
      intro x hx
      rw [extendAssignment_negVar (φ := φ) (a := a) hx,
        extendAssignment_source (φ := φ) (a := a) hx])

theorem clausesToFormulaAux_extend {φ : ThreeCNF} {a : Assignment}
    (hSat : φ.Satisfies a) :
    Formula.Satisfies (clausesToFormulaAux φ 0 φ.clauses) (extendAssignment φ a) := by
  have hVars : ∀ c ∈ φ.clauses, ∀ l ∈ c, l.var < falseVar φ := by
    intro c hc
    exact CNF.clause_vars_lt_varBound hc
  exact clausesToFormulaAux_extend_of_auxValues φ.isThree
    (extendAssignment_falseVar φ a)
    (extendAssignment_trueVar φ a)
    (by
      intro c hc l hl
      exact extendAssignment_litVar (φ := φ) (a := a) (hVars c hc l hl))
    (by
      intro c hc l hl
      exact extendAssignment_litNegVar (φ := φ) (a := a) (hVars c hc l hl))
    (by
      simpa [extendAssignment] using
        (extendAssignmentAux_auxValues
          (φ := φ) (clauses := φ.clauses) (i := 0)
          (source := a) (base := extendBaseAssignment φ a)))
    hSat

theorem threeCNFToOneInThreeFormula_extend (φ : ThreeCNF) :
    φ.Satisfiable → Formula.Satisfiable (threeCNFToOneInThreeFormula φ) := by
  rintro ⟨a, hSat⟩
  refine ⟨extendAssignment φ a, ?_⟩
  have hAnchor : Formula.Satisfies (anchorConstraints φ) (extendAssignment φ a) :=
    anchorConstraints_extend (extendAssignment_falseVar φ a) (extendAssignment_trueVar φ a)
  have hSource : Formula.Satisfies (sourceComplementConstraints φ) (extendAssignment φ a) :=
    sourceComplementConstraints_extend (φ := φ) (a := a)
  have hClauses :
      Formula.Satisfies (clausesToFormulaAux φ 0 φ.clauses) (extendAssignment φ a) :=
    clausesToFormulaAux_extend (φ := φ) (a := a) hSat
  intro c hc
  have hCases :
      c ∈ anchorConstraints φ ∨
        c ∈ sourceComplementConstraints φ ∨
          c ∈ clausesToFormulaAux φ 0 φ.clauses := by
    simpa [threeCNFToOneInThreeFormula, List.append_assoc] using hc
  rcases hCases with hA | hS | hC
  · exact hAnchor c hA
  · exact hSource c hS
  · exact hClauses c hC

theorem threeCNFToOneInThreeFormula_satisfiable_iff (φ : ThreeCNF) :
    Formula.Satisfiable (threeCNFToOneInThreeFormula φ) ↔ φ.Satisfiable :=
  ⟨threeCNFToOneInThreeFormula_project φ, threeCNFToOneInThreeFormula_extend φ⟩

theorem oneConstraint_encodedLength (x y z : Nat) :
    (Encoding.encodeConstraint (oneConstraint x y z)).length = x + y + z + 8 := by
  rw [Encoding.encodeConstraint_length]
  change 2 +
      ((List.ofFn (fun i : Fin 3 =>
        (match i.val with | 0 => x | 1 => y | _ => z) + 2)).sum) =
    x + y + z + 8
  conv_lhs =>
    enter [2, 1]
    rw [List.ofFn_succ]
    rw [List.ofFn_succ]
    rw [List.ofFn_succ]
  simp
  omega

theorem complementPairConstraints_encodedLength_le {φ : ThreeCNF} {x nx B : Nat}
    (hx : x ≤ B) (hnx : nx ≤ B) (hFalse : falseVar φ ≤ B) :
    (Encoding.encodeFormula (complementPairConstraints φ x nx)).length ≤
      3 * B + 8 := by
  simp [complementPairConstraints, Encoding.encodeFormula, oneConstraint_encodedLength]
  omega

theorem sourceComplementConstraintsAux_encodedLength_le {φ : ThreeCNF} {n B : Nat}
    (hN : ∀ x, x < n → x ≤ B)
    (hNeg : ∀ x, x < n → negVar φ x ≤ B)
    (hFalse : falseVar φ ≤ B) :
    (Encoding.encodeFormula (sourceComplementConstraintsAux φ n)).length ≤
      n * (3 * B + 8) := by
  induction n with
  | zero =>
      simp [sourceComplementConstraintsAux]
  | succ n ih =>
      have hHead := complementPairConstraints_encodedLength_le
        (φ := φ) (x := n) (nx := negVar φ n) (B := B)
        (hN n (Nat.lt_succ_self n)) (hNeg n (Nat.lt_succ_self n)) hFalse
      have hTail := ih
        (by intro x hx; exact hN x (Nat.lt_trans hx (Nat.lt_succ_self n)))
        (by intro x hx; exact hNeg x (Nat.lt_trans hx (Nat.lt_succ_self n)))
      simp [sourceComplementConstraintsAux, Encoding.encodeFormula, List.length_flatMap] at hHead hTail ⊢
      calc
        (List.map (fun a => (Encoding.encodeConstraint a).length)
              (complementPairConstraints φ n (negVar φ n))).sum +
            (List.map (fun a => (Encoding.encodeConstraint a).length)
              (sourceComplementConstraintsAux φ n)).sum
            ≤ (3 * B + 8) + n * (3 * B + 8) :=
          Nat.add_le_add hHead hTail
        _ = (n + 1) * (3 * B + 8) := by ring

theorem clauseGadgetFormula_encodedLength_le {φ : ThreeCNF} {i B x nx y ny z : Nat}
    (hnx : nx ≤ B) (hny : ny ≤ B) (hz : z ≤ B)
    (hAux0 : aux0Var φ i ≤ B) (hAux1 : aux1Var φ i ≤ B)
    (hAux2 : aux2Var φ i ≤ B) (hAux3 : aux3Var φ i ≤ B) :
    (Encoding.encodeFormula (clauseGadgetFormula φ i x nx y ny z)).length ≤
      3 * (3 * B + 8) := by
  simp [clauseGadgetFormula, Encoding.encodeFormula, oneConstraint_encodedLength]
  omega

theorem literal_var_lt_encodeClause_length {c : Clause} {l : Literal} (hl : l ∈ c) :
    l.var < (SAT.ThreeSATEncoding.encodeClause c).length := by
  have hmem : (SAT.ThreeSATEncoding.encodeLiteral l).length ∈
      (c.map fun x => (SAT.ThreeSATEncoding.encodeLiteral x).length) := by
    exact List.mem_map.mpr ⟨l, hl, rfl⟩
  have hle : (SAT.ThreeSATEncoding.encodeLiteral l).length ≤
      (c.map fun x => (SAT.ThreeSATEncoding.encodeLiteral x).length).sum :=
    List.le_sum_of_mem hmem
  simp [SAT.ThreeSATEncoding.encodeClause, SAT.ThreeSATEncoding.encodeLiteral,
    SAT.ThreeSATEncoding.encodeNat, EncodedType.nat, List.length_flatMap] at hle ⊢
  omega

theorem threeCNF_varBound_le_inputSize (φ : ThreeCNF) :
    falseVar φ ≤ SAT.threeSATDecisionProblem.Instance.inputSize φ := by
  unfold falseVar
  change CNF.varBound φ.clauses ≤ (SAT.ThreeSATEncoding.encodeThreeCNF φ).length
  exact CNF.varBound_le_of_vars_lt φ.clauses (SAT.ThreeSATEncoding.encodeThreeCNF φ).length
    (by
      intro c hc l hl
      have hLit : l.var < (SAT.ThreeSATEncoding.encodeClause c).length :=
        literal_var_lt_encodeClause_length (c := c) hl
      have hBlock :
          (SAT.ThreeSATEncoding.encodeClause c).length ≤
            (SAT.ThreeSATEncoding.encodeThreeCNF φ).length := by
        unfold SAT.ThreeSATEncoding.encodeThreeCNF
        rw [List.length_flatMap]
        exact List.le_sum_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)
      exact Nat.lt_of_lt_of_le hLit hBlock)

theorem cnf_clauseLength_le_encodeCNF (clauses : CNF) :
    clauses.length ≤ (SAT.ThreeSATEncoding.encodeCNF clauses).length := by
  induction clauses with
  | nil =>
      simp [SAT.ThreeSATEncoding.encodeCNF]
  | cons c cs ih =>
      have hc : 1 ≤ (SAT.ThreeSATEncoding.encodeClause c).length := by
        simp [SAT.ThreeSATEncoding.encodeClause]
      rw [SAT.ThreeSATEncoding.encodeCNF_cons, List.length_append, List.length_cons]
      omega

theorem threeCNF_clauseLength_le_inputSize (φ : ThreeCNF) :
    φ.clauses.length ≤ SAT.threeSATDecisionProblem.Instance.inputSize φ := by
  change φ.clauses.length ≤ (SAT.ThreeSATEncoding.encodeThreeCNF φ).length
  simpa [SAT.ThreeSATEncoding.encodeThreeCNF_eq_encodeCNF] using
    cnf_clauseLength_le_encodeCNF φ.clauses

theorem litVar_le_of_source_bound {φ : ThreeCNF} {B : Nat}
    (hBase : falseVar φ ≤ B) (hNeg : ∀ x, x < falseVar φ → negVar φ x ≤ B)
    {l : Literal} (hl : l.var < falseVar φ) :
    litVar φ l ≤ B := by
  cases l with
  | mk v neg =>
      cases neg
      · simpa [litVar] using Nat.le_trans (Nat.le_of_lt hl) hBase
      · simpa [litVar] using hNeg v hl

theorem litNegVar_le_of_source_bound {φ : ThreeCNF} {B : Nat}
    (hBase : falseVar φ ≤ B) (hNeg : ∀ x, x < falseVar φ → negVar φ x ≤ B)
    {l : Literal} (hl : l.var < falseVar φ) :
    litNegVar φ l ≤ B := by
  cases l with
  | mk v neg =>
      cases neg
      · simpa [litNegVar] using hNeg v hl
      · simpa [litNegVar] using Nat.le_trans (Nat.le_of_lt hl) hBase

theorem clauseToFormula_encodedLength_le {φ : ThreeCNF} {c : Clause} (hlen : c.length ≤ 3)
    {i B : Nat}
    (hFalse : falseVar φ ≤ B) (hTrue : trueVar φ ≤ B)
    (hAux0 : aux0Var φ i ≤ B) (hAux1 : aux1Var φ i ≤ B)
    (hAux2 : aux2Var φ i ≤ B) (hAux3 : aux3Var φ i ≤ B)
    (hLit : ∀ l ∈ c, litVar φ l ≤ B)
    (hLitNeg : ∀ l ∈ c, litNegVar φ l ≤ B) :
    (Encoding.encodeFormula (clauseToFormula φ i c)).length ≤
      3 * (3 * B + 8) := by
  cases c with
  | nil =>
      simp [clauseToFormula, oneConstraint_encodedLength]
      omega
  | cons l₁ rest =>
      cases rest with
      | nil =>
          have hBlock := clauseGadgetFormula_encodedLength_le
            (φ := φ) (i := i) (B := B)
            (x := litVar φ l₁) (nx := litNegVar φ l₁)
            (y := falseVar φ) (ny := trueVar φ) (z := falseVar φ)
            (hLitNeg l₁ (by simp)) hTrue hFalse hAux0 hAux1 hAux2 hAux3
          simpa [clauseToFormula] using hBlock
      | cons l₂ rest₂ =>
          cases rest₂ with
          | nil =>
              have hBlock := clauseGadgetFormula_encodedLength_le
                (φ := φ) (i := i) (B := B)
                (x := litVar φ l₁) (nx := litNegVar φ l₁)
                (y := litVar φ l₂) (ny := litNegVar φ l₂) (z := falseVar φ)
                (hLitNeg l₁ (by simp)) (hLitNeg l₂ (by simp)) hFalse
                hAux0 hAux1 hAux2 hAux3
              simpa [clauseToFormula] using hBlock
          | cons l₃ rest₃ =>
              cases rest₃ with
              | nil =>
                  have hBlock := clauseGadgetFormula_encodedLength_le
                    (φ := φ) (i := i) (B := B)
                    (x := litVar φ l₁) (nx := litNegVar φ l₁)
                    (y := litVar φ l₂) (ny := litNegVar φ l₂) (z := litVar φ l₃)
                    (hLitNeg l₁ (by simp)) (hLitNeg l₂ (by simp))
                    (hLit l₃ (by simp)) hAux0 hAux1 hAux2 hAux3
                  simpa [clauseToFormula] using hBlock
              | cons _ _ =>
                  simp at hlen

theorem clausesToFormulaAux_encodedLength_le {φ : ThreeCNF} {clauses : CNF}
    (hThree : CNF.IsThreeCNF clauses) {i B : Nat}
    (hAux0 : ∀ j, i ≤ j → j < i + clauses.length → aux0Var φ j ≤ B)
    (hAux1 : ∀ j, i ≤ j → j < i + clauses.length → aux1Var φ j ≤ B)
    (hAux2 : ∀ j, i ≤ j → j < i + clauses.length → aux2Var φ j ≤ B)
    (hAux3 : ∀ j, i ≤ j → j < i + clauses.length → aux3Var φ j ≤ B)
    (hFalse : falseVar φ ≤ B) (hTrue : trueVar φ ≤ B)
    (hLit : ∀ c ∈ clauses, ∀ l ∈ c, litVar φ l ≤ B)
    (hLitNeg : ∀ c ∈ clauses, ∀ l ∈ c, litNegVar φ l ≤ B) :
    (Encoding.encodeFormula (clausesToFormulaAux φ i clauses)).length ≤
      3 * clauses.length * (3 * B + 8) := by
  induction clauses generalizing i with
  | nil =>
      simp [clausesToFormulaAux]
  | cons c cs ih =>
      have hcLen : c.length ≤ 3 := hThree c (by simp)
      have hcsThree : CNF.IsThreeCNF cs := by
        intro d hd
        exact hThree d (by simp [hd])
      have hAux0Head : aux0Var φ i ≤ B := hAux0 i (Nat.le_refl i) (by simp)
      have hAux1Head : aux1Var φ i ≤ B := hAux1 i (Nat.le_refl i) (by simp)
      have hAux2Head : aux2Var φ i ≤ B := hAux2 i (Nat.le_refl i) (by simp)
      have hAux3Head : aux3Var φ i ≤ B := hAux3 i (Nat.le_refl i) (by simp)
      have hBlock := clauseToFormula_encodedLength_le (φ := φ) (c := c) hcLen
        (i := i) (B := B) hFalse hTrue hAux0Head hAux1Head hAux2Head hAux3Head
        (by intro l hl; exact hLit c (by simp) l hl)
        (by intro l hl; exact hLitNeg c (by simp) l hl)
      have hTail := ih hcsThree (i := i + 1)
        (by
          intro j hjLower hjUpper
          exact hAux0 j (Nat.le_trans (Nat.le_succ i) hjLower)
            (by simp at hjUpper ⊢; omega))
        (by
          intro j hjLower hjUpper
          exact hAux1 j (Nat.le_trans (Nat.le_succ i) hjLower)
            (by simp at hjUpper ⊢; omega))
        (by
          intro j hjLower hjUpper
          exact hAux2 j (Nat.le_trans (Nat.le_succ i) hjLower)
            (by simp at hjUpper ⊢; omega))
        (by
          intro j hjLower hjUpper
          exact hAux3 j (Nat.le_trans (Nat.le_succ i) hjLower)
            (by simp at hjUpper ⊢; omega))
        (by intro d hd l hl; exact hLit d (by simp [hd]) l hl)
        (by intro d hd l hl; exact hLitNeg d (by simp [hd]) l hl)
      simp [clausesToFormulaAux, Encoding.encodeFormula, List.length_flatMap] at hBlock hTail ⊢
      calc
        (List.map (fun a => (Encoding.encodeConstraint a).length) (clauseToFormula φ i c)).sum +
            (List.map (fun a => (Encoding.encodeConstraint a).length)
              (clausesToFormulaAux φ (i + 1) cs)).sum
            ≤ 3 * (3 * B + 8) + 3 * cs.length * (3 * B + 8) :=
          Nat.add_le_add hBlock hTail
        _ = 3 * (cs.length + 1) * (3 * B + 8) := by ring

theorem threeCNFToOneInThreeFormula_encodedLength_le (φ : ThreeCNF) :
    (Encoding.encodeFormula (threeCNFToOneInThreeFormula φ)).length ≤
      200 * (SAT.threeSATDecisionProblem.Instance.inputSize φ + 1) ^ 2 := by
  let n := SAT.threeSATDecisionProblem.Instance.inputSize φ
  let B := 6 * (n + 1)
  have hFalseInput : falseVar φ ≤ n := by
    unfold n
    exact threeCNF_varBound_le_inputSize φ
  have hClauseLen : φ.clauses.length ≤ n := by
    unfold n
    exact threeCNF_clauseLength_le_inputSize φ
  have hFalse : falseVar φ ≤ B := by unfold B; omega
  have hTrue : trueVar φ ≤ B := by unfold B trueVar; omega
  have hNeg : ∀ x, x < falseVar φ → negVar φ x ≤ B := by
    intro x hx
    unfold B negVar
    have hxle : x ≤ n := Nat.le_trans (Nat.le_of_lt hx) hFalseInput
    omega
  have hSourceIndex : ∀ x, x < falseVar φ → x ≤ B := by
    intro x hx
    exact Nat.le_trans (Nat.le_of_lt hx) hFalse
  have hSource := sourceComplementConstraintsAux_encodedLength_le
    (φ := φ) (n := falseVar φ) (B := B)
    hSourceIndex hNeg hFalse
  have hAux0 : ∀ j, 0 ≤ j → j < 0 + φ.clauses.length → aux0Var φ j ≤ B := by
    intro j _ hj
    unfold B aux0Var auxBase
    have hjlt : j < φ.clauses.length := by simpa using hj
    have hjle : j ≤ n := Nat.le_trans (Nat.le_of_lt hjlt) hClauseLen
    omega
  have hAux1 : ∀ j, 0 ≤ j → j < 0 + φ.clauses.length → aux1Var φ j ≤ B := by
    intro j _ hj
    unfold B aux1Var auxBase
    have hjlt : j < φ.clauses.length := by simpa using hj
    have hjle : j ≤ n := Nat.le_trans (Nat.le_of_lt hjlt) hClauseLen
    omega
  have hAux2 : ∀ j, 0 ≤ j → j < 0 + φ.clauses.length → aux2Var φ j ≤ B := by
    intro j _ hj
    unfold B aux2Var auxBase
    have hjlt : j < φ.clauses.length := by simpa using hj
    have hjle : j ≤ n := Nat.le_trans (Nat.le_of_lt hjlt) hClauseLen
    omega
  have hAux3 : ∀ j, 0 ≤ j → j < 0 + φ.clauses.length → aux3Var φ j ≤ B := by
    intro j _ hj
    unfold B aux3Var auxBase
    have hjlt : j < φ.clauses.length := by simpa using hj
    have hjle : j ≤ n := Nat.le_trans (Nat.le_of_lt hjlt) hClauseLen
    omega
  have hLit : ∀ c ∈ φ.clauses, ∀ l ∈ c, litVar φ l ≤ B := by
    intro c hc l hl
    exact litVar_le_of_source_bound hFalse hNeg (CNF.clause_vars_lt_varBound hc l hl)
  have hLitNeg : ∀ c ∈ φ.clauses, ∀ l ∈ c, litNegVar φ l ≤ B := by
    intro c hc l hl
    exact litNegVar_le_of_source_bound hFalse hNeg (CNF.clause_vars_lt_varBound hc l hl)
  have hClauses := clausesToFormulaAux_encodedLength_le φ.isThree
    (φ := φ) (i := 0) (B := B) hAux0 hAux1 hAux2 hAux3 hFalse hTrue hLit hLitNeg
  have hAnchor : (Encoding.encodeFormula (anchorConstraints φ)).length ≤ 3 * B + 8 := by
    simp [anchorConstraints, Encoding.encodeFormula, oneConstraint_encodedLength]
    omega
  simp [threeCNFToOneInThreeFormula, sourceComplementConstraints, Encoding.encodeFormula,
    List.length_flatMap] at hSource hClauses hAnchor ⊢
  have hMain :
      (3 * B + 8) + falseVar φ * (3 * B + 8) +
          3 * φ.clauses.length * (3 * B + 8) ≤ 200 * (n + 1) ^ 2 := by
    unfold B
    let A := n + 1
    have hfactor : 3 * (6 * A) + 8 ≤ 26 * A := by omega
    have hsum : 1 + falseVar φ + 3 * φ.clauses.length ≤ 7 * A := by
      unfold A
      omega
    calc
      (3 * (6 * A) + 8) + falseVar φ * (3 * (6 * A) + 8) +
          3 * φ.clauses.length * (3 * (6 * A) + 8)
          = (1 + falseVar φ + 3 * φ.clauses.length) * (3 * (6 * A) + 8) := by ring
      _ ≤ 7 * A * (26 * A) := Nat.mul_le_mul hsum hfactor
      _ = 182 * A ^ 2 := by ring
      _ ≤ 200 * A ^ 2 := by omega
  calc
    (List.map (fun a => (Encoding.encodeConstraint a).length) (anchorConstraints φ)).sum +
        ((List.map (fun a => (Encoding.encodeConstraint a).length)
              (sourceComplementConstraintsAux φ (falseVar φ))).sum +
          (List.map (fun a => (Encoding.encodeConstraint a).length)
              (clausesToFormulaAux φ 0 φ.clauses)).sum)
        ≤ (3 * B + 8) + falseVar φ * (3 * B + 8) +
            3 * φ.clauses.length * (3 * B + 8) := by
      omega
    _ ≤ 200 * (n + 1) ^ 2 := hMain

theorem threeCNFToOneInThreeFormula_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : ThreeCNF => SAT.threeSATDecisionProblem.Instance.inputSize φ)
      (fun ψ : Formula Examples.oneInThreeLanguage =>
        (boolCSPDecisionProblem Examples.oneInThreeLanguage).Instance.inputSize ψ)
      threeCNFToOneInThreeFormula :=
  PolynomialSizeBound.intro_with 2 800 200 (by
    intro φ
    have h := threeCNFToOneInThreeFormula_encodedLength_le φ
    calc
      (boolCSPDecisionProblem Examples.oneInThreeLanguage).Instance.inputSize
          (threeCNFToOneInThreeFormula φ)
          ≤ 200 * (SAT.threeSATDecisionProblem.Instance.inputSize φ + 1) ^ 2 := by
        simpa [EncodedType.inputSize, boolCSPDecisionProblem, boolCSPSatLike, formulaEncodedType]
          using h
      _ ≤ 200 *
          (4 * (SAT.threeSATDecisionProblem.Instance.inputSize φ) ^ 2 + 1) := by
        exact Nat.mul_le_mul_left 200
          (Formula.add_one_sq_le_four_sq_add_one
            (SAT.threeSATDecisionProblem.Instance.inputSize φ))
      _ = 800 * (SAT.threeSATDecisionProblem.Instance.inputSize φ) ^ 2 + 200 := by
        ring)

noncomputable def threeSATToOneInThreeReduction :
    SemanticReduction SAT.threeSATDecisionProblem
      Examples.oneInThreeDecisionProblem where
  f := threeCNFToOneInThreeFormula
  correct := by
    intro φ
    exact (threeCNFToOneInThreeFormula_satisfiable_iff φ).symm

noncomputable def threeSATToOneInThreeCostedReduction :
    CostedReduction SAT.threeSATDecisionProblem Examples.oneInThreeDecisionProblem :=
  CostedReduction.ofCostedMap
    threeCNFToOneInThreeFormula
    threeSATToOneInThreeReduction.correct
    (CostedMap.of_encodedPolynomialSizeBound
      threeCNFToOneInThreeFormula_polynomialSizeBound)

noncomputable def threeSATToOneInThreeKarpReduction :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem
      Examples.oneInThreeDecisionProblem :=
  threeSATToOneInThreeCostedReduction.toKarpReductionM

end OneInThree
end Hardness
end CSP
end ComplexityReduction
