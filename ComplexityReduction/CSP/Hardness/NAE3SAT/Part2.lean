import ComplexityReduction.CSP.Hardness.NAE3SAT.Part1

namespace ComplexityReduction
namespace CSP
namespace Hardness
namespace NAE3SAT
open SAT

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

theorem sourceComplementConstraints_extend {φ : ThreeCNF} {a : Assignment} :
    Formula.Satisfies (sourceComplementConstraints φ) (extendAssignment φ a) := by
  unfold sourceComplementConstraints
  exact sourceComplementConstraintsAux_extend
    (extendAssignment_falseVar φ a)
    (extendAssignment_trueVar φ a)
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
      simpa [extendAssignment] using
        (extendAssignmentAux_auxValues
          (φ := φ) (clauses := φ.clauses) (i := 0)
          (source := a) (base := extendBaseAssignment φ a)))
    hSat

theorem threeCNFToNAE3Formula_extend (φ : ThreeCNF) :
    φ.Satisfiable → Formula.Satisfiable (threeCNFToNAE3Formula φ) := by
  rintro ⟨a, hSat⟩
  refine ⟨extendAssignment φ a, ?_⟩
  intro c hc
  have hCases :
      c = anchorConstraint φ ∨
        c ∈ sourceComplementConstraints φ ∨
          c ∈ clausesToFormulaAux φ 0 φ.clauses := by
    simpa [threeCNFToNAE3Formula] using hc
  rcases hCases with hAnchor | hSource | hClause
  · subst c
    exact (anchorConstraint_satisfies_iff φ (extendAssignment φ a)).2 (by
      simp [extendAssignment_falseVar, extendAssignment_trueVar])
  · exact sourceComplementConstraints_extend (φ := φ) (a := a) c hSource
  · exact clausesToFormulaAux_extend (φ := φ) (a := a) hSat c hClause

theorem threeCNFToNAE3Formula_satisfiable_iff (φ : ThreeCNF) :
    Formula.Satisfiable (threeCNFToNAE3Formula φ) ↔ φ.Satisfiable :=
  ⟨threeCNFToNAE3Formula_project φ, threeCNFToNAE3Formula_extend φ⟩

/-- Semantic reverse reduction from local 3SAT to ordinary NAE-3SAT. -/
noncomputable def threeSATToNAE3Reduction :
    SemanticReduction SAT.threeSATDecisionProblem Examples.notAllEqual3DecisionProblem where
  f := threeCNFToNAE3Formula
  correct := by
    intro φ
    exact (threeCNFToNAE3Formula_satisfiable_iff φ).symm

theorem naeConstraint_encodedLength (x y z : Nat) :
    (Encoding.encodeConstraint (naeConstraint x y z)).length = x + y + z + 8 := by
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

theorem complementPairConstraints_encodedLength_le {x nx f t B : Nat}
    (hx : x ≤ B) (hnx : nx ≤ B) (hf : f ≤ B) (ht : t ≤ B) :
    (Encoding.encodeFormula (complementPairConstraints x nx f t)).length ≤
      2 * (3 * B + 8) := by
  simp [complementPairConstraints, Encoding.encodeFormula, naeConstraint_encodedLength]
  omega

theorem sourceComplementConstraintsAux_encodedLength_le {φ : ThreeCNF} {n B : Nat}
    (hN : ∀ x, x < n → x ≤ B)
    (hNeg : ∀ x, x < n → negVar φ x ≤ B)
    (hFalse : falseVar φ ≤ B)
    (hTrue : trueVar φ ≤ B) :
    (Encoding.encodeFormula (sourceComplementConstraintsAux φ n)).length ≤
      2 * n * (3 * B + 8) := by
  induction n with
  | zero =>
      simp [sourceComplementConstraintsAux]
  | succ n ih =>
      have hHead := complementPairConstraints_encodedLength_le
        (x := n) (nx := negVar φ n) (f := falseVar φ) (t := trueVar φ) (B := B)
        (hN n (Nat.lt_succ_self n)) (hNeg n (Nat.lt_succ_self n)) hFalse hTrue
      have hTail := ih
        (by intro x hx; exact hN x (Nat.lt_trans hx (Nat.lt_succ_self n)))
        (by intro x hx; exact hNeg x (Nat.lt_trans hx (Nat.lt_succ_self n)))
      simp [sourceComplementConstraintsAux, Encoding.encodeFormula, List.length_flatMap] at hHead hTail ⊢
      calc
        (List.map (fun a => (Encoding.encodeConstraint a).length)
              (complementPairConstraints n (negVar φ n) (falseVar φ) (trueVar φ))).sum +
            (List.map (fun a => (Encoding.encodeConstraint a).length)
              (sourceComplementConstraintsAux φ n)).sum
            ≤ 2 * (3 * B + 8) + 2 * n * (3 * B + 8) :=
          Nat.add_le_add hHead hTail
        _ = 2 * (n + 1) * (3 * B + 8) := by ring

theorem clauseToFormula_encodedLength_le {φ : ThreeCNF} {c : Clause} (hlen : c.length ≤ 3)
    {i B : Nat}
    (hFalse : falseVar φ ≤ B) (hTrue : trueVar φ ≤ B)
    (hAux : auxVar φ i ≤ B) (hAuxNeg : auxNegVar φ i ≤ B)
    (hLit : ∀ l ∈ c, litVar φ l ≤ B) :
    (Encoding.encodeFormula (clauseToFormula φ i c)).length ≤
      4 * (3 * B + 8) := by
  cases c with
  | nil =>
      simp [clauseToFormula, naeConstraint_encodedLength]
      omega
  | cons l₁ rest =>
      cases rest with
      | nil =>
          have h₁ : litVar φ l₁ ≤ B := hLit l₁ (by simp)
          simp [clauseToFormula, naeConstraint_encodedLength]
          omega
      | cons l₂ rest₂ =>
          cases rest₂ with
          | nil =>
              have h₁ : litVar φ l₁ ≤ B := hLit l₁ (by simp)
              have h₂ : litVar φ l₂ ≤ B := hLit l₂ (by simp)
              simp [clauseToFormula, naeConstraint_encodedLength]
              omega
          | cons l₃ rest₃ =>
              cases rest₃ with
              | nil =>
                  have h₁ : litVar φ l₁ ≤ B := hLit l₁ (by simp)
                  have h₂ : litVar φ l₂ ≤ B := hLit l₂ (by simp)
                  have h₃ : litVar φ l₃ ≤ B := hLit l₃ (by simp)
                  have hPair := complementPairConstraints_encodedLength_le
                    (x := auxVar φ i) (nx := auxNegVar φ i)
                    (f := falseVar φ) (t := trueVar φ) (B := B)
                    hAux hAuxNeg hFalse hTrue
                  simp [clauseToFormula, Encoding.encodeFormula, naeConstraint_encodedLength,
                    complementPairConstraints] at hPair ⊢
                  omega
              | cons _ _ =>
                  simp at hlen

theorem clausesToFormulaAux_encodedLength_le {φ : ThreeCNF} {clauses : CNF}
    (hThree : CNF.IsThreeCNF clauses) {i B : Nat}
    (hAux : ∀ j, i ≤ j → j < i + clauses.length → auxVar φ j ≤ B)
    (hAuxNeg : ∀ j, i ≤ j → j < i + clauses.length → auxNegVar φ j ≤ B)
    (hFalse : falseVar φ ≤ B) (hTrue : trueVar φ ≤ B)
    (hLit : ∀ c ∈ clauses, ∀ l ∈ c, litVar φ l ≤ B) :
    (Encoding.encodeFormula (clausesToFormulaAux φ i clauses)).length ≤
      4 * clauses.length * (3 * B + 8) := by
  induction clauses generalizing i with
  | nil =>
      simp [clausesToFormulaAux]
  | cons c cs ih =>
      have hcLen : c.length ≤ 3 := hThree c (by simp)
      have hcsThree : CNF.IsThreeCNF cs := by
        intro d hd
        exact hThree d (by simp [hd])
      have hAuxHead : auxVar φ i ≤ B := hAux i (Nat.le_refl i) (by simp)
      have hAuxNegHead : auxNegVar φ i ≤ B := hAuxNeg i (Nat.le_refl i) (by simp)
      have hBlock := clauseToFormula_encodedLength_le (φ := φ) (c := c) hcLen
        (i := i) (B := B) hFalse hTrue hAuxHead hAuxNegHead
        (by intro l hl; exact hLit c (by simp) l hl)
      have hTail := ih hcsThree (i := i + 1)
        (by
          intro j hjLower hjUpper
          exact hAux j (Nat.le_trans (Nat.le_succ i) hjLower)
            (by simp at hjUpper ⊢; omega))
        (by
          intro j hjLower hjUpper
          exact hAuxNeg j (Nat.le_trans (Nat.le_succ i) hjLower)
            (by simp at hjUpper ⊢; omega))
        (by intro d hd l hl; exact hLit d (by simp [hd]) l hl)
      simp [clausesToFormulaAux, Encoding.encodeFormula, List.length_flatMap] at hBlock hTail ⊢
      calc
        (List.map (fun a => (Encoding.encodeConstraint a).length) (clauseToFormula φ i c)).sum +
            (List.map (fun a => (Encoding.encodeConstraint a).length)
              (clausesToFormulaAux φ (i + 1) cs)).sum
            ≤ 4 * (3 * B + 8) + 4 * cs.length * (3 * B + 8) :=
          Nat.add_le_add hBlock hTail
        _ = 4 * (cs.length + 1) * (3 * B + 8) := by ring

theorem literal_var_lt_encodeClause_length {c : Clause} {l : Literal} (hl : l ∈ c) :
    l.var < (ThreeSATEncoding.encodeClause c).length := by
  have hmem : (ThreeSATEncoding.encodeLiteral l).length ∈
      (c.map fun x => (ThreeSATEncoding.encodeLiteral x).length) := by
    exact List.mem_map.mpr ⟨l, hl, rfl⟩
  have hle : (ThreeSATEncoding.encodeLiteral l).length ≤
      (c.map fun x => (ThreeSATEncoding.encodeLiteral x).length).sum :=
    List.le_sum_of_mem hmem
  simp [ThreeSATEncoding.encodeClause, ThreeSATEncoding.encodeLiteral,
    ThreeSATEncoding.encodeNat, EncodedType.nat, List.length_flatMap] at hle ⊢
  omega

theorem threeCNF_varBound_le_inputSize (φ : ThreeCNF) :
    falseVar φ ≤ SAT.threeSATDecisionProblem.Instance.inputSize φ := by
  unfold falseVar
  change CNF.varBound φ.clauses ≤ (ThreeSATEncoding.encodeThreeCNF φ).length
  exact CNF.varBound_le_of_vars_lt φ.clauses (ThreeSATEncoding.encodeThreeCNF φ).length
    (by
      intro c hc l hl
      have hLit : l.var < (ThreeSATEncoding.encodeClause c).length :=
        literal_var_lt_encodeClause_length hl
      have hBlock :
          (ThreeSATEncoding.encodeClause c).length ≤
            (ThreeSATEncoding.encodeThreeCNF φ).length := by
        unfold ThreeSATEncoding.encodeThreeCNF
        rw [List.length_flatMap]
        exact List.le_sum_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)
      exact Nat.lt_of_lt_of_le hLit hBlock)

theorem cnf_clauseLength_le_encodeCNF (clauses : CNF) :
    clauses.length ≤ (ThreeSATEncoding.encodeCNF clauses).length := by
  induction clauses with
  | nil =>
      simp [ThreeSATEncoding.encodeCNF]
  | cons c cs ih =>
      have hc : 1 ≤ (ThreeSATEncoding.encodeClause c).length := by
        simp [ThreeSATEncoding.encodeClause]
      rw [ThreeSATEncoding.encodeCNF_cons, List.length_append, List.length_cons]
      omega

theorem threeCNF_clauseLength_le_inputSize (φ : ThreeCNF) :
    φ.clauses.length ≤ SAT.threeSATDecisionProblem.Instance.inputSize φ := by
  change φ.clauses.length ≤ (ThreeSATEncoding.encodeThreeCNF φ).length
  simpa [ThreeSATEncoding.encodeThreeCNF_eq_encodeCNF] using
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

theorem threeCNFToNAE3Formula_encodedLength_le_quadratic (φ : ThreeCNF) :
    (Encoding.encodeFormula (threeCNFToNAE3Formula φ)).length ≤
      200 * (SAT.threeSATDecisionProblem.Instance.inputSize φ + 1) ^ 2 := by
  let n := SAT.threeSATDecisionProblem.Instance.inputSize φ
  let B := 4 * (n + 1)
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
    hSourceIndex hNeg hFalse hTrue
  have hAux : ∀ j, 0 ≤ j → j < 0 + φ.clauses.length → auxVar φ j ≤ B := by
    intro j _ hj
    unfold B auxVar auxBase
    have hjlt : j < φ.clauses.length := by simpa using hj
    have hjle : j ≤ n := Nat.le_trans (Nat.le_of_lt hjlt) hClauseLen
    omega
  have hAuxNeg : ∀ j, 0 ≤ j → j < 0 + φ.clauses.length → auxNegVar φ j ≤ B := by
    intro j _ hj
    unfold B auxNegVar auxBase
    have hjlt : j < φ.clauses.length := by simpa using hj
    have hjle : j ≤ n := Nat.le_trans (Nat.le_of_lt hjlt) hClauseLen
    omega
  have hLit : ∀ c ∈ φ.clauses, ∀ l ∈ c, litVar φ l ≤ B := by
    intro c hc l hl
    exact litVar_le_of_source_bound hFalse hNeg (CNF.clause_vars_lt_varBound hc l hl)
  have hClauses := clausesToFormulaAux_encodedLength_le φ.isThree
    (φ := φ) (i := 0) (B := B) hAux hAuxNeg hFalse hTrue hLit
  have hAnchor : (Encoding.encodeConstraint (anchorConstraint φ)).length ≤ 3 * B + 8 := by
    rw [anchorConstraint, naeConstraint_encodedLength]
    omega
  simp [threeCNFToNAE3Formula, sourceComplementConstraints, Encoding.encodeFormula,
    List.length_flatMap] at hSource hClauses ⊢
  have hMain :
      (3 * B + 8) + 2 * falseVar φ * (3 * B + 8) +
          4 * φ.clauses.length * (3 * B + 8) ≤ 200 * (n + 1) ^ 2 := by
    unfold B
    let A := n + 1
    have hfactor : 3 * (4 * A) + 8 ≤ 20 * A := by omega
    have hsum : 1 + 2 * falseVar φ + 4 * φ.clauses.length ≤ 7 * A := by
      unfold A
      omega
    calc
      (3 * (4 * A) + 8) + 2 * falseVar φ * (3 * (4 * A) + 8) +
          4 * φ.clauses.length * (3 * (4 * A) + 8)
          = (1 + 2 * falseVar φ + 4 * φ.clauses.length) * (3 * (4 * A) + 8) := by ring
      _ ≤ 7 * A * (20 * A) := Nat.mul_le_mul hsum hfactor
      _ = 140 * A ^ 2 := by ring
      _ ≤ 200 * A ^ 2 := by omega
  calc
    (Encoding.encodeConstraint (anchorConstraint φ)).length +
        ((List.map (fun a => (Encoding.encodeConstraint a).length)
              (sourceComplementConstraintsAux φ (falseVar φ))).sum +
          (List.map (fun a => (Encoding.encodeConstraint a).length)
              (clausesToFormulaAux φ 0 φ.clauses)).sum)
        ≤ (3 * B + 8) + 2 * falseVar φ * (3 * B + 8) +
            4 * φ.clauses.length * (3 * B + 8) := by
      omega
    _ ≤ 200 * (n + 1) ^ 2 := hMain

theorem threeCNFToNAE3Formula_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : ThreeCNF => SAT.threeSATDecisionProblem.Instance.inputSize φ)
      (fun ψ : Formula Examples.notAllEqual3Language =>
        Examples.notAllEqual3DecisionProblem.Instance.inputSize ψ)
      threeCNFToNAE3Formula :=
  PolynomialSizeBound.intro_with 2 800 200 (by
    intro φ
    have h := threeCNFToNAE3Formula_encodedLength_le_quadratic φ
    calc
      Examples.notAllEqual3DecisionProblem.Instance.inputSize (threeCNFToNAE3Formula φ)
          ≤ 200 * (SAT.threeSATDecisionProblem.Instance.inputSize φ + 1) ^ 2 := by
        simpa [EncodedType.inputSize, Examples.notAllEqual3DecisionProblem,
          boolCSPDecisionProblem, boolCSPSatLike, formulaEncodedType] using h
      _ ≤ 200 *
          (4 * (SAT.threeSATDecisionProblem.Instance.inputSize φ) ^ 2 + 1) := by
        exact Nat.mul_le_mul_left 200
          (Formula.add_one_sq_le_four_sq_add_one
            (SAT.threeSATDecisionProblem.Instance.inputSize φ))
      _ = 800 * (SAT.threeSATDecisionProblem.Instance.inputSize φ) ^ 2 + 200 := by
        ring)

/-- Project-local costed reverse reduction from local 3SAT to ordinary NAE-3SAT. -/
noncomputable def threeSATToNAE3CostedReduction :
    CostedReduction SAT.threeSATDecisionProblem Examples.notAllEqual3DecisionProblem :=
  CostedReduction.ofCostedMap
    threeCNFToNAE3Formula
    threeSATToNAE3Reduction.correct
    (CostedMap.of_encodedPolynomialSizeBound
      threeCNFToNAE3Formula_polynomialSizeBound)

/-- Costed-model Karp reverse reduction from local 3SAT to ordinary NAE-3SAT. -/
noncomputable def threeSATToNAE3KarpReduction :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem
      Examples.notAllEqual3DecisionProblem :=
  threeSATToNAE3CostedReduction.toKarpReductionM

end NAE3SAT
end Hardness
end CSP
end ComplexityReduction
