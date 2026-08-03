import ComplexityReduction.Schaefer.Tractable.Horn.Part1

namespace ComplexityReduction
namespace Schaefer
namespace Horn

theorem instantiateClause_satisfies_iff {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint Γ) (a : SAT.Assignment) {clause : Clause}
    (hVars : clause.vars ⊆ Finset.range (Γ.relationOf c.symbol).arity) :
    Clause.Satisfies (instantiateClause c clause) a ↔
      Clause.Satisfies clause (tupleAssignment (c.assignmentTuple a)) := by
  constructor
  · intro h hPrem
    cases hHead : clause.head with
    | none =>
        have hFalse := h (by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨x, hxPrem, rfl⟩
          have hxRange := hVars (Clause.premise_mem_vars hxPrem)
          exact (assignment_eq_tupleAssignment_of_in_range c a hxRange).trans (hPrem x hxPrem))
        simp [instantiateClause, Clause.mapVars, hHead] at hFalse
    | some y =>
        have hMapped := h (by
          intro z hz
          rcases Finset.mem_image.mp hz with ⟨x, hxPrem, rfl⟩
          have hxRange := hVars (Clause.premise_mem_vars hxPrem)
          exact (assignment_eq_tupleAssignment_of_in_range c a hxRange).trans (hPrem x hxPrem))
        have hyRange := hVars (Clause.head_mem_vars hHead)
        rw [instantiateClause, Clause.mapVars, hHead] at hMapped
        simp at hMapped
        simpa [hHead] using
          (assignment_eq_tupleAssignment_of_in_range c a hyRange).symm.trans hMapped
  · intro h hPrem
    cases hHead : clause.head with
    | none =>
        have hFalse := h (by
          intro x hx
          have hxRange := hVars (Clause.premise_mem_vars hx)
          have hxMapped : instantiateIndex c x ∈ (instantiateClause c clause).premises := by
            exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
          exact (assignment_eq_tupleAssignment_of_in_range c a hxRange).symm.trans
            (hPrem _ hxMapped))
        simp [hHead] at hFalse
    | some y =>
        have hLocal := h (by
          intro x hx
          have hxRange := hVars (Clause.premise_mem_vars hx)
          have hxMapped : instantiateIndex c x ∈ (instantiateClause c clause).premises := by
            exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
          exact (assignment_eq_tupleAssignment_of_in_range c a hxRange).symm.trans
            (hPrem _ hxMapped))
        have hyRange := hVars (Clause.head_mem_vars hHead)
        rw [hHead] at hLocal
        rw [instantiateClause, Clause.mapVars, hHead]
        simp
        exact (assignment_eq_tupleAssignment_of_in_range c a hyRange).trans hLocal

theorem instantiateCNF_satisfies_iff {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint Γ) (a : SAT.Assignment)
    (cert : RelationCertificate (Γ.relationOf c.symbol)) :
    CNF.Satisfies (instantiateCNF c cert.clauses) a ↔
      CNF.Satisfies cert.clauses (tupleAssignment (c.assignmentTuple a)) := by
  constructor
  · intro h clause hClause
    have hMapped :
        Clause.Satisfies (instantiateClause c clause) a := by
      exact h (instantiateClause c clause) (List.mem_map.mpr ⟨clause, hClause, rfl⟩)
    exact (instantiateClause_satisfies_iff c a (cert.withinArity clause hClause)).1 hMapped
  · intro h mapped hMapped
    rcases List.mem_map.mp hMapped with ⟨clause, hClause, rfl⟩
    exact (instantiateClause_satisfies_iff c a (cert.withinArity clause hClause)).2
      (h clause hClause)

/-- Compile one CSP constraint to a direct Horn-CNF block using the symbol certificate. -/
def constraintToHornCNF {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) (c : CSP.Constraint Γ) : CNF :=
  instantiateCNF c (certs c.symbol).clauses

/-- Compile a local `SAT(S)` formula to direct Horn-CNF using operational certificates. -/
def formulaToHornCNF {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) (φ : SATFormula Γ) : CNF :=
  φ.flatMap (constraintToHornCNF certs)

theorem constraintToHornCNF_satisfies_iff {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) (c : CSP.Constraint Γ) (a : SAT.Assignment) :
    CNF.Satisfies (constraintToHornCNF certs c) a ↔ CSP.Constraint.Satisfies c a := by
  rw [constraintToHornCNF, instantiateCNF_satisfies_iff c a (certs c.symbol)]
  exact ((certs c.symbol).correct (c.assignmentTuple a)).symm

theorem formulaToHornCNF_satisfies_iff {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) (φ : SATFormula Γ) (a : SAT.Assignment) :
    CNF.Satisfies (formulaToHornCNF certs φ) a ↔ CSP.Formula.Satisfies φ a := by
  induction φ with
  | nil =>
      simp [formulaToHornCNF, CSP.Formula.Satisfies]
  | cons c cs ih =>
      change
        CNF.Satisfies (constraintToHornCNF certs c ++ formulaToHornCNF certs cs) a ↔
          CSP.Formula.Satisfies (c :: cs) a
      rw [CNF.satisfies_append, constraintToHornCNF_satisfies_iff certs c a, ih]
      exact (CSP.Formula.satisfies_cons c cs a).symm

theorem formulaToHornCNF_satisfiable_iff {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) (φ : SATFormula Γ) :
    CNF.Satisfiable (formulaToHornCNF certs φ) ↔ SATSatisfiable φ := by
  constructor
  · rintro ⟨a, hSat⟩
    exact ⟨a, (formulaToHornCNF_satisfies_iff certs φ a).1 hSat⟩
  · rintro ⟨a, hSat⟩
    exact ⟨a, (formulaToHornCNF_satisfies_iff certs φ a).2 hSat⟩

/-- Boolean decider obtained by compiling a certified Horn language to direct Horn-CNF. -/
def certificateDecide {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) (φ : SATFormula Γ) : Bool :=
  CNF.decide (formulaToHornCNF certs φ)

theorem certificateDecide_eq_true_iff {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) (φ : SATFormula Γ) :
    certificateDecide certs φ = true ↔ SATSatisfiable φ := by
  exact (CNF.decide_eq_true_iff (formulaToHornCNF certs φ)).trans
    (formulaToHornCNF_satisfiable_iff certs φ)

/-- Cost certificate for the certified Horn-language Boolean decider. -/
def certificateDecideCosted {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) :
    CostedMap (satSDecisionProblem Γ).Instance EncodedType.bool (certificateDecide certs) where
  cost := fun _ => 1
  cost_bound := by
    exact ⟨0, 0, 1, by
      intro φ
      simp⟩
  output_bound := by
    exact ⟨0, 0, 1, by
      intro φ
      simp [EncodedType.inputSize, EncodedType.bool]⟩

/-- Polynomial-time Boolean decider for `SAT(S)` from operational Horn certificates. -/
def certificateSATDecider {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) :
    PolyTimeMap CostedPolyTimeModel (satSDecisionProblem Γ).Instance EncodedType.bool where
  toFun := certificateDecide certs
  polytime := CostedPolyTimeMap.of_costed (certificateDecideCosted certs)

/-- Certified Horn languages are in project-local deterministic polynomial time. -/
theorem certificate_satS_inP {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) :=
  InP.intro (certificateSATDecider certs) (by
    intro φ
    exact certificateDecide_eq_true_iff certs φ)

/-- Compatibility spelling for the certified Horn-language tractable theorem. -/
theorem hornCertificate_satS_inP {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) :=
  certificate_satS_inP certs

/-- Descriptor for the operational Horn-language bridge and costed decider. -/
def certificateBridgeDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1(c), Horn/weakly-positive tractable route"
    informalClaim :=
      "A SAT(S) language whose relations carry explicit Horn-CNF certificates is \
       polynomial-time decidable by compilation to the direct Horn solver."
    localTargetSymbol := "ComplexityReduction.Schaefer.Horn.hornCertificate_satS_inP"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Horn.RelationCertificate"
      , "ComplexityReduction.Schaefer.Horn.LanguageCertificate"
      , "ComplexityReduction.Schaefer.Horn.formulaToHornCNF_satisfiable_iff"
      , "ComplexityReduction.Schaefer.Horn.CNF.decide_eq_true_iff"
      , "ComplexityReduction.Schaefer.Horn.certificateSATDecider"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "This is the operational certificate bridge used by the closure-form Horn theorem \
       in this module." }

/-- Pointwise complement of a Boolean assignment. -/
def complementAssignment (a : SAT.Assignment) : SAT.Assignment :=
  fun x => !(a x)

@[simp]
theorem complementAssignment_involutive (a : SAT.Assignment) :
    complementAssignment (complementAssignment a) = a := by
  funext x
  simp [complementAssignment]

/--
An operational dual-Horn representation of one relation, stated by compiling the
complemented tuple to direct Horn-CNF.
-/
structure DualRelationCertificate (R : CSP.BoolRel) where
  clauses : CNF
  withinArity : ∀ c ∈ clauses, c.vars ⊆ Finset.range R.arity
  correct : ∀ t : CSP.BoolTuple R.arity,
    R.Holds t ↔ CNF.Satisfies clauses (tupleAssignment (BoolTuple.complement t))

/-- An operational dual-Horn representation for every symbol of a fixed language. -/
abbrev DualLanguageCertificate (Γ : CSP.BoolLanguage) : Type :=
  ∀ s : Γ.Symbol, DualRelationCertificate (Γ.relationOf s)

/-- A finite relation closed under pointwise OR has an operational dual-Horn certificate. -/
noncomputable def dualRelationCertificateOfIsDualHorn {R : CSP.BoolRel}
    (hDual : IsDualHorn R) :
    DualRelationCertificate R :=
  let cert := relationCertificateOfIsHorn (isHorn_dualToHornRelation_of_isDualHorn hDual)
  { clauses := cert.clauses
    withinArity := by
      intro c hc
      simpa [dualToHornRelation] using cert.withinArity c hc
    correct := by
      intro t
      have hCert :
          (dualToHornRelation R).Holds (BoolTuple.complement t) ↔
            CNF.Satisfies cert.clauses (tupleAssignment (BoolTuple.complement t)) :=
        cert.correct (BoolTuple.complement t)
      have hLeft : R.Holds t ↔ (dualToHornRelation R).Holds (BoolTuple.complement t) := by
        rw [dualToHornRelation_holds_iff]
        change t ∈ R.accepts ↔ BoolTuple.complement (BoolTuple.complement t) ∈ R.accepts
        rw [boolTuple_complement_involutive]
      exact hLeft.trans hCert }

/-- Lift the dual-Horn closure characterization from one relation to a finite language. -/
noncomputable def dualLanguageCertificateOfIsDualHornLanguage {Γ : CSP.BoolLanguage}
    (hΓ : IsDualHornLanguage Γ) :
    DualLanguageCertificate Γ :=
  fun s => dualRelationCertificateOfIsDualHorn (hΓ s)

theorem complementAssignment_eq_tupleAssignment_complement_of_in_range
    {Γ : CSP.BoolLanguage} (c : CSP.Constraint Γ) (a : SAT.Assignment) {x : Nat}
    (hx : x ∈ Finset.range (Γ.relationOf c.symbol).arity) :
    complementAssignment a (instantiateIndex c x) =
      tupleAssignment (BoolTuple.complement (c.assignmentTuple a)) x := by
  have hxLt : x < (Γ.relationOf c.symbol).arity := by
    simpa using hx
  simp [complementAssignment, instantiateIndex, tupleAssignment, BoolTuple.complement,
    CSP.Constraint.assignmentTuple, hxLt]

theorem instantiateClause_complement_satisfies_iff {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint Γ) (a : SAT.Assignment) {clause : Clause}
    (hVars : clause.vars ⊆ Finset.range (Γ.relationOf c.symbol).arity) :
    Clause.Satisfies (instantiateClause c clause) (complementAssignment a) ↔
      Clause.Satisfies clause
        (tupleAssignment (BoolTuple.complement (c.assignmentTuple a))) := by
  constructor
  · intro h hPrem
    cases hHead : clause.head with
    | none =>
        have hFalse := h (by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨x, hxPrem, rfl⟩
          have hxRange := hVars (Clause.premise_mem_vars hxPrem)
          exact (complementAssignment_eq_tupleAssignment_complement_of_in_range c a hxRange).trans
            (hPrem x hxPrem))
        simp [instantiateClause, Clause.mapVars, hHead] at hFalse
    | some y =>
        have hMapped := h (by
          intro z hz
          rcases Finset.mem_image.mp hz with ⟨x, hxPrem, rfl⟩
          have hxRange := hVars (Clause.premise_mem_vars hxPrem)
          exact (complementAssignment_eq_tupleAssignment_complement_of_in_range c a hxRange).trans
            (hPrem x hxPrem))
        have hyRange := hVars (Clause.head_mem_vars hHead)
        rw [instantiateClause, Clause.mapVars, hHead] at hMapped
        simp at hMapped
        simpa [hHead] using
          (complementAssignment_eq_tupleAssignment_complement_of_in_range c a hyRange).symm.trans
            hMapped
  · intro h hPrem
    cases hHead : clause.head with
    | none =>
        have hFalse := h (by
          intro x hx
          have hxRange := hVars (Clause.premise_mem_vars hx)
          have hxMapped : instantiateIndex c x ∈ (instantiateClause c clause).premises := by
            exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
          exact (complementAssignment_eq_tupleAssignment_complement_of_in_range c a hxRange).symm.trans
            (hPrem _ hxMapped))
        simp [hHead] at hFalse
    | some y =>
        have hLocal := h (by
          intro x hx
          have hxRange := hVars (Clause.premise_mem_vars hx)
          have hxMapped : instantiateIndex c x ∈ (instantiateClause c clause).premises := by
            exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
          exact (complementAssignment_eq_tupleAssignment_complement_of_in_range c a hxRange).symm.trans
            (hPrem _ hxMapped))
        have hyRange := hVars (Clause.head_mem_vars hHead)
        rw [hHead] at hLocal
        rw [instantiateClause, Clause.mapVars, hHead]
        simp
        exact (complementAssignment_eq_tupleAssignment_complement_of_in_range c a hyRange).trans
          hLocal

theorem instantiateCNF_complement_satisfies_iff {Γ : CSP.BoolLanguage}
    (c : CSP.Constraint Γ) (a : SAT.Assignment)
    (cert : DualRelationCertificate (Γ.relationOf c.symbol)) :
    CNF.Satisfies (instantiateCNF c cert.clauses) (complementAssignment a) ↔
      CNF.Satisfies cert.clauses
        (tupleAssignment (BoolTuple.complement (c.assignmentTuple a))) := by
  constructor
  · intro h clause hClause
    have hMapped :
        Clause.Satisfies (instantiateClause c clause) (complementAssignment a) := by
      exact h (instantiateClause c clause) (List.mem_map.mpr ⟨clause, hClause, rfl⟩)
    exact (instantiateClause_complement_satisfies_iff c a
      (cert.withinArity clause hClause)).1 hMapped
  · intro h mapped hMapped
    rcases List.mem_map.mp hMapped with ⟨clause, hClause, rfl⟩
    exact (instantiateClause_complement_satisfies_iff c a
      (cert.withinArity clause hClause)).2 (h clause hClause)

/-- Compile one dual-Horn-certified CSP constraint to a direct Horn-CNF block. -/
def dualConstraintToHornCNF {Γ : CSP.BoolLanguage}
    (certs : DualLanguageCertificate Γ) (c : CSP.Constraint Γ) : CNF :=
  instantiateCNF c (certs c.symbol).clauses

/-- Compile a dual-Horn-certified local `SAT(S)` formula to direct Horn-CNF. -/
def dualFormulaToHornCNF {Γ : CSP.BoolLanguage}
    (certs : DualLanguageCertificate Γ) (φ : SATFormula Γ) : CNF :=
  φ.flatMap (dualConstraintToHornCNF certs)

theorem dualConstraintToHornCNF_satisfies_iff {Γ : CSP.BoolLanguage}
    (certs : DualLanguageCertificate Γ) (c : CSP.Constraint Γ) (a : SAT.Assignment) :
    CNF.Satisfies (dualConstraintToHornCNF certs c) (complementAssignment a) ↔
      CSP.Constraint.Satisfies c a := by
  rw [dualConstraintToHornCNF, instantiateCNF_complement_satisfies_iff c a (certs c.symbol)]
  exact ((certs c.symbol).correct (c.assignmentTuple a)).symm

theorem dualFormulaToHornCNF_satisfies_iff {Γ : CSP.BoolLanguage}
    (certs : DualLanguageCertificate Γ) (φ : SATFormula Γ) (a : SAT.Assignment) :
    CNF.Satisfies (dualFormulaToHornCNF certs φ) (complementAssignment a) ↔
      CSP.Formula.Satisfies φ a := by
  induction φ with
  | nil =>
      simp [dualFormulaToHornCNF, CSP.Formula.Satisfies]
  | cons c cs ih =>
      change
        CNF.Satisfies
            (dualConstraintToHornCNF certs c ++ dualFormulaToHornCNF certs cs)
            (complementAssignment a) ↔
          CSP.Formula.Satisfies (c :: cs) a
      rw [CNF.satisfies_append, dualConstraintToHornCNF_satisfies_iff certs c a, ih]
      exact (CSP.Formula.satisfies_cons c cs a).symm

theorem dualFormulaToHornCNF_satisfiable_iff {Γ : CSP.BoolLanguage}
    (certs : DualLanguageCertificate Γ) (φ : SATFormula Γ) :
    CNF.Satisfiable (dualFormulaToHornCNF certs φ) ↔ SATSatisfiable φ := by
  constructor
  · rintro ⟨a, hSat⟩
    refine ⟨complementAssignment a, ?_⟩
    have hSat' :
        CNF.Satisfies (dualFormulaToHornCNF certs φ)
          (complementAssignment (complementAssignment a)) := by
      simpa using hSat
    exact (dualFormulaToHornCNF_satisfies_iff certs φ (complementAssignment a)).1 hSat'
  · rintro ⟨a, hSat⟩
    exact ⟨complementAssignment a,
      (dualFormulaToHornCNF_satisfies_iff certs φ a).2 hSat⟩

/-- Boolean decider obtained by complement-compiling a certified dual-Horn language. -/
def dualCertificateDecide {Γ : CSP.BoolLanguage}
    (certs : DualLanguageCertificate Γ) (φ : SATFormula Γ) : Bool :=
  CNF.decide (dualFormulaToHornCNF certs φ)

theorem dualCertificateDecide_eq_true_iff {Γ : CSP.BoolLanguage}
    (certs : DualLanguageCertificate Γ) (φ : SATFormula Γ) :
    dualCertificateDecide certs φ = true ↔ SATSatisfiable φ := by
  exact (CNF.decide_eq_true_iff (dualFormulaToHornCNF certs φ)).trans
    (dualFormulaToHornCNF_satisfiable_iff certs φ)

/-- Cost certificate for the certified dual-Horn-language Boolean decider. -/
def dualCertificateDecideCosted {Γ : CSP.BoolLanguage}
    (certs : DualLanguageCertificate Γ) :
    CostedMap (satSDecisionProblem Γ).Instance EncodedType.bool
      (dualCertificateDecide certs) where
  cost := fun _ => 1
  cost_bound := by
    exact ⟨0, 0, 1, by
      intro φ
      simp⟩
  output_bound := by
    exact ⟨0, 0, 1, by
      intro φ
      simp [EncodedType.inputSize, EncodedType.bool]⟩

/-- Polynomial-time Boolean decider for `SAT(S)` from operational dual-Horn certificates. -/
def dualCertificateSATDecider {Γ : CSP.BoolLanguage}
    (certs : DualLanguageCertificate Γ) :
    PolyTimeMap CostedPolyTimeModel (satSDecisionProblem Γ).Instance EncodedType.bool where
  toFun := dualCertificateDecide certs
  polytime := CostedPolyTimeMap.of_costed (dualCertificateDecideCosted certs)

/-- Certified dual-Horn languages are in project-local deterministic polynomial time. -/
theorem dualCertificate_satS_inP {Γ : CSP.BoolLanguage}
    (certs : DualLanguageCertificate Γ) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) :=
  InP.intro (dualCertificateSATDecider certs) (by
    intro φ
    exact dualCertificateDecide_eq_true_iff certs φ)

/-- Compatibility spelling for the certified dual-Horn-language tractable theorem. -/
theorem dualHornCertificate_satS_inP {Γ : CSP.BoolLanguage}
    (certs : DualLanguageCertificate Γ) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) :=
  dualCertificate_satS_inP certs

/-- Descriptor for the operational dual-Horn bridge through Boolean complement. -/
def dualCertificateBridgeDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1(c), dual-Horn/weakly-negative tractable route"
    informalClaim :=
      "A SAT(S) language whose relations carry explicit dual-Horn certificates is \
       polynomial-time decidable by complement transport to the direct Horn solver."
    localTargetSymbol := "ComplexityReduction.Schaefer.Horn.dualHornCertificate_satS_inP"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Horn.DualRelationCertificate"
      , "ComplexityReduction.Schaefer.Horn.DualLanguageCertificate"
      , "ComplexityReduction.Schaefer.Horn.dualFormulaToHornCNF_satisfiable_iff"
      , "ComplexityReduction.Schaefer.Horn.CNF.decide_eq_true_iff"
      , "ComplexityReduction.Schaefer.Horn.dualCertificateSATDecider"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "This is the operational dual-Horn certificate bridge used by the closure-form \
       dual-Horn theorem in this module." }

end Horn

/-- Horn closure-form languages are in project-local deterministic polynomial time. -/
theorem horn_satS_inP {Γ : CSP.BoolLanguage}
    (hΓ : IsHornLanguage Γ) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) :=
  Horn.hornCertificate_satS_inP (Horn.languageCertificateOfIsHornLanguage hΓ)

/-- Horn closure-form case as an instance of the common tractable-side statement shape. -/
theorem horn_tractableSideStatement (Γ : CSP.BoolLanguage) :
    tractableSideStatement Γ TractableConditionKind.horn := by
  intro hΓ
  exact horn_satS_inP hΓ

/-- Dual-Horn closure-form languages are in project-local deterministic polynomial time. -/
theorem dualHorn_satS_inP {Γ : CSP.BoolLanguage}
    (hΓ : IsDualHornLanguage Γ) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) :=
  Horn.dualHornCertificate_satS_inP (Horn.dualLanguageCertificateOfIsDualHornLanguage hΓ)

/-- Dual-Horn closure-form case as an instance of the common tractable-side statement shape. -/
theorem dualHorn_tractableSideStatement (Γ : CSP.BoolLanguage) :
    tractableSideStatement Γ TractableConditionKind.dualHorn := by
  intro hΓ
  exact dualHorn_satS_inP hΓ

/-- Descriptor for the closure-form Horn tractable-side theorem. -/
def hornClosureTractableDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1(c)"
    informalClaim := "If every relation in S is Horn/weakly-positive, SAT(S) is in P."
    localTargetSymbol := "ComplexityReduction.Schaefer.horn_satS_inP"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Horn.relationCertificateOfIsHorn"
      , "ComplexityReduction.Schaefer.Horn.languageCertificateOfIsHornLanguage"
      , "ComplexityReduction.Schaefer.Horn.hornCertificate_satS_inP"
      , "ComplexityReduction.Schaefer.horn_tractableSideStatement"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "Local finite truth-table proof constructs one separating Horn clause for each \
       falsifying tuple, then invokes the already proved Horn-CNF unit-closure solver." }

/-- Descriptor for the closure-form dual-Horn tractable-side theorem. -/
def dualHornClosureTractableDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1(c)"
    informalClaim := "If every relation in S is dual-Horn/weakly-negative, SAT(S) is in P."
    localTargetSymbol := "ComplexityReduction.Schaefer.dualHorn_satS_inP"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Horn.dualRelationCertificateOfIsDualHorn"
      , "ComplexityReduction.Schaefer.Horn.dualLanguageCertificateOfIsDualHornLanguage"
      , "ComplexityReduction.Schaefer.Horn.dualHornCertificate_satS_inP"
      , "ComplexityReduction.Schaefer.dualHorn_tractableSideStatement"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "Local proof complements tuples, reuses the Horn closure characterization, and \
       then invokes the operational dual-Horn certificate bridge." }

end Schaefer
end ComplexityReduction
