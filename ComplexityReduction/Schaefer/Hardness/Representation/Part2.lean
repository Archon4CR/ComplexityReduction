import ComplexityReduction.Schaefer.Hardness.Representation.Part1

namespace ComplexityReduction
namespace Schaefer
namespace Hardness

theorem formulaViaRepresentation_satisfiable_iff {Δ Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation Δ Γ) (φ : SATFormula Δ) :
    SATSatisfiable (formulaViaRepresentation rep φ) ↔ SATSatisfiable φ := by
  constructor
  · rintro ⟨target, hTarget⟩
    exact ⟨target, formulaViaRepresentation_project rep φ hTarget⟩
  · rintro ⟨source, hSource⟩
    exact formulaViaRepresentation_lift rep φ hSource

/--
Compose a single relation representation block through another language
representation.  The auxiliary block starts above both the free-variable range
and the variables already used by the intermediate block, so fresh variables do
not collide with free variables that happen not to occur in the block.
-/
noncomputable def relationFormulaViaRepresentationComposition
    {Δ Γ : CSP.BoolLanguage} (inner : LanguageRepresentation Δ Γ)
    (R : CSP.BoolRel) (rep : RelationFormula Δ R.arity) :
    RelationFormula Γ R.arity where
  constraints :=
    formulaViaRepresentationFrom inner
      (max R.arity (formulaVarBound rep.constraints))
      inner.auxBlockWidth
      rep.constraints
  notes := "Composition of relation representations."

/-- Semantic correctness for a composed relation representation block. -/
theorem relationFormulaViaRepresentationComposition_represents
    {Δ Γ : CSP.BoolLanguage} (inner : LanguageRepresentation Δ Γ)
    (R : CSP.BoolRel) (rep : RelationFormula Δ R.arity)
    (hRep : RepresentsRelation Δ R rep) :
    RepresentsRelation Γ R
      (relationFormulaViaRepresentationComposition inner R rep) := by
  intro t
  let auxBase := max R.arity (formulaVarBound rep.constraints)
  constructor
  · intro hR
    rcases (hRep t).1 hR with ⟨midAux, hMid⟩
    let source := extendTupleAssignment t midAux
    have hWidth :
        ∀ s : Δ.Symbol, ∀ x ∈ FiniteSearch.formulaVars (inner.block s).constraints,
          x < inner.auxBlockWidth := by
      intro s x hx
      exact inner.var_lt_auxBlockWidth s hx
    have hSource :
        ∀ c ∈ rep.constraints, ∀ i : Fin (Δ.relationOf c.symbol).arity,
          c.vars i < auxBase := by
      intro c hc i
      have hVar : c.vars i < formulaVarBound rep.constraints :=
        constraint_var_lt_formulaVarBound_of_mem hc i
      exact lt_of_lt_of_le hVar (Nat.le_max_right R.arity (formulaVarBound rep.constraints))
    rcases formulaViaRepresentationFrom_lift inner auxBase inner.auxBlockWidth
        rep.constraints hWidth hSource hMid with
      ⟨target, hTarget, hAgree⟩
    let finalAux : SAT.Assignment := fun x => target x
    refine ⟨finalAux, ?_⟩
    refine (FiniteSearch.formula_satisfies_iff_of_agree
      (φ := (relationFormulaViaRepresentationComposition inner R rep).constraints)
      (a := extendTupleAssignment t finalAux)
      (b := target) ?_).2 hTarget
    intro y _hy
    by_cases hyFree : y < R.arity
    · have hyBase : y < auxBase :=
        lt_of_lt_of_le hyFree (Nat.le_max_left R.arity (formulaVarBound rep.constraints))
      have hTargetSource : target y = source y := hAgree y hyBase
      have hSource : source y = t ⟨y, hyFree⟩ := by
        simp [source, hyFree]
      have hFinal : extendTupleAssignment t finalAux y = t ⟨y, hyFree⟩ := by
        simp [extendTupleAssignment, hyFree]
      exact hFinal.trans (hTargetSource.trans hSource).symm
    · simp [extendTupleAssignment, finalAux, hyFree]
  · rintro ⟨aux, hSat⟩
    have hMid :
        CSP.Formula.Satisfies rep.constraints (extendTupleAssignment t aux) := by
      exact formulaViaRepresentationFrom_project inner auxBase inner.auxBlockWidth
        rep.constraints hSat
    exact (hRep t).2 ⟨aux, hMid⟩

/-- Compose two language representations. -/
noncomputable def composeLanguageRepresentation
    (Α Δ Γ : CSP.BoolLanguage)
    (outer : LanguageRepresentation Α Δ) (inner : LanguageRepresentation Δ Γ) :
    LanguageRepresentation Α Γ where
  block s :=
    relationFormulaViaRepresentationComposition inner (Α.relationOf s) (outer.block s)
  represents s :=
    relationFormulaViaRepresentationComposition_represents inner
      (Α.relationOf s) (outer.block s) (outer.represents s)
  notes := "Composition of proof-bearing language representations."

/--
Proof-bearing formula expansion certificate.  Future concrete hard gadgets can
instantiate this once their fresh-variable allocation and semantic proof are in
place.
-/
structure RepresentationReductionCertificate (Δ Γ : CSP.BoolLanguage) where
  representation : LanguageRepresentation Δ Γ
  mapFormula : SATFormula Δ → SATFormula Γ
  mapFormula_satisfiable_iff :
    ∀ φ : SATFormula Δ, SATSatisfiable (mapFormula φ) ↔ SATSatisfiable φ
  reduction :
    KarpReductionM CostedPolyTimeModel (satSDecisionProblem Δ) (satSDecisionProblem Γ)

/--
Package the canonical formula expansion as a representation-reduction
certificate once a costed polynomial-time map certificate is supplied.
-/
noncomputable def representationReductionCertificateOfLanguageRepresentation
    {Δ Γ : CSP.BoolLanguage} (rep : LanguageRepresentation Δ Γ)
    (hPoly :
      CostedPolyTimeModel.IsPolyTimeMap
        (X := (satSDecisionProblem Δ).Instance)
        (Y := (satSDecisionProblem Γ).Instance)
        (formulaViaRepresentation rep)) :
    RepresentationReductionCertificate Δ Γ where
  representation := rep
  mapFormula := formulaViaRepresentation rep
  mapFormula_satisfiable_iff := formulaViaRepresentation_satisfiable_iff rep
  reduction :=
    { f := { toFun := formulaViaRepresentation rep, polytime := hPoly }
      correct := fun φ => (formulaViaRepresentation_satisfiable_iff rep φ).symm }

noncomputable def representationReductionCertificateOfLanguageRepresentationAuto
    {Δ Γ : CSP.BoolLanguage} (rep : LanguageRepresentation Δ Γ) :
    RepresentationReductionCertificate Δ Γ :=
  representationReductionCertificateOfLanguageRepresentation rep
    (formulaViaRepresentation_polytime rep)

/-- Known hard base language families that can feed a hard-side certificate. -/
inductive HardBaseRelationKind where
  | threeSATLike
  | oneInThree
  | nae3
  deriving DecidableEq, Repr

namespace HardBaseRelationKind

/-- Stable spelling for docs and manifests. -/
def asString : HardBaseRelationKind → String
  | threeSATLike => "threeSAT-like"
  | oneInThree => "one-in-three"
  | nae3 => "NAE-3SAT"

end HardBaseRelationKind

/--
A hard-side certificate for a local language `Γ`.

The certificate starts from a base problem already known NP-complete under the
explicit local 3SAT boundary, then supplies a Karp reduction into `SAT(Γ)` and
membership for `SAT(Γ)` under the same boundary.
-/
structure HardRelationCertificate (Γ : CSP.BoolLanguage) where
  baseKind : HardBaseRelationKind
  baseProblem : EncodedDecisionProblem
  baseNPCompleteFromBoundary :
    Targets.ThreeSATCompleteBoundary → NPCompleteEnc CostedPolyTimeModel baseProblem
  reduction :
    KarpReductionM CostedPolyTimeModel baseProblem (satSDecisionProblem Γ)
  membership :
    Targets.ThreeSATCompleteBoundary →
      InNPEnc CostedPolyTimeModel (satSDecisionProblem Γ)
  notes : String := ""

/-- Every fixed local `SAT(S)` language is in NP once local 3SAT is in NP. -/
theorem satS_inNP_fromBoundary (Γ : CSP.BoolLanguage)
    (B : Targets.ThreeSATCompleteBoundary) :
    InNPEnc CostedPolyTimeModel (satSDecisionProblem Γ) :=
  CSP.boolCSPInNP_of_threeSATInNP Γ B.complete.1

/-- Extract the Karp reduction carried by a hard-side certificate. -/
def hardCertificate_satS_karp {Γ : CSP.BoolLanguage}
    (cert : HardRelationCertificate Γ) :
    KarpReductionM CostedPolyTimeModel cert.baseProblem (satSDecisionProblem Γ) :=
  cert.reduction

/--
Conditional NP-completeness of `SAT(Γ)` from a hard-side certificate and the
central local 3SAT completeness boundary.
-/
theorem hardCertificate_satS_npComplete_fromBoundary {Γ : CSP.BoolLanguage}
    (cert : HardRelationCertificate Γ) (B : Targets.ThreeSATCompleteBoundary) :
    NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem Γ) :=
  NPCompleteEnc.transfer
    (cert.baseNPCompleteFromBoundary B)
    ⟨cert.reduction⟩
    (cert.membership B)

/-- Identity hard certificate for the fixed local 3SAT-like CSP base language. -/
noncomputable def hardBaseCertificate_threeSATLike :
    HardRelationCertificate CSP.Examples.threeSATLikeLanguage where
  baseKind := HardBaseRelationKind.threeSATLike
  baseProblem := CSP.Examples.threeSATLikeDecisionProblem
  baseNPCompleteFromBoundary :=
    ComplexityReduction.CSP.Hardness.ThreeSATLike.threeSATLikeNPComplete_fromBoundary
  reduction :=
    { f := PolyTimeMap.id CostedPolyTimeModel CSP.Examples.threeSATLikeDecisionProblem.Instance
      correct := fun _ => Iff.rfl }
  membership := satS_inNP_fromBoundary CSP.Examples.threeSATLikeLanguage
  notes := "Base hard-side certificate for the fixed 3SAT-like CSP language."

/-- Identity hard certificate for the fixed ordinary one-in-three CSP base language. -/
noncomputable def hardBaseCertificate_oneInThree :
    HardRelationCertificate CSP.Examples.oneInThreeLanguage where
  baseKind := HardBaseRelationKind.oneInThree
  baseProblem := CSP.Examples.oneInThreeDecisionProblem
  baseNPCompleteFromBoundary :=
    ComplexityReduction.CSP.Hardness.OneInThree.oneInThreeNPComplete_fromBoundary
  reduction :=
    { f := PolyTimeMap.id CostedPolyTimeModel CSP.Examples.oneInThreeDecisionProblem.Instance
      correct := fun _ => Iff.rfl }
  membership := satS_inNP_fromBoundary CSP.Examples.oneInThreeLanguage
  notes := "Base hard-side certificate for the fixed ordinary one-in-three CSP language."

/-- Identity hard certificate for the fixed ordinary NAE-3SAT CSP base language. -/
noncomputable def hardBaseCertificate_nae3 :
    HardRelationCertificate CSP.Examples.notAllEqual3Language where
  baseKind := HardBaseRelationKind.nae3
  baseProblem := CSP.Examples.notAllEqual3DecisionProblem
  baseNPCompleteFromBoundary :=
    ComplexityReduction.CSP.Hardness.NAE3SAT.nae3NPComplete_fromBoundary
  reduction :=
    { f := PolyTimeMap.id CostedPolyTimeModel CSP.Examples.notAllEqual3DecisionProblem.Instance
      correct := fun _ => Iff.rfl }
  membership := satS_inNP_fromBoundary CSP.Examples.notAllEqual3Language
  notes := "Base hard-side certificate for the fixed ordinary NAE-3SAT CSP language."

/--
Transport a hard certificate along a verified representation reduction.
This is the reusable route from a hard base language represented in `Γ` to a
hard-side certificate for `SAT(Γ)`.
-/
noncomputable def hardRelationCertificateOfRepresentation {Δ Γ : CSP.BoolLanguage}
    (base : HardRelationCertificate Δ)
    (red : RepresentationReductionCertificate Δ Γ) :
    HardRelationCertificate Γ where
  baseKind := base.baseKind
  baseProblem := base.baseProblem
  baseNPCompleteFromBoundary := base.baseNPCompleteFromBoundary
  reduction :=
    { f := PolyTimeMap.comp red.reduction.f base.reduction.f
      correct := fun x =>
        Iff.trans (base.reduction.correct x) (red.reduction.correct (base.reduction.f.toFun x)) }
  membership := satS_inNP_fromBoundary Γ
  notes := "Hard certificate transported along a proof-bearing relation representation."

/--
A typed local route from one verified hard base language to a target `SAT(Γ)`.
The missing Schaefer Section 3/4 classification theorem should eventually
produce this structure from `HardCaseAssumptions Γ`.
-/
structure HardClassificationRoute (Γ : CSP.BoolLanguage) where
  Base : CSP.BoolLanguage
  baseCertificate : HardRelationCertificate Base
  representationCertificate : RepresentationReductionCertificate Base Γ
  notes : String := ""

/-- A classification route mechanically yields a hard relation certificate. -/
noncomputable def hardRelationCertificateOfClassificationRoute {Γ : CSP.BoolLanguage}
    (route : HardClassificationRoute Γ) :
    HardRelationCertificate Γ :=
  hardRelationCertificateOfRepresentation
    route.baseCertificate
    route.representationCertificate

/-- Convert a hard-case-to-route theorem into the certificate builder expected by wrappers. -/
noncomputable def hardRelationCertificateOfHardCaseRoute {Γ : CSP.BoolLanguage}
    (toRoute : HardCaseAssumptions Γ → HardClassificationRoute Γ) :
    HardCaseAssumptions Γ → HardRelationCertificate Γ :=
  fun hHard => hardRelationCertificateOfClassificationRoute (toRoute hHard)

/-- Package a supplied hard-case-to-route theorem as `hardSideStatement`. -/
theorem hardSideStatement_ofHardClassificationRoute {Γ : CSP.BoolLanguage}
    (toRoute : HardCaseAssumptions Γ → HardClassificationRoute Γ) :
    hardSideStatement Γ := by
  intro hHard B
  exact hardCertificate_satS_npComplete_fromBoundary
    (hardRelationCertificateOfHardCaseRoute toRoute hHard) B

/-- Boundary-explicit hard branch from a supplied local hard-classification certificate builder. -/
theorem hardCase_satS_npComplete_fromBoundary {Γ : CSP.BoolLanguage}
    (toCert : HardCaseAssumptions Γ → HardRelationCertificate Γ)
    (hHard : HardCaseAssumptions Γ) (B : Targets.ThreeSATCompleteBoundary) :
    NPCompleteEnc CostedPolyTimeModel (satSDecisionProblem Γ) :=
  hardCertificate_satS_npComplete_fromBoundary (toCert hHard) B

/-- Package a supplied local hard-classification certificate builder as `hardSideStatement`. -/
theorem hardSideStatement_ofHardCertificateBuilder {Γ : CSP.BoolLanguage}
    (toCert : HardCaseAssumptions Γ → HardRelationCertificate Γ) :
    hardSideStatement Γ := by
  intro hHard B
  exact hardCase_satS_npComplete_fromBoundary toCert hHard B

/-- Descriptor for the local representation foundation. -/
def representationFoundationDescriptor : StatementDescriptor :=
  { pdfReference := "Section 3 and Section 4 hard-side route"
    informalClaim :=
      "Local relation-representation syntax and semantics for future Schaefer \
       hard-side classification."
    localTargetSymbol := "ComplexityReduction.Schaefer.Hardness.RepresentsRelation"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Hardness.RelationFormula"
      , "ComplexityReduction.Schaefer.Hardness.LanguageRepresentation"
      , "ComplexityReduction.Schaefer.Hardness.RepresentationReductionCertificate"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "This is the local foundation.  The classification theorem from \
       HardCaseAssumptions to a representation certificate is still a separate \
       missing proof." }

/-- Descriptor for the hard-side certificate-to-NPC theorem. -/
def hardCertificateDescriptor : StatementDescriptor :=
  { pdfReference := "Section 4, proof of Theorem 2.1"
    informalClaim :=
      "A proof-bearing hard relation certificate gives conditional NP-completeness \
       of SAT(S) through the explicit 3SAT completeness boundary."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.Hardness.hardCertificate_satS_npComplete_fromBoundary"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Hardness.HardRelationCertificate"
      , "ComplexityReduction.Schaefer.Hardness.hardCertificate_satS_karp"
      , "ComplexityReduction.Schaefer.Hardness.satS_inNP_fromBoundary"
      , "ComplexityReduction.Targets.ThreeSATCompleteBoundary"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "This proves the certificate hard-side branch only.  It does not prove \
       HardCaseAssumptions Γ -> HardRelationCertificate Γ." }

/-- Descriptor for the P8f representation-to-certificate route. -/
def representationToCertificateDescriptor : StatementDescriptor :=
  { pdfReference := "Section 3 and Section 4 hard-side route"
    informalClaim :=
      "A proof-bearing relation representation reduction transports a hard base \
       certificate to a hard certificate for SAT(S)."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.Hardness.hardRelationCertificateOfRepresentation"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Hardness.formulaViaRepresentation"
      , "ComplexityReduction.Schaefer.Hardness.formulaViaRepresentation_polytime"
      , "ComplexityReduction.Schaefer.Hardness.RepresentationReductionCertificate"
      , "ComplexityReduction.Schaefer.Hardness.representationReductionCertificateOfLanguageRepresentationAuto"
      , "ComplexityReduction.Schaefer.Hardness.hardBaseCertificate_threeSATLike"
      , "ComplexityReduction.Schaefer.Hardness.hardBaseCertificate_oneInThree"
      , "ComplexityReduction.Schaefer.Hardness.hardBaseCertificate_nae3"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "This completes the reusable semantic and costed certificate route.  The full local \
       Schaefer classification theorem remains a separate missing proof: \
       HardCaseAssumptions Γ -> HardRelationCertificate Γ." }

end Hardness
end Schaefer
end ComplexityReduction
