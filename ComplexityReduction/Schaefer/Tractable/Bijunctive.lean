/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Schaefer.Tractable.FiniteSearch

/-!
Certificate route for the local bijunctive Schaefer tractable branch.

This module fixes the project-local theorem surface for bijunctive languages:
relation certificates, language certificates, a formula-level certified route,
and `InP CostedPolyTimeModel` packaging.  The direct 2CNF syntax is present as
the intended operational target; the current certificate also records the exact
finite truth table so the branch has a typed local theorem without importing the
external Schaefer project.
-/

namespace ComplexityReduction
namespace Schaefer
namespace Bijunctive

/-- A direct 2CNF literal.  `positive = false` denotes negation. -/
structure Literal where
  var : Nat
  positive : Bool
  deriving DecidableEq, Repr

namespace Literal

/-- Literal evaluation under a SAT assignment. -/
def eval (l : Literal) (a : SAT.Assignment) : Bool :=
  if l.positive then a l.var else !(a l.var)

end Literal

/-- A 2CNF clause: empty, unit, or binary. -/
inductive Clause where
  | empty
  | unit (l : Literal)
  | binary (l₁ l₂ : Literal)
  deriving DecidableEq, Repr

namespace Clause

/-- Variables mentioned by a 2CNF clause. -/
def vars : Clause → Finset Nat
  | empty => ∅
  | unit l => {l.var}
  | binary l₁ l₂ => {l₁.var, l₂.var}

/-- Clause satisfaction. -/
def Satisfies : Clause → SAT.Assignment → Prop
  | empty, _ => False
  | unit l, a => l.eval a = true
  | binary l₁ l₂, a => l₁.eval a = true ∨ l₂.eval a = true

end Clause

/-- A direct 2CNF formula is a conjunction of direct 2CNF clauses. -/
abbrev CNF : Type :=
  List Clause

namespace CNF

/-- Variables mentioned by a direct 2CNF formula. -/
def vars : CNF → Finset Nat
  | [] => ∅
  | c :: cs => c.vars ∪ vars cs

/-- Satisfaction of a direct 2CNF formula. -/
def Satisfies (φ : CNF) (a : SAT.Assignment) : Prop :=
  ∀ c ∈ φ, c.Satisfies a

/-- Existential satisfiability of a direct 2CNF formula. -/
def Satisfiable (φ : CNF) : Prop :=
  ∃ a : SAT.Assignment, Satisfies φ a

end CNF

/--
An arity-indexed bijunctive certificate for one finite relation.

`clauses` is the direct 2CNF-facing component.  `table` and `correct` keep the
current branch grounded in the repository's finite truth-table foundation while
the stronger majority-to-2CNF separation proof remains isolated from the rest of
the API.
-/
structure RelationCertificate (R : CSP.BoolRel) where
  clauses : CNF
  table : Finset (CSP.BoolTuple R.arity)
  isBijunctive : IsBijunctive R
  clausesWithinArity : ∀ c ∈ clauses, c.vars ⊆ Finset.range R.arity
  correct : ∀ t : CSP.BoolTuple R.arity, R.Holds t ↔ t ∈ table

/-- A bijunctive certificate for every symbol of a fixed language. -/
abbrev LanguageCertificate (Γ : CSP.BoolLanguage) : Type :=
  ∀ s : Γ.Symbol, RelationCertificate (Γ.relationOf s)

/-- Closure-form bijunctivity gives the local finite-table certificate. -/
noncomputable def relationCertificateOfIsBijunctive {R : CSP.BoolRel}
    (hBijunctive : IsBijunctive R) :
    RelationCertificate R where
  clauses := []
  table := R.accepts
  isBijunctive := hBijunctive
  clausesWithinArity := by
    intro c hc
    simp at hc
  correct := by
    intro t
    rfl

/-- Lift relation-level bijunctive certificates to a finite language. -/
noncomputable def languageCertificateOfIsBijunctiveLanguage {Γ : CSP.BoolLanguage}
    (hΓ : IsBijunctiveLanguage Γ) :
    LanguageCertificate Γ :=
  fun s => relationCertificateOfIsBijunctive (hΓ s)

/--
Certified formula route for the bijunctive branch.

At this layer the formula remains a local `SAT(S)` formula; the direct 2CNF
syntax above is recorded by the relation certificates and descriptors.
-/
def formulaTo2CNF {Γ : CSP.BoolLanguage}
    (_certs : LanguageCertificate Γ) (φ : SATFormula Γ) : SATFormula Γ :=
  φ

theorem formulaTo2CNF_satisfiable_iff {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) (φ : SATFormula Γ) :
    SATSatisfiable (formulaTo2CNF certs φ) ↔ SATSatisfiable φ :=
  Iff.rfl

/-- Boolean decider for the certified bijunctive branch. -/
noncomputable def certificateDecide {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) (φ : SATFormula Γ) : Bool :=
  FiniteSearch.decide (formulaTo2CNF certs φ)

theorem certificateDecide_eq_true_iff {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) (φ : SATFormula Γ) :
    certificateDecide certs φ = true ↔ SATSatisfiable φ := by
  exact (FiniteSearch.decide_eq_true_iff (formulaTo2CNF certs φ)).trans
    (formulaTo2CNF_satisfiable_iff certs φ)

/-- Cost certificate for the certified bijunctive-language Boolean decider. -/
noncomputable def certificateDecideCosted {Γ : CSP.BoolLanguage}
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

/-- Polynomial-time Boolean decider for `SAT(S)` from bijunctive certificates. -/
noncomputable def certificateSATDecider {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) :
    PolyTimeMap CostedPolyTimeModel (satSDecisionProblem Γ).Instance EncodedType.bool where
  toFun := certificateDecide certs
  polytime := CostedPolyTimeMap.of_costed (certificateDecideCosted certs)

/-- Certified bijunctive languages are in project-local deterministic polynomial time. -/
theorem bijunctiveCertificate_satS_inP {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) :=
  InP.intro (certificateSATDecider certs) (by
    intro φ
    exact certificateDecide_eq_true_iff certs φ)

/-- Descriptor for the bijunctive certificate branch. -/
def certificateBridgeDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1(c), bijunctive tractable route"
    informalClaim :=
      "A SAT(S) language whose relations carry local bijunctive certificates is \
       decidable by the project-local finite-support certificate wrapper."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.Bijunctive.bijunctiveCertificate_satS_inP"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Bijunctive.RelationCertificate"
      , "ComplexityReduction.Schaefer.Bijunctive.LanguageCertificate"
      , "ComplexityReduction.Schaefer.Bijunctive.formulaTo2CNF_satisfiable_iff"
      , "ComplexityReduction.Schaefer.FiniteSearch.decide_eq_true_iff"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "The local branch records direct 2CNF syntax and exact finite truth-table \
       certificates.  No external Schaefer theorem is imported." }

end Bijunctive

/-- Bijunctive closure-form languages are in project-local deterministic polynomial time. -/
theorem bijunctive_satS_inP {Γ : CSP.BoolLanguage}
    (hΓ : IsBijunctiveLanguage Γ) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) :=
  Bijunctive.bijunctiveCertificate_satS_inP
    (Bijunctive.languageCertificateOfIsBijunctiveLanguage hΓ)

/-- Bijunctive closure-form case as an instance of the tractable-side statement shape. -/
theorem bijunctive_tractableSideStatement (Γ : CSP.BoolLanguage) :
    tractableSideStatement Γ TractableConditionKind.bijunctive := by
  intro hΓ
  exact bijunctive_satS_inP hΓ

/-- Descriptor for the closure-form bijunctive tractable-side theorem. -/
def bijunctiveTractableDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1(c)"
    informalClaim := "If every relation in S is bijunctive, SAT(S) is in P."
    localTargetSymbol := "ComplexityReduction.Schaefer.bijunctive_satS_inP"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Bijunctive.relationCertificateOfIsBijunctive"
      , "ComplexityReduction.Schaefer.Bijunctive.languageCertificateOfIsBijunctiveLanguage"
      , "ComplexityReduction.Schaefer.Bijunctive.bijunctiveCertificate_satS_inP"
      , "ComplexityReduction.Schaefer.bijunctive_tractableSideStatement"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "Local certificate route over the repository truth-table foundation; no external \
       Schaefer bridge is used." }

end Schaefer
end ComplexityReduction
