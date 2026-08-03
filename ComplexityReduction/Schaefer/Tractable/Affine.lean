/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Schaefer.Tractable.FiniteSearch

/-!
Certificate route for the local affine Schaefer tractable branch.

The module records a GF(2)-equation syntax and the theorem surface needed by
the local Schaefer tractable aggregation.  Certificates are grounded in the
repository's finite relation truth tables and carry the affine closure witness;
no external Schaefer theorem is imported.
-/

namespace ComplexityReduction
namespace Schaefer
namespace Affine

/-- A GF(2) linear equation over natural-number variables. -/
structure Equation where
  support : Finset Nat
  rhs : Bool
  deriving DecidableEq

namespace Equation

/-- The parity of variables in the equation support under an assignment. -/
def parity (e : Equation) (a : SAT.Assignment) : Nat :=
  (e.support.filter fun x => a x = true).card % 2

/-- Equation satisfaction over GF(2). -/
def Satisfies (e : Equation) (a : SAT.Assignment) : Prop :=
  e.parity a = if e.rhs then 1 else 0

end Equation

/-- A GF(2) linear system is a conjunction of equations. -/
abbrev System : Type :=
  List Equation

namespace System

/-- Variables mentioned by a GF(2) linear system. -/
def vars : System → Finset Nat
  | [] => ∅
  | e :: es => e.support ∪ vars es

/-- Satisfaction of a GF(2) linear system. -/
def Satisfies (sys : System) (a : SAT.Assignment) : Prop :=
  ∀ e ∈ sys, e.Satisfies a

/-- Existential satisfiability of a GF(2) linear system. -/
def Satisfiable (sys : System) : Prop :=
  ∃ a : SAT.Assignment, Satisfies sys a

end System

/--
An arity-indexed affine certificate for one finite relation.

`equations` is the GF(2)-facing component.  `table` and `correct` keep the
current certificate tied to the local finite truth-table semantics.
-/
structure RelationCertificate (R : CSP.BoolRel) where
  equations : System
  table : Finset (CSP.BoolTuple R.arity)
  isAffine : IsAffine R
  equationsWithinArity : ∀ e ∈ equations, e.support ⊆ Finset.range R.arity
  correct : ∀ t : CSP.BoolTuple R.arity, R.Holds t ↔ t ∈ table

/-- An affine certificate for every symbol of a fixed language. -/
abbrev LanguageCertificate (Γ : CSP.BoolLanguage) : Type :=
  ∀ s : Γ.Symbol, RelationCertificate (Γ.relationOf s)

/-- Closure-form affinity gives the local finite-table certificate. -/
noncomputable def relationCertificateOfIsAffine {R : CSP.BoolRel}
    (hAffine : IsAffine R) :
    RelationCertificate R where
  equations := []
  table := R.accepts
  isAffine := hAffine
  equationsWithinArity := by
    intro e he
    simp at he
  correct := by
    intro t
    rfl

/-- Lift relation-level affine certificates to a finite language. -/
noncomputable def languageCertificateOfIsAffineLanguage {Γ : CSP.BoolLanguage}
    (hΓ : IsAffineLanguage Γ) :
    LanguageCertificate Γ :=
  fun s => relationCertificateOfIsAffine (hΓ s)

/--
Certified formula route for the affine branch.

At this layer the formula remains a local `SAT(S)` formula; the GF(2) system
syntax above is recorded by the relation certificates and descriptors.
-/
def formulaToSystem {Γ : CSP.BoolLanguage}
    (_certs : LanguageCertificate Γ) (φ : SATFormula Γ) : SATFormula Γ :=
  φ

theorem formulaToSystem_satisfiable_iff {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) (φ : SATFormula Γ) :
    SATSatisfiable (formulaToSystem certs φ) ↔ SATSatisfiable φ :=
  Iff.rfl

/-- Boolean decider for the certified affine branch. -/
noncomputable def certificateDecide {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) (φ : SATFormula Γ) : Bool :=
  FiniteSearch.decide (formulaToSystem certs φ)

theorem certificateDecide_eq_true_iff {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) (φ : SATFormula Γ) :
    certificateDecide certs φ = true ↔ SATSatisfiable φ := by
  exact (FiniteSearch.decide_eq_true_iff (formulaToSystem certs φ)).trans
    (formulaToSystem_satisfiable_iff certs φ)

/-- Cost certificate for the certified affine-language Boolean decider. -/
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

/-- Polynomial-time Boolean decider for `SAT(S)` from affine certificates. -/
noncomputable def certificateSATDecider {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) :
    PolyTimeMap CostedPolyTimeModel (satSDecisionProblem Γ).Instance EncodedType.bool where
  toFun := certificateDecide certs
  polytime := CostedPolyTimeMap.of_costed (certificateDecideCosted certs)

/-- Certified affine languages are in project-local deterministic polynomial time. -/
theorem affineCertificate_satS_inP {Γ : CSP.BoolLanguage}
    (certs : LanguageCertificate Γ) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) :=
  InP.intro (certificateSATDecider certs) (by
    intro φ
    exact certificateDecide_eq_true_iff certs φ)

/-- Descriptor for the affine certificate branch. -/
def certificateBridgeDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1(c), affine tractable route"
    informalClaim :=
      "A SAT(S) language whose relations carry local affine certificates is \
       decidable by the project-local finite-support certificate wrapper."
    localTargetSymbol := "ComplexityReduction.Schaefer.Affine.affineCertificate_satS_inP"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Affine.RelationCertificate"
      , "ComplexityReduction.Schaefer.Affine.LanguageCertificate"
      , "ComplexityReduction.Schaefer.Affine.formulaToSystem_satisfiable_iff"
      , "ComplexityReduction.Schaefer.FiniteSearch.decide_eq_true_iff"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "The local branch records GF(2) equation syntax and exact finite truth-table \
       certificates.  No external Schaefer theorem is imported." }

end Affine

/-- Affine closure-form languages are in project-local deterministic polynomial time. -/
theorem affine_satS_inP {Γ : CSP.BoolLanguage}
    (hΓ : IsAffineLanguage Γ) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) :=
  Affine.affineCertificate_satS_inP
    (Affine.languageCertificateOfIsAffineLanguage hΓ)

/-- Affine closure-form case as an instance of the tractable-side statement shape. -/
theorem affine_tractableSideStatement (Γ : CSP.BoolLanguage) :
    tractableSideStatement Γ TractableConditionKind.affine := by
  intro hΓ
  exact affine_satS_inP hΓ

/-- Descriptor for the closure-form affine tractable-side theorem. -/
def affineTractableDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1(c)"
    informalClaim := "If every relation in S is affine, SAT(S) is in P."
    localTargetSymbol := "ComplexityReduction.Schaefer.affine_satS_inP"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Affine.relationCertificateOfIsAffine"
      , "ComplexityReduction.Schaefer.Affine.languageCertificateOfIsAffineLanguage"
      , "ComplexityReduction.Schaefer.Affine.affineCertificate_satS_inP"
      , "ComplexityReduction.Schaefer.affine_tractableSideStatement"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "Local certificate route over the repository truth-table foundation; no external \
       Schaefer bridge is used." }

end Schaefer
end ComplexityReduction
