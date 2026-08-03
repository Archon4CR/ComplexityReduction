/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Schaefer.Tractable.Horn
import ComplexityReduction.Schaefer.Tractable.Bijunctive
import ComplexityReduction.Schaefer.Tractable.Affine

/-!
First local tractable-side certificates for Schaefer `SAT(S)`.

This module aggregates locally proved tractable-side cases of Theorem 2.1:
zero-valid, one-valid, Horn, dual-Horn, bijunctive, and affine languages.
-/

namespace ComplexityReduction
namespace Schaefer

/-- The all-false assignment used by the zero-valid tractable case. -/
def zeroAssignment : SAT.Assignment :=
  fun _ => false

/-- The all-true assignment used by the one-valid tractable case. -/
def oneAssignment : SAT.Assignment :=
  fun _ => true

/-- Any constraint over a zero-valid language is satisfied by the all-false assignment. -/
theorem zeroValid_constraint_satisfies {Γ : CSP.BoolLanguage}
    (hΓ : IsZeroValidLanguage Γ) (c : CSP.Constraint Γ) :
    CSP.Constraint.Satisfies c zeroAssignment := by
  simpa [IsZeroValidLanguage, LanguageSatisfies, RelationSatisfies,
    CSP.Constraint.Satisfies, CSP.Constraint.assignmentTuple, zeroAssignment,
    BoolTuple.constFalse] using hΓ c.symbol

/-- Any formula over a zero-valid language is satisfied by the all-false assignment. -/
theorem zeroValid_formula_satisfies {Γ : CSP.BoolLanguage}
    (hΓ : IsZeroValidLanguage Γ) (φ : SATFormula Γ) :
    CSP.Formula.Satisfies φ zeroAssignment := by
  intro c _hc
  exact zeroValid_constraint_satisfies hΓ c

/-- Every formula over a zero-valid language is satisfiable. -/
theorem zeroValid_formula_satisfiable {Γ : CSP.BoolLanguage}
    (hΓ : IsZeroValidLanguage Γ) (φ : SATFormula Γ) :
    SATSatisfiable φ := by
  exact ⟨zeroAssignment, zeroValid_formula_satisfies hΓ φ⟩

/-- Any constraint over a one-valid language is satisfied by the all-true assignment. -/
theorem oneValid_constraint_satisfies {Γ : CSP.BoolLanguage}
    (hΓ : IsOneValidLanguage Γ) (c : CSP.Constraint Γ) :
    CSP.Constraint.Satisfies c oneAssignment := by
  simpa [IsOneValidLanguage, LanguageSatisfies, RelationSatisfies,
    CSP.Constraint.Satisfies, CSP.Constraint.assignmentTuple, oneAssignment,
    BoolTuple.constTrue] using hΓ c.symbol

/-- Any formula over a one-valid language is satisfied by the all-true assignment. -/
theorem oneValid_formula_satisfies {Γ : CSP.BoolLanguage}
    (hΓ : IsOneValidLanguage Γ) (φ : SATFormula Γ) :
    CSP.Formula.Satisfies φ oneAssignment := by
  intro c _hc
  exact oneValid_constraint_satisfies hΓ c

/-- Every formula over a one-valid language is satisfiable. -/
theorem oneValid_formula_satisfiable {Γ : CSP.BoolLanguage}
    (hΓ : IsOneValidLanguage Γ) (φ : SATFormula Γ) :
    SATSatisfiable φ := by
  exact ⟨oneAssignment, oneValid_formula_satisfies hΓ φ⟩

/-- Constant-true Boolean decider for a `SAT(S)` problem. -/
def constantTrueSATDecider (Γ : CSP.BoolLanguage) :
    PolyTimeMap CostedPolyTimeModel (satSDecisionProblem Γ).Instance EncodedType.bool :=
  PolyTimeMap.const CostedPolyTimeModel (satSDecisionProblem Γ).Instance EncodedType.bool true

/-- Zero-valid languages are in P by the all-false satisfying assignment. -/
theorem zeroValid_satS_inP {Γ : CSP.BoolLanguage}
    (hΓ : IsZeroValidLanguage Γ) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) :=
  InP.intro (constantTrueSATDecider Γ) (by
    intro φ
    constructor
    · intro _h
      exact zeroValid_formula_satisfiable hΓ φ
    · intro _h
      rfl)

/-- One-valid languages are in P by the all-true satisfying assignment. -/
theorem oneValid_satS_inP {Γ : CSP.BoolLanguage}
    (hΓ : IsOneValidLanguage Γ) :
    InP CostedPolyTimeModel (satSDecisionProblem Γ) :=
  InP.intro (constantTrueSATDecider Γ) (by
    intro φ
    constructor
    · intro _h
      exact oneValid_formula_satisfiable hΓ φ
    · intro _h
      rfl)

/-- Zero-valid case as an instance of the common tractable-side statement shape. -/
theorem zeroValid_tractableSideStatement (Γ : CSP.BoolLanguage) :
    tractableSideStatement Γ TractableConditionKind.zeroValid := by
  intro hΓ
  exact zeroValid_satS_inP hΓ

/-- One-valid case as an instance of the common tractable-side statement shape. -/
theorem oneValid_tractableSideStatement (Γ : CSP.BoolLanguage) :
    tractableSideStatement Γ TractableConditionKind.oneValid := by
  intro hΓ
  exact oneValid_satS_inP hΓ

/-- Descriptor for the zero-valid tractable-side theorem. -/
def zeroValidTractableDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1(a)"
    informalClaim := "If every relation in S is zero-valid, SAT(S) is polynomial-time decidable."
    localTargetSymbol := "ComplexityReduction.Schaefer.zeroValid_satS_inP"
    dependencies :=
      [ "ComplexityReduction.Schaefer.zeroAssignment"
      , "ComplexityReduction.Schaefer.zeroValid_formula_satisfiable"
      , "ComplexityReduction.Schaefer.constantTrueSATDecider"
      , "ComplexityReduction.Schaefer.zeroValid_tractableSideStatement"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes := "Local proof uses the all-false assignment and a constant-true costed decider." }

/-- Descriptor for the one-valid tractable-side theorem. -/
def oneValidTractableDescriptor : StatementDescriptor :=
  { pdfReference := "Section 2, Theorem 2.1(b)"
    informalClaim := "If every relation in S is one-valid, SAT(S) is polynomial-time decidable."
    localTargetSymbol := "ComplexityReduction.Schaefer.oneValid_satS_inP"
    dependencies :=
      [ "ComplexityReduction.Schaefer.oneAssignment"
      , "ComplexityReduction.Schaefer.oneValid_formula_satisfiable"
      , "ComplexityReduction.Schaefer.constantTrueSATDecider"
      , "ComplexityReduction.Schaefer.oneValid_tractableSideStatement"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes := "Local proof uses the all-true assignment and a constant-true costed decider." }

/-- Tractable-side descriptors that are already locally proved. -/
def provedTractableDescriptors : List StatementDescriptor :=
  [ zeroValidTractableDescriptor
  , oneValidTractableDescriptor
  , hornClosureTractableDescriptor
  , dualHornClosureTractableDescriptor
  , bijunctiveTractableDescriptor
  , affineTractableDescriptor
  ]

theorem provedTractableDescriptors_length :
    provedTractableDescriptors.length = 6 :=
  rfl

end Schaefer
end ComplexityReduction
