/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Hardness.Sublanguage
import ComplexityReduction.CSP.Examples.MixedFiniteLanguage

/-!
Reverse reductions into the mixed finite CSP language by sublanguage embedding.

The mixed language contains both the one-in-three and NAE-3 relations as named
symbols.  These maps rewrite only the relation symbol of each constraint and
preserve the variable tuple exactly, so repeated variables remain unchanged.
-/

namespace ComplexityReduction
namespace CSP
namespace Hardness
namespace MixedFiniteLanguage

open SAT
open ComplexityReduction.CSP.Examples

/-- Embed one one-in-three constraint into the mixed language. -/
def mapOneInThreeConstraintToMixed :
    Constraint oneInThreeLanguage → Constraint mixedFiniteLanguage
  | ⟨OneInThreeSymbol.rel, vars⟩ =>
      { symbol := MixedFiniteSymbol.oneInThree
        vars := vars }

/-- Embed one NAE-3 constraint into the mixed language. -/
def mapNAEConstraintToMixed :
    Constraint notAllEqual3Language → Constraint mixedFiniteLanguage
  | ⟨NAE3Symbol.rel, vars⟩ =>
      { symbol := MixedFiniteSymbol.notAllEqual3
        vars := vars }

/-- Formula-level one-in-three sublanguage embedding. -/
def oneInThreeFormulaToMixed (φ : Formula oneInThreeLanguage) : Formula mixedFiniteLanguage :=
  φ.map mapOneInThreeConstraintToMixed

/-- Formula-level NAE-3 sublanguage embedding. -/
def nae3FormulaToMixed (φ : Formula notAllEqual3Language) : Formula mixedFiniteLanguage :=
  φ.map mapNAEConstraintToMixed

@[simp]
theorem mapOneInThreeConstraint_satisfies_iff
    (c : Constraint oneInThreeLanguage) (a : Assignment) :
    Constraint.Satisfies (mapOneInThreeConstraintToMixed c) a ↔
      Constraint.Satisfies c a := by
  cases c with
  | mk symbol vars =>
      cases symbol
      rfl

@[simp]
theorem mapNAEConstraint_satisfies_iff
    (c : Constraint notAllEqual3Language) (a : Assignment) :
    Constraint.Satisfies (mapNAEConstraintToMixed c) a ↔
      Constraint.Satisfies c a := by
  cases c with
  | mk symbol vars =>
      cases symbol
      rfl

theorem oneInThreeFormulaToMixed_satisfies_iff
    (φ : Formula oneInThreeLanguage) (a : Assignment) :
    Formula.Satisfies (oneInThreeFormulaToMixed φ) a ↔ Formula.Satisfies φ a := by
  constructor
  · intro h c hc
    have hm :
        mapOneInThreeConstraintToMixed c ∈ oneInThreeFormulaToMixed φ := by
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    exact (mapOneInThreeConstraint_satisfies_iff c a).1 (h _ hm)
  · intro h c hc
    rcases List.mem_map.1 hc with ⟨d, hd, rfl⟩
    exact (mapOneInThreeConstraint_satisfies_iff d a).2 (h d hd)

theorem nae3FormulaToMixed_satisfies_iff
    (φ : Formula notAllEqual3Language) (a : Assignment) :
    Formula.Satisfies (nae3FormulaToMixed φ) a ↔ Formula.Satisfies φ a := by
  constructor
  · intro h c hc
    have hm : mapNAEConstraintToMixed c ∈ nae3FormulaToMixed φ := by
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    exact (mapNAEConstraint_satisfies_iff c a).1 (h _ hm)
  · intro h c hc
    rcases List.mem_map.1 hc with ⟨d, hd, rfl⟩
    exact (mapNAEConstraint_satisfies_iff d a).2 (h d hd)

theorem oneInThreeFormulaToMixed_satisfiable_iff (φ : Formula oneInThreeLanguage) :
    Formula.Satisfiable (oneInThreeFormulaToMixed φ) ↔ Formula.Satisfiable φ := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, (oneInThreeFormulaToMixed_satisfies_iff φ a).1 h⟩
  · rintro ⟨a, h⟩
    exact ⟨a, (oneInThreeFormulaToMixed_satisfies_iff φ a).2 h⟩

theorem nae3FormulaToMixed_satisfiable_iff (φ : Formula notAllEqual3Language) :
    Formula.Satisfiable (nae3FormulaToMixed φ) ↔ Formula.Satisfiable φ := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, (nae3FormulaToMixed_satisfies_iff φ a).1 h⟩
  · rintro ⟨a, h⟩
    exact ⟨a, (nae3FormulaToMixed_satisfies_iff φ a).2 h⟩

/-- Semantic reverse reduction from one-in-three SAT into the mixed language. -/
noncomputable def oneInThreeToMixedFiniteReduction :
    SemanticReduction oneInThreeDecisionProblem mixedFiniteDecisionProblem where
  f := oneInThreeFormulaToMixed
  correct := by
    intro φ
    exact (oneInThreeFormulaToMixed_satisfiable_iff φ).symm

/-- Semantic reverse reduction from NAE-3SAT into the mixed language. -/
noncomputable def nae3ToMixedFiniteReduction :
    SemanticReduction notAllEqual3DecisionProblem mixedFiniteDecisionProblem where
  f := nae3FormulaToMixed
  correct := by
    intro φ
    exact (nae3FormulaToMixed_satisfiable_iff φ).symm

@[simp]
theorem encodeMixedOneInThreeConstraint_length
    (c : Constraint oneInThreeLanguage) :
    (Encoding.encodeConstraint (mapOneInThreeConstraintToMixed c)).length =
      (Encoding.encodeConstraint c).length := by
  cases c with
  | mk symbol vars =>
      cases symbol
      rw [Encoding.encodeConstraint_length, Encoding.encodeConstraint_length]
      rfl

@[simp]
theorem encodeMixedNAEConstraint_length
    (c : Constraint notAllEqual3Language) :
    (Encoding.encodeConstraint (mapNAEConstraintToMixed c)).length =
      (Encoding.encodeConstraint c).length := by
  cases c with
  | mk symbol vars =>
      cases symbol
      rw [Encoding.encodeConstraint_length, Encoding.encodeConstraint_length]
      rfl

theorem oneInThreeFormulaToMixed_encodedLength_eq (φ : Formula oneInThreeLanguage) :
    (Encoding.encodeFormula (oneInThreeFormulaToMixed φ)).length =
      (Encoding.encodeFormula φ).length := by
  induction φ with
  | nil =>
      rfl
  | cons c cs ih =>
      change
        (Encoding.encodeConstraint (mapOneInThreeConstraintToMixed c) ++
            Encoding.encodeFormula (oneInThreeFormulaToMixed cs)).length =
          (Encoding.encodeConstraint c ++ Encoding.encodeFormula cs).length
      simp [ih]

theorem nae3FormulaToMixed_encodedLength_eq (φ : Formula notAllEqual3Language) :
    (Encoding.encodeFormula (nae3FormulaToMixed φ)).length =
      (Encoding.encodeFormula φ).length := by
  induction φ with
  | nil =>
      rfl
  | cons c cs ih =>
      change
        (Encoding.encodeConstraint (mapNAEConstraintToMixed c) ++
            Encoding.encodeFormula (nae3FormulaToMixed cs)).length =
          (Encoding.encodeConstraint c ++ Encoding.encodeFormula cs).length
      simp [ih]

theorem oneInThreeFormulaToMixed_linearSizeBound :
    LinearSizeBound
      (fun φ : Formula oneInThreeLanguage =>
        oneInThreeDecisionProblem.Instance.inputSize φ)
      (fun ψ : Formula mixedFiniteLanguage =>
        mixedFiniteDecisionProblem.Instance.inputSize ψ)
      oneInThreeFormulaToMixed :=
  LinearSizeBound.intro_with 1 0 (by
    intro φ
    simpa [EncodedType.inputSize, oneInThreeDecisionProblem, mixedFiniteDecisionProblem,
      boolCSPDecisionProblem, boolCSPSatLike, formulaEncodedType]
      using Nat.le_of_eq (oneInThreeFormulaToMixed_encodedLength_eq φ))

theorem nae3FormulaToMixed_linearSizeBound :
    LinearSizeBound
      (fun φ : Formula notAllEqual3Language =>
        notAllEqual3DecisionProblem.Instance.inputSize φ)
      (fun ψ : Formula mixedFiniteLanguage =>
        mixedFiniteDecisionProblem.Instance.inputSize ψ)
      nae3FormulaToMixed :=
  LinearSizeBound.intro_with 1 0 (by
    intro φ
    simpa [EncodedType.inputSize, notAllEqual3DecisionProblem, mixedFiniteDecisionProblem,
      boolCSPDecisionProblem, boolCSPSatLike, formulaEncodedType]
      using Nat.le_of_eq (nae3FormulaToMixed_encodedLength_eq φ))

/-- Proof-bearing one-in-three sublanguage embedding into the mixed language. -/
noncomputable def oneInThreeToMixedFiniteEmbedding :
    CostedSublanguageEmbedding oneInThreeLanguage mixedFiniteLanguage where
  mapConstraint := mapOneInThreeConstraintToMixed
  constraint_satisfies_iff := mapOneInThreeConstraint_satisfies_iff
  mapFormula_linearSizeBound := by
    simpa [SublanguageEmbedding.mapFormula, oneInThreeFormulaToMixed]
      using oneInThreeFormulaToMixed_linearSizeBound

/-- Proof-bearing NAE-3 sublanguage embedding into the mixed language. -/
noncomputable def nae3ToMixedFiniteEmbedding :
    CostedSublanguageEmbedding notAllEqual3Language mixedFiniteLanguage where
  mapConstraint := mapNAEConstraintToMixed
  constraint_satisfies_iff := mapNAEConstraint_satisfies_iff
  mapFormula_linearSizeBound := by
    simpa [SublanguageEmbedding.mapFormula, nae3FormulaToMixed]
      using nae3FormulaToMixed_linearSizeBound

/-- Project-local costed reverse reduction from one-in-three SAT into the mixed language. -/
noncomputable def oneInThreeToMixedFiniteCostedReduction :
    CostedReduction oneInThreeDecisionProblem mixedFiniteDecisionProblem :=
  oneInThreeToMixedFiniteEmbedding.toCostedReduction

/-- Project-local costed reverse reduction from NAE-3SAT into the mixed language. -/
noncomputable def nae3ToMixedFiniteCostedReduction :
    CostedReduction notAllEqual3DecisionProblem mixedFiniteDecisionProblem :=
  nae3ToMixedFiniteEmbedding.toCostedReduction

/-- Costed-model Karp reverse reduction from one-in-three SAT into the mixed language. -/
noncomputable def oneInThreeToMixedFiniteKarpReduction :
    KarpReductionM CostedPolyTimeModel oneInThreeDecisionProblem mixedFiniteDecisionProblem :=
  oneInThreeToMixedFiniteCostedReduction.toKarpReductionM

/-- Costed-model Karp reverse reduction from NAE-3SAT into the mixed language. -/
noncomputable def nae3ToMixedFiniteKarpReduction :
    KarpReductionM CostedPolyTimeModel notAllEqual3DecisionProblem mixedFiniteDecisionProblem :=
  nae3ToMixedFiniteCostedReduction.toKarpReductionM

end MixedFiniteLanguage
end Hardness
end CSP
end ComplexityReduction
