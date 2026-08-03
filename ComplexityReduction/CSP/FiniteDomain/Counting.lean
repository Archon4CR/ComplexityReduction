/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import ComplexityReduction.CSP.Counting
import ComplexityReduction.CSP.FiniteDomain.FiniteSearch
import ComplexityReduction.CSP.FiniteDomain.PPBounds
import ComplexityReduction.CSP.FiniteDomain.Tiling

/-!
Finite-support solution counting for finite-domain CSP formulas.

The semantic assignments in `Basic` are total functions `Nat -> D`, so their
full type is not finite.  The counting surface below counts valuations only on
the finite support of the formula, then extends them to total assignments using
the existing `FiniteSupport.assignmentOf` wrapper.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain

namespace Formula

open FiniteSupport

/-- Finite set of satisfying valuations on the variables mentioned by a formula. -/
noncomputable def solutionSet {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} (φ : Formula Γ) :
    Finset ({x : Nat // x ∈ formulaVars φ} → D) := by
  classical
  letI : Fintype {x : Nat // x ∈ formulaVars φ} := Finset.Subtype.fintype (formulaVars φ)
  exact
    (Finset.univ : Finset ({x : Nat // x ∈ formulaVars φ} → D)).filter
      fun values => Formula.Satisfies φ (assignmentOf values)

@[simp]
theorem mem_solutionSet {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} (φ : Formula Γ)
    (values : {x : Nat // x ∈ formulaVars φ} → D) :
    values ∈ solutionSet φ ↔ Formula.Satisfies φ (assignmentOf values) := by
  classical
  unfold solutionSet
  simp

/-- Number of finite-support satisfying valuations of a formula. -/
noncomputable def solutionCount {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} (φ : Formula Γ) : Nat :=
  (solutionSet φ).card

/-- The finite-support solution set is nonempty exactly when the formula is satisfiable. -/
theorem solutionSet_nonempty_iff_satisfiable {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} (φ : Formula Γ) :
    (solutionSet φ).Nonempty ↔ Formula.Satisfiable φ := by
  classical
  constructor
  · rintro ⟨values, hvalues⟩
    exact ⟨assignmentOf values, (mem_solutionSet φ values).1 hvalues⟩
  · rintro ⟨a, hSat⟩
    let values : {x : Nat // x ∈ formulaVars φ} → D := fun x => a x.val
    refine ⟨values, (mem_solutionSet φ values).2 ?_⟩
    exact (formula_satisfies_iff_of_agree (φ := φ)
      (a := assignmentOf values) (b := a) (by
        intro x hx
        simp [assignmentOf, hx, values])).2 hSat

/-- Positive solution count is the finite-support counting form of satisfiability. -/
theorem solutionCount_pos_iff_satisfiable {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} (φ : Formula Γ) :
    0 < solutionCount φ ↔ Formula.Satisfiable φ := by
  rw [solutionCount, Finset.card_pos]
  exact solutionSet_nonempty_iff_satisfiable φ

end Formula

/-- Counting problem associated to a fixed finite-domain CSP language. -/
noncomputable def countingProblem {D : Type} [Fintype D] [Inhabited D] (Γ : Language D) :
    CSP.CountingProblem := by
  classical
  exact
    { Instance := formulaEncodedType Γ
      count := fun φ => Formula.solutionCount φ }

@[simp]
theorem countingProblem_count {D : Type} [Fintype D] [Inhabited D] (Γ : Language D)
    (φ : Formula Γ) :
    (countingProblem Γ).count φ = Formula.solutionCount φ := by
  classical
  rfl

/-- Forgetting counts from the fixed-language counting problem recovers CSP satisfiability. -/
theorem countingProblem_decision_iff_satisfiable {D : Type} [Fintype D] [Inhabited D]
    (Γ : Language D) (φ : Formula Γ) :
    (countingProblem Γ).isYes φ ↔ Formula.Satisfiable φ := by
  classical
  simpa [CSP.CountingProblem.isYes, countingProblem] using
    Formula.solutionCount_pos_iff_satisfiable (Γ := Γ) φ

namespace PPDef

/-- A pp-representation together with an explicit proof that expansion preserves counts. -/
structure CountPreservingRepresentationCertificate {D : Type} [Fintype D] [Inhabited D]
    (Δ Γ : Language D) where
  representation : LanguageRepresentation Δ Γ
  count_preserving :
    ∀ φ : Formula Δ,
      Formula.solutionCount (formulaViaRepresentation representation φ) =
        Formula.solutionCount φ
  notes : String := ""

/--
Use a count-preserving pp-representation certificate to rewrite the solution
count of the automatically bounded pp expansion.
-/
theorem solutionCount_viaRepresentation {D : Type} [Fintype D] [Inhabited D]
    {Δ Γ : Language D} (cert : CountPreservingRepresentationCertificate Δ Γ)
    (φ : Formula Δ) :
    Formula.solutionCount (formulaViaRepresentation cert.representation φ) =
      Formula.solutionCount φ :=
  cert.count_preserving φ

end PPDef

namespace Tiling

namespace TilingInstance

/-- Finite-support satisfying placements for a tiling instance, via its CSP formula. -/
noncomputable def solutionSet {P : TilePalette} [Inhabited P.State] (I : TilingInstance P) :
    Finset ({x : Nat // x ∈ FiniteSupport.formulaVars I.tilingFormula} → P.State) :=
  Formula.solutionSet I.tilingFormula

/-- Number of finite-support satisfying placements of a tiling instance. -/
noncomputable def solutionCount {P : TilePalette} [Inhabited P.State] (I : TilingInstance P) :
    Nat :=
  Formula.solutionCount I.tilingFormula

@[simp]
theorem solutionCount_eq_formula_solutionCount {P : TilePalette} [Inhabited P.State]
    (I : TilingInstance P) :
    I.solutionCount = Formula.solutionCount I.tilingFormula :=
  rfl

/-- Positive tiling solution count is exactly local tileability. -/
theorem solutionCount_pos_iff_tileable {P : TilePalette} [Inhabited P.State]
    (I : TilingInstance P) :
    0 < I.solutionCount ↔ I.Tileable := by
  calc
    0 < I.solutionCount ↔ Formula.Satisfiable I.tilingFormula := by
      simpa [solutionCount] using Formula.solutionCount_pos_iff_satisfiable I.tilingFormula
    _ ↔ I.Tileable := I.tilingFormula_satisfiable_iff

end TilingInstance

end Tiling

end FiniteDomain
end CSP
end ComplexityReduction
