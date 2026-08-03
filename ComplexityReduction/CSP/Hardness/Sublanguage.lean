/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.To3SATCosted

/-!
Reusable template for hard sublanguage embeddings.

Many Boolean-CSP hard-case proofs first show that a known hard language embeds
into a larger language by rewriting relation symbols and preserving variable
tuples.  This file packages that pattern without committing to a particular
dependent arity-cast representation.
-/

namespace ComplexityReduction
namespace CSP
namespace Hardness

open SAT

/-- A proof-bearing constraint rewrite from language `Γ` to language `Δ`. -/
structure SublanguageEmbedding (Γ Δ : BoolLanguage) where
  mapConstraint : Constraint Γ → Constraint Δ
  constraint_satisfies_iff :
    ∀ c a, Constraint.Satisfies (mapConstraint c) a ↔ Constraint.Satisfies c a

namespace SublanguageEmbedding

/-- Formula-level map induced by a sublanguage embedding. -/
def mapFormula {Γ Δ : BoolLanguage} (e : SublanguageEmbedding Γ Δ)
    (φ : Formula Γ) : Formula Δ :=
  φ.map e.mapConstraint

theorem mapFormula_satisfies_iff {Γ Δ : BoolLanguage}
    (e : SublanguageEmbedding Γ Δ) (φ : Formula Γ) (a : Assignment) :
    Formula.Satisfies (e.mapFormula φ) a ↔ Formula.Satisfies φ a := by
  constructor
  · intro h c hc
    have hm : e.mapConstraint c ∈ e.mapFormula φ := List.mem_map.mpr ⟨c, hc, rfl⟩
    exact (e.constraint_satisfies_iff c a).1 (h _ hm)
  · intro h c hc
    rcases List.mem_map.1 hc with ⟨d, hd, rfl⟩
    exact (e.constraint_satisfies_iff d a).2 (h d hd)

theorem mapFormula_satisfiable_iff {Γ Δ : BoolLanguage}
    (e : SublanguageEmbedding Γ Δ) (φ : Formula Γ) :
    Formula.Satisfiable (e.mapFormula φ) ↔ Formula.Satisfiable φ := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, (e.mapFormula_satisfies_iff φ a).1 h⟩
  · rintro ⟨a, h⟩
    exact ⟨a, (e.mapFormula_satisfies_iff φ a).2 h⟩

/-- Semantic reduction induced by a sublanguage embedding. -/
noncomputable def toSemanticReduction {Γ Δ : BoolLanguage}
    (e : SublanguageEmbedding Γ Δ) :
    SemanticReduction (boolCSPDecisionProblem Γ) (boolCSPDecisionProblem Δ) where
  f := e.mapFormula
  correct := by
    intro φ
    exact (e.mapFormula_satisfiable_iff φ).symm

end SublanguageEmbedding

/-- A sublanguage embedding with a project-local linear encoded-size bound. -/
structure CostedSublanguageEmbedding (Γ Δ : BoolLanguage)
    extends SublanguageEmbedding Γ Δ where
  mapFormula_linearSizeBound :
    LinearSizeBound
      (fun φ : Formula Γ => (boolCSPDecisionProblem Γ).Instance.inputSize φ)
      (fun ψ : Formula Δ => (boolCSPDecisionProblem Δ).Instance.inputSize ψ)
      toSublanguageEmbedding.mapFormula

namespace CostedSublanguageEmbedding

/-- Costed reduction induced by a costed sublanguage embedding. -/
noncomputable def toCostedReduction {Γ Δ : BoolLanguage}
    (e : CostedSublanguageEmbedding Γ Δ) :
    CostedReduction (boolCSPDecisionProblem Γ) (boolCSPDecisionProblem Δ) :=
  CostedReduction.ofCostedMap
    e.toSublanguageEmbedding.mapFormula
    e.toSublanguageEmbedding.toSemanticReduction.correct
    (CostedMap.of_encodedLinearSizeBound e.mapFormula_linearSizeBound)

/-- Costed-model Karp reduction induced by a costed sublanguage embedding. -/
noncomputable def toKarpReduction {Γ Δ : BoolLanguage}
    (e : CostedSublanguageEmbedding Γ Δ) :
    KarpReductionM CostedPolyTimeModel
      (boolCSPDecisionProblem Γ) (boolCSPDecisionProblem Δ) :=
  e.toCostedReduction.toKarpReductionM

end CostedSublanguageEmbedding

end Hardness
end CSP
end ComplexityReduction
