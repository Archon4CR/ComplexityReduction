/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.CSP.FiniteDomain.Gadgets
import ComplexityReduction.CSP.FiniteDomain.Polymorphisms

/-!
Preservation lemmas for finite-domain polymorphisms.

These theorems package the standard algebraic CSP fact that polymorphisms of a
target language preserve all formulas over that language, and therefore also
preserve pp-defined and pp-represented source relations.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain

namespace Operation

theorem assignmentTuple_applyAssignment {D : Type} {Γ : Language D} {n : Nat}
    (op : Operation D n) (rows : Fin n → Assignment D) (c : Constraint Γ) :
    Constraint.assignmentTuple c (applyAssignment op rows) =
      applyTuple op (fun j => Constraint.assignmentTuple c (rows j)) := by
  funext i
  rfl

theorem extendTupleAssignment_applyAssignment {D : Type} {n arity : Nat}
    (op : Operation D n) (rows : Fin n → Tuple D arity)
    (auxRows : Fin n → Assignment D) :
    applyAssignment op (fun j => PPDef.extendTupleAssignment (rows j) (auxRows j)) =
      PPDef.extendTupleAssignment
        (applyTuple op rows)
        (applyAssignment op auxRows) := by
  funext x
  by_cases hx : x < arity
  · simp [applyAssignment, PPDef.extendTupleAssignment, hx]
  · simp [applyAssignment, PPDef.extendTupleAssignment, hx]

end Operation

namespace PreservesRel

theorem constraint_satisfies {D : Type} {Γ : Language D} {n : Nat}
    {op : Operation D n} {c : Constraint Γ}
    (h : PreservesRel op (Γ.relationOf c.symbol))
    {rows : Fin n → Assignment D}
    (hRows : ∀ j, Constraint.Satisfies c (rows j)) :
    Constraint.Satisfies c (Operation.applyAssignment op rows) := by
  have hTuple := Operation.assignmentTuple_applyAssignment op rows c
  have hOut := h (fun j => Constraint.assignmentTuple c (rows j)) (by
    intro j
    exact hRows j)
  simpa [Constraint.Satisfies, hTuple] using hOut

end PreservesRel

namespace PreservesLanguage

theorem formula_satisfies {D : Type} {Γ : Language D} {n : Nat}
    {op : Operation D n} (hΓ : PreservesLanguage op Γ)
    {φ : Formula Γ} {rows : Fin n → Assignment D}
    (hRows : ∀ j, Formula.Satisfies φ (rows j)) :
    Formula.Satisfies φ (Operation.applyAssignment op rows) := by
  intro c hc
  exact PreservesRel.constraint_satisfies (hΓ c.symbol) (fun j => hRows j c hc)

theorem pp_definedRel {D : Type} {Γ : Language D} {n : Nat}
    {op : Operation D n} (hΓ : PreservesLanguage op Γ)
    {arity : Nat} (rep : PPDef.RelationFormula Γ arity) :
    PreservesRel op rep.definedRel := by
  classical
  intro rows hRows
  have hRowsExists :
      ∀ j, ∃ aux : Assignment D,
        Formula.Satisfies rep.constraints (PPDef.extendTupleAssignment (rows j) aux) := by
    intro j
    simpa [PPDef.RelationFormula.definedRel, Rel.Holds] using hRows j
  let auxRows : Fin n → Assignment D := fun j => Classical.choose (hRowsExists j)
  have hAuxRows :
      ∀ j,
        Formula.Satisfies rep.constraints
          (PPDef.extendTupleAssignment (rows j) (auxRows j)) := by
    intro j
    exact Classical.choose_spec (hRowsExists j)
  let rowAssignments : Fin n → Assignment D := fun j =>
    PPDef.extendTupleAssignment (rows j) (auxRows j)
  have hFormula :
      Formula.Satisfies rep.constraints
        (Operation.applyAssignment op rowAssignments) := by
    exact formula_satisfies hΓ (fun j => hAuxRows j)
  let auxOut : Assignment D := Operation.applyAssignment op auxRows
  change ∃ aux : Assignment D,
    Formula.Satisfies rep.constraints
      (PPDef.extendTupleAssignment (Operation.applyTuple op rows) aux)
  refine ⟨auxOut, ?_⟩
  have hEq :
      Operation.applyAssignment op rowAssignments =
        PPDef.extendTupleAssignment (Operation.applyTuple op rows) auxOut := by
    simpa [rowAssignments, auxOut] using
      Operation.extendTupleAssignment_applyAssignment op rows auxRows
  simpa [hEq] using hFormula

theorem pp_representedRel {D : Type} {Γ : Language D} {n : Nat}
    {op : Operation D n} (hΓ : PreservesLanguage op Γ)
    {R : Rel D} (rep : PPDef.RelationFormula Γ R.arity)
    (hRep : PPDef.RepresentsRelation Γ R rep) :
    PreservesRel op R := by
  intro rows hRows
  have hRowsDefined :
      ∀ j, rep.definedRel.Holds (rows j) := by
    intro j
    exact (hRep (rows j)).1 (hRows j)
  have hDefined := pp_definedRel hΓ rep rows hRowsDefined
  exact (hRep (Operation.applyTuple op rows)).2 (by
    simpa [PPDef.RelationFormula.definedRel, Rel.Holds] using hDefined)

theorem of_representation {D : Type} {Δ Γ : Language D} {n : Nat}
    {op : Operation D n} (hΓ : PreservesLanguage op Γ)
    (rep : PPDef.LanguageRepresentation Δ Γ) :
    PreservesLanguage op Δ := by
  intro s
  exact pp_representedRel hΓ (rep.block s) (rep.represents s)

end PreservesLanguage

namespace Polymorphism

theorem formula_satisfies {D : Type} {Γ : Language D} {n : Nat}
    (p : Polymorphism Γ n) {φ : Formula Γ} {rows : Fin n → Assignment D}
    (hRows : ∀ j, Formula.Satisfies φ (rows j)) :
    Formula.Satisfies φ (Operation.applyAssignment p.op rows) :=
  PreservesLanguage.formula_satisfies p.preserves hRows

def through_representation {D : Type} {Δ Γ : Language D} {n : Nat}
    (p : Polymorphism Γ n) (rep : PPDef.LanguageRepresentation Δ Γ) :
    Polymorphism Δ n where
  op := p.op
  preserves := PreservesLanguage.of_representation p.preserves rep

end Polymorphism

end FiniteDomain
end CSP
end ComplexityReduction
