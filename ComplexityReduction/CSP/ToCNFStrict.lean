/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.To3SATCosted
import ComplexityReduction.SAT.CNFTo3SATStrict
import ComplexityReduction.Bridges.StrictLogSpaceMachine

/-!
Strict streaming certificates for the CSP truth-table expansion phase.

The semantic construction is still `Formula.toCNF` from `ToCNF.lean`; this file
only records a decomposed project-local streaming certificate for that phase.
-/

namespace ComplexityReduction
namespace CSP

open SAT

/--
Project-local structural CNF encoded type.

The intermediate splitting phase only needs the structural CNF measure already
used by `CNFTo3SATCosted`: variable bound, total literal count, and clause
count.  This keeps the streaming DAG proof aligned with the existing costed
splitting theorem.
-/
abbrev cnfEncodedType : EncodedType :=
  SAT.cnfStructuralEncodedType

namespace Constraint

/-- Strict streaming primitive for one fixed-relation truth-table expansion block. -/
noncomputable def toCNFStrictPrimitive (Γ : BoolLanguage) :
    StrictStreamPrimitive
      (formulaEncodedType Γ)
      cnfEncodedType
      (fun φ : Formula Γ => Formula.toCNF φ) :=
  { name := "CSP.Formula.toCNF"
    pass_bound := "One left-to-right pass over the constraint list."
    workspace_bound :=
      "O(log |input|) counters plus fixed finite Γ truth-table constants."
    output_order :=
      "For each constraint, emit falsifying-tuple clauses before moving to the next constraint."
    oracle_free :=
      "The expansion reads only relation tables and variable tuples; it never branches on \
       satisfiability of the source formula."
    costed := CostedPolyTimeMap.of_costed
      (CostedMap.of_encodedPolynomialSizeBound
        (PolynomialSizeBound.intro_with 1
          (1 + Γ.maxFalsifyingTuples * Γ.maxArity + Γ.maxFalsifyingTuples) 1 (by
            intro φ
            simpa [cnfEncodedType, SAT.cnfStructuralEncodedType, EncodedType.inputSize,
              boolCSPDecisionProblem, boolCSPSatLike, formulaEncodedType]
              using Formula.toCNF_structuralSize_le_general (Γ := Γ) φ))) }

end Constraint

/-- Strict streaming map for `Formula.toCNF`. -/
noncomputable def Formula.toCNFStrictMap (Γ : BoolLanguage) :
    StrictStreamMap
      (X := formulaEncodedType Γ)
      (Y := cnfEncodedType)
      (fun φ : Formula Γ => Formula.toCNF φ) :=
  StrictStreamMap.registeredPrimitive (Constraint.toCNFStrictPrimitive Γ)

/-- Strict log-space map obtained from the streaming certificate for `Formula.toCNF`. -/
noncomputable def Formula.toCNFStrictLogSpaceMap (Γ : BoolLanguage) :
    StrictLogSpaceMap
      (X := formulaEncodedType Γ)
      (Y := cnfEncodedType)
      (fun φ : Formula Γ => Formula.toCNF φ) :=
  (Formula.toCNFStrictMap Γ).toStrictLogSpaceMap

/-- Project-local machine/log-space certificate for `Formula.toCNF`. -/
noncomputable def Formula.toCNFMachineMap (Γ : BoolLanguage) :
    StrictLogSpaceMachineMap
      (X := formulaEncodedType Γ)
      (Y := cnfEncodedType)
      (fun φ : Formula Γ => Formula.toCNF φ) :=
  (Formula.toCNFStrictMap Γ).toMachineMap

end CSP
end ComplexityReduction
