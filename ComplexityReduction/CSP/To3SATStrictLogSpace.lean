/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.ToCNFStrict
import ComplexityReduction.Bridges.StrictLogSpaceTMSound

/-!
Strict log-space certificate boundary for the Boolean-CSP-to-3SAT map.

The project has a verified semantic and costed/Karp construction for every
fixed finite Boolean CSP language.  This file packages the same explicit map as
a strict streaming DAG: truth-table expansion `Formula.toCNF`, followed by
long-clause splitting `CNF.splitToThreeCNF`.  The older whole-map primitive is
retained as fallback audit metadata; the exported reduction below uses the
split certificate.  TM semantics still require an explicit
`StrictLogSpaceTMSound` witness.
-/

namespace ComplexityReduction
namespace CSP

/-- Audit metadata for the streaming unrestricted-arity CSP-to-3SAT construction. -/
noncomputable def boolCSPToThreeSATGeneralStrictPrimitive (Γ : BoolLanguage) :
    StrictLogSpacePrimitive
      (boolCSPDecisionProblem Γ).Instance
      SAT.threeSATDecisionProblem.Instance
      (fun φ => Formula.toThreeCNFGeneral φ) :=
  { name := "boolCSPToThreeSATGeneral"
    construction :=
      "Stream the input formula constraint by constraint; for each fixed relation symbol, \
       enumerate the fixed finite falsifying truth table, emit the corresponding CNF block, \
       and stream the standard long-clause splitting with a fresh-variable counter."
    space_bound :=
      "O(log |input|) work space plus language-dependent constants for the fixed finite Γ."
    oracle_free :=
      "The map inspects only syntax, fixed relation tables, and counters; it never branches on \
       source satisfiability."
    costed := (boolCSPToThreeSATGeneralKarpReduction Γ).f.polytime }

/-- Split streaming certificate for the unrestricted-arity CSP-to-3SAT map. -/
noncomputable def Formula.toThreeCNFGeneralStrictMap (Γ : BoolLanguage) :
    StrictStreamMap
      (X := (boolCSPDecisionProblem Γ).Instance)
      (Y := SAT.threeSATDecisionProblem.Instance)
      (fun φ => Formula.toThreeCNFGeneral φ) := by
  simpa [Formula.toThreeCNFGeneral, boolCSPDecisionProblem, boolCSPSatLike]
    using StrictStreamMap.comp_map
      (SAT.CNF.splitToThreeCNFStrictMap)
      (Formula.toCNFStrictMap Γ)

/-- Split strict log-space certificate for the unrestricted-arity CSP-to-3SAT map. -/
noncomputable def Formula.toThreeCNFGeneralStrictLogSpaceMap (Γ : BoolLanguage) :
    StrictLogSpaceMap
      (X := (boolCSPDecisionProblem Γ).Instance)
      (Y := SAT.threeSATDecisionProblem.Instance)
      (fun φ => Formula.toThreeCNFGeneral φ) :=
  (Formula.toThreeCNFGeneralStrictMap Γ).toStrictLogSpaceMap

/-- Strict log-space certificate for fixed finite Boolean CSP to local 3SAT. -/
noncomputable def boolCSPToThreeSATGeneralStrictLogReduction (Γ : BoolLanguage) :
    StrictLogReductionCert (boolCSPDecisionProblem Γ) SAT.threeSATDecisionProblem :=
  { f := fun φ => Formula.toThreeCNFGeneral φ
    correct := (boolCSPToThreeSATGeneralReduction Γ).correct
    strict_logspace := Formula.toThreeCNFGeneralStrictLogSpaceMap Γ }

/-- Project-local machine/log-space certificate for the unrestricted CSP-to-3SAT map. -/
noncomputable def Formula.toThreeCNFGeneralMachineMap (Γ : BoolLanguage) :
    StrictLogSpaceMachineMap
      (X := (boolCSPDecisionProblem Γ).Instance)
      (Y := SAT.threeSATDecisionProblem.Instance)
      (fun φ => Formula.toThreeCNFGeneral φ) :=
  (Formula.toThreeCNFGeneralStrictMap Γ).toMachineMap

/-- Project-local machine/log-space reduction certificate for fixed finite Boolean CSP to 3SAT. -/
noncomputable def boolCSPToThreeSATGeneralMachineReduction (Γ : BoolLanguage) :
    StrictLogSpaceMachineReductionCert (boolCSPDecisionProblem Γ) SAT.threeSATDecisionProblem :=
  { f := fun φ => Formula.toThreeCNFGeneral φ
    correct := (boolCSPToThreeSATGeneralReduction Γ).correct
    machine_logspace := Formula.toThreeCNFGeneralMachineMap Γ }

/-- Costed-model Karp reduction obtained from the project-local machine certificate. -/
noncomputable def boolCSPToThreeSATGeneralMachineKarpReduction (Γ : BoolLanguage) :
    KarpReductionM CostedPolyTimeModel (boolCSPDecisionProblem Γ) SAT.threeSATDecisionProblem :=
  (boolCSPToThreeSATGeneralMachineReduction Γ).toKarpReductionM

/--
TM-level Karp reduction obtained from the project-local machine certificate,
conditional on the strict-logspace soundness boundary.
-/
noncomputable def boolCSPToThreeSATGeneralMachineTMKarpReduction
    (hSound : StrictLogSpaceTMSound) (Γ : BoolLanguage) :
    TMKarpReduction (boolCSPDecisionProblem Γ) SAT.threeSATDecisionProblem :=
  (boolCSPToThreeSATGeneralMachineReduction Γ).toTMKarpReduction hSound

/-- Costed-model Karp reduction obtained by forgetting only the strict-logspace metadata. -/
noncomputable def boolCSPToThreeSATGeneralStrictCostedKarpReduction (Γ : BoolLanguage) :
    KarpReductionM CostedPolyTimeModel (boolCSPDecisionProblem Γ) SAT.threeSATDecisionProblem :=
  (boolCSPToThreeSATGeneralStrictLogReduction Γ).toKarpReductionM

/-- TM-level Karp reduction, conditional on strict-log-space soundness. -/
noncomputable def boolCSPToThreeSATGeneralTMKarpReduction
    (hSound : StrictLogSpaceTMSound) (Γ : BoolLanguage) :
    TMKarpReduction (boolCSPDecisionProblem Γ) SAT.threeSATDecisionProblem :=
  (boolCSPToThreeSATGeneralStrictLogReduction Γ).toTMKarpReduction hSound

/-- TM-level reducibility, conditional on strict-log-space soundness. -/
theorem boolCSPToThreeSATGeneralTMReducible
    (hSound : StrictLogSpaceTMSound) (Γ : BoolLanguage) :
    TMPolyReducible (boolCSPDecisionProblem Γ) SAT.threeSATDecisionProblem :=
  ⟨boolCSPToThreeSATGeneralTMKarpReduction hSound Γ⟩

end CSP
end ComplexityReduction
