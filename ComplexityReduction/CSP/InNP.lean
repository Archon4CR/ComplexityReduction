/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.To3SATCosted

/-!
Encoded-NP membership closure facts for Boolean CSPs.

These theorems intentionally avoid asserting Cook-Levin or local 3SAT
membership.  They say that once local 3SAT is known to be in NP, every fixed
finite Boolean CSP language is also in NP via the already verified upper-bound
Karp reduction to local 3SAT.
-/

namespace ComplexityReduction
namespace CSP

/-- Every fixed finite Boolean CSP is in NP, conditional on local 3SAT being in NP. -/
theorem boolCSPInNP_of_threeSATInNP (Γ : BoolLanguage)
    (h3InNP : InNPEnc CostedPolyTimeModel SAT.threeSATDecisionProblem) :
    InNPEnc CostedPolyTimeModel (boolCSPDecisionProblem Γ) :=
  InNPEnc.of_reduction
    ⟨boolCSPToThreeSATGeneralKarpReduction Γ⟩
    h3InNP

/-- Arity-at-most-three specialization using the linear upper-bound Karp reduction. -/
theorem boolCSPInNP_of_threeSATInNP_threeBounded {Γ : BoolLanguage}
    (hΓ : Γ.IsThreeBounded)
    (h3InNP : InNPEnc CostedPolyTimeModel SAT.threeSATDecisionProblem) :
    InNPEnc CostedPolyTimeModel (boolCSPDecisionProblem Γ) :=
  InNPEnc.of_reduction
    ⟨boolCSPToThreeSATKarpReduction hΓ⟩
    h3InNP

end CSP
end ComplexityReduction
