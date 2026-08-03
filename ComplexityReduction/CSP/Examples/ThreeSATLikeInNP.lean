/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Examples.ThreeSATLike
import ComplexityReduction.CSP.InNP

/-!
Conditional encoded-NP membership for the 3SAT-like CSP example.

The membership proof uses the upper-bound reduction `threeSATLike <=p 3SAT`.
Thus the only remaining boundary is local 3SAT membership in NP, which is
available from any future local 3SAT NP-completeness theorem.
-/

namespace ComplexityReduction
namespace CSP
namespace Examples

/-- The 3SAT-like CSP is in NP, conditional on local 3SAT being in NP. -/
theorem threeSATLikeInNP_of_threeSATInNP
    (h3InNP : InNPEnc CostedPolyTimeModel SAT.threeSATDecisionProblem) :
    InNPEnc CostedPolyTimeModel threeSATLikeDecisionProblem :=
  boolCSPInNP_of_threeSATInNP_threeBounded threeSATLikeLanguage_isThreeBounded h3InNP

end Examples
end CSP
end ComplexityReduction
