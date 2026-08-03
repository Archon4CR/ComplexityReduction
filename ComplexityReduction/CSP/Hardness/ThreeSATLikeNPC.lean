/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.Examples.ThreeSATLikeInNP
import ComplexityReduction.CSP.Hardness.ThreeSATLike
import ComplexityReduction.Targets.NPCTransfer
import ComplexityReduction.Targets.ThreeSATCompleteBoundary

/-!
NP-completeness transfer for the 3SAT-like CSP example.

The boundary-explicit theorem remains available for compatibility; the local
theorem uses the P14e discharged 3SAT completeness witness.
-/

namespace ComplexityReduction
namespace CSP
namespace Hardness
namespace ThreeSATLike

open ComplexityReduction.CSP.Examples

/--
Conditional NP-completeness of the 3SAT-like CSP when local 3SAT completeness
and 3SAT-like NP membership are supplied explicitly.
-/
theorem threeSATLikeNPComplete_of_threeSAT
    (h3SAT : NPCompleteEnc CostedPolyTimeModel SAT.threeSATDecisionProblem)
    (hInNP : InNPEnc CostedPolyTimeModel threeSATLikeDecisionProblem) :
    NPCompleteEnc CostedPolyTimeModel threeSATLikeDecisionProblem :=
  Targets.npComplete_of_threeSAT_karp
    threeSATLikeDecisionProblem
    h3SAT
    threeSATToThreeSATLikeKarpReduction
    hInNP

/--
Short conditional NPC theorem for the current catalog entry.  The membership
side is derived from the upper-bound reduction `threeSATLike <=p 3SAT` and
`h3SAT.1`; the hardness side uses `3SAT <=p threeSATLike`.
-/
theorem threeSATLikeNPComplete_of_threeSAT_only
    (h3SAT : NPCompleteEnc CostedPolyTimeModel SAT.threeSATDecisionProblem) :
    NPCompleteEnc CostedPolyTimeModel threeSATLikeDecisionProblem :=
  threeSATLikeNPComplete_of_threeSAT
    h3SAT
    (Examples.threeSATLikeInNP_of_threeSATInNP h3SAT.1)

/-- Local NP-completeness of the 3SAT-like CSP using the discharged P14e 3SAT theorem. -/
theorem threeSATLikeNPComplete :
    NPCompleteEnc CostedPolyTimeModel threeSATLikeDecisionProblem :=
  Targets.npComplete_of_localThreeSAT_karp
    threeSATLikeDecisionProblem
    threeSATToThreeSATLikeKarpReduction
    (Examples.threeSATLikeInNP_of_threeSATInNP
      Targets.localThreeSATCompleteBoundary.complete.1)

/--
Conditional NPC theorem using the centralized 3SAT-completeness boundary
wrapper.  This remains conditional; the boundary object is supplied by the
caller and this file does not assert Cook-Levin.
-/
theorem threeSATLikeNPComplete_fromBoundary
    (B : Targets.ThreeSATCompleteBoundary) :
    NPCompleteEnc CostedPolyTimeModel threeSATLikeDecisionProblem :=
  threeSATLikeNPComplete_of_threeSAT_only B.complete

end ThreeSATLike
end Hardness
end CSP
end ComplexityReduction
