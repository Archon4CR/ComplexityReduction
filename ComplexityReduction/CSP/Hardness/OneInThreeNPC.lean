/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.InNP
import ComplexityReduction.CSP.Hardness.OneInThree
import ComplexityReduction.Targets.NPCTransfer
import ComplexityReduction.Targets.ThreeSATCompleteBoundary

/-!
NP-completeness transfer for ordinary one-in-three SAT.

The boundary-explicit theorem remains available for compatibility; the local
theorem uses the P14e discharged 3SAT completeness witness.
-/

namespace ComplexityReduction
namespace CSP
namespace Hardness
namespace OneInThree

/-- Ordinary one-in-three SAT is in NP, conditional on local 3SAT being in NP. -/
theorem oneInThreeInNP_of_threeSATInNP
    (h3InNP : InNPEnc CostedPolyTimeModel SAT.threeSATDecisionProblem) :
    InNPEnc CostedPolyTimeModel Examples.oneInThreeDecisionProblem :=
  boolCSPInNP_of_threeSATInNP_threeBounded
    Examples.oneInThreeLanguage_isThreeBounded h3InNP

/--
Conditional NP-completeness of ordinary one-in-three SAT when local 3SAT
completeness and one-in-three NP membership are supplied explicitly.
-/
theorem oneInThreeNPComplete_of_threeSAT
    (h3SAT : NPCompleteEnc CostedPolyTimeModel SAT.threeSATDecisionProblem)
    (hInNP : InNPEnc CostedPolyTimeModel Examples.oneInThreeDecisionProblem) :
    NPCompleteEnc CostedPolyTimeModel Examples.oneInThreeDecisionProblem :=
  Targets.npComplete_of_threeSAT_karp
    Examples.oneInThreeDecisionProblem
    h3SAT
    threeSATToOneInThreeKarpReduction
    hInNP

/--
Short conditional NPC theorem for ordinary one-in-three SAT. The membership side
is derived from the upper-bound reduction `one-in-three SAT <=p 3SAT` and
`h3SAT.1`; the hardness side uses the ordinary gadget reduction
`3SAT <=p one-in-three SAT`.
-/
theorem oneInThreeNPComplete_of_threeSAT_only
    (h3SAT : NPCompleteEnc CostedPolyTimeModel SAT.threeSATDecisionProblem) :
    NPCompleteEnc CostedPolyTimeModel Examples.oneInThreeDecisionProblem :=
  oneInThreeNPComplete_of_threeSAT
    h3SAT
    (oneInThreeInNP_of_threeSATInNP h3SAT.1)

/-- Local NP-completeness of ordinary one-in-three SAT using the discharged P14e 3SAT theorem. -/
theorem oneInThreeNPComplete :
    NPCompleteEnc CostedPolyTimeModel Examples.oneInThreeDecisionProblem :=
  Targets.npComplete_of_localThreeSAT_karp
    Examples.oneInThreeDecisionProblem
    threeSATToOneInThreeKarpReduction
    (oneInThreeInNP_of_threeSATInNP Targets.localThreeSATCompleteBoundary.complete.1)

/--
Conditional NPC theorem using the centralized 3SAT-completeness boundary
wrapper. This remains conditional; the boundary object is supplied by the caller
and this file does not assert Cook-Levin.
-/
theorem oneInThreeNPComplete_fromBoundary
    (B : Targets.ThreeSATCompleteBoundary) :
    NPCompleteEnc CostedPolyTimeModel Examples.oneInThreeDecisionProblem :=
  oneInThreeNPComplete_of_threeSAT_only B.complete

end OneInThree
end Hardness
end CSP
end ComplexityReduction
