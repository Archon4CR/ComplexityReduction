/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.InNP
import ComplexityReduction.CSP.Hardness.NAE3SAT
import ComplexityReduction.Targets.NPCTransfer
import ComplexityReduction.Targets.ThreeSATCompleteBoundary

/-!
NP-completeness transfer for ordinary NAE-3SAT.

The boundary-explicit theorem remains available for compatibility; the local
theorem uses the P14e discharged 3SAT completeness witness.
-/

namespace ComplexityReduction
namespace CSP
namespace Hardness
namespace NAE3SAT

/-- Ordinary NAE-3SAT is in NP, conditional on local 3SAT being in NP. -/
theorem nae3InNP_of_threeSATInNP
    (h3InNP : InNPEnc CostedPolyTimeModel SAT.threeSATDecisionProblem) :
    InNPEnc CostedPolyTimeModel Examples.notAllEqual3DecisionProblem :=
  boolCSPInNP_of_threeSATInNP_threeBounded
    Examples.notAllEqual3Language_isThreeBounded h3InNP

/--
Conditional NP-completeness of ordinary NAE-3SAT when local 3SAT completeness
and NAE-3SAT NP membership are supplied explicitly.
-/
theorem nae3NPComplete_of_threeSAT
    (h3SAT : NPCompleteEnc CostedPolyTimeModel SAT.threeSATDecisionProblem)
    (hInNP : InNPEnc CostedPolyTimeModel Examples.notAllEqual3DecisionProblem) :
    NPCompleteEnc CostedPolyTimeModel Examples.notAllEqual3DecisionProblem :=
  Targets.npComplete_of_threeSAT_karp
    Examples.notAllEqual3DecisionProblem
    h3SAT
    threeSATToNAE3KarpReduction
    hInNP

/--
Short conditional NPC theorem for ordinary NAE-3SAT.  The membership side is
derived from the upper-bound reduction `NAE-3SAT <=p 3SAT` and `h3SAT.1`; the
hardness side uses the ordinary gadget reduction `3SAT <=p NAE-3SAT`.
-/
theorem nae3NPComplete_of_threeSAT_only
    (h3SAT : NPCompleteEnc CostedPolyTimeModel SAT.threeSATDecisionProblem) :
    NPCompleteEnc CostedPolyTimeModel Examples.notAllEqual3DecisionProblem :=
  nae3NPComplete_of_threeSAT
    h3SAT
    (nae3InNP_of_threeSATInNP h3SAT.1)

/-- Local NP-completeness of ordinary NAE-3SAT using the discharged P14e 3SAT theorem. -/
theorem nae3NPComplete :
    NPCompleteEnc CostedPolyTimeModel Examples.notAllEqual3DecisionProblem :=
  Targets.npComplete_of_localThreeSAT_karp
    Examples.notAllEqual3DecisionProblem
    threeSATToNAE3KarpReduction
    (nae3InNP_of_threeSATInNP Targets.localThreeSATCompleteBoundary.complete.1)

/--
Conditional NPC theorem using the centralized 3SAT-completeness boundary
wrapper.  This remains conditional; the boundary object is supplied by the
caller and this file does not assert Cook-Levin.
-/
theorem nae3NPComplete_fromBoundary
    (B : Targets.ThreeSATCompleteBoundary) :
    NPCompleteEnc CostedPolyTimeModel Examples.notAllEqual3DecisionProblem :=
  nae3NPComplete_of_threeSAT_only B.complete

end NAE3SAT
end Hardness
end CSP
end ComplexityReduction
