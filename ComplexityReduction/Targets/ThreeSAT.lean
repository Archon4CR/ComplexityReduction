/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.SAT.ThreeSAT

/-!
Concrete local 3SAT target exports.
-/

namespace ComplexityReduction
namespace Targets

/-- Local satisfiability-style 3SAT target. -/
abbrev threeSATSatLike :=
  SAT.threeSATSatLike

/-- Local encoded 3SAT decision problem. -/
abbrev threeSATDecisionProblem :=
  SAT.threeSATDecisionProblem

end Targets
end ComplexityReduction
