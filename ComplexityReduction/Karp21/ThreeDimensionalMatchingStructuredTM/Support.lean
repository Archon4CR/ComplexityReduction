/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatchingStructuredTM.Projections
import ComplexityReduction.Karp21.SteinerTreeStructuredTM.Support

/-!
Executable compact-support generation for the compact
Exact-Cover-to-3-Dimensional-Matching route.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

/-! ### Support list for one source set -/

abbrev compactSupportInputEncodedType : EncodedType :=
  SteinerTree.compactSupportInputEncodedType

def compactSupportExecutable (p : Nat × List Nat) : List Nat :=
  SteinerTree.compactSupportExecutable p

theorem compactSupportExecutable_eq_filter (bound : Nat) (S : List Nat) :
    compactSupportExecutable (bound, S) =
      (List.range bound).filter (fun x => HittingSet.setContainsBool (x, S)) := by
  simpa [compactSupportExecutable] using
    SteinerTree.compactSupportExecutable_eq_filter bound S

theorem compactSupportExecutable_eq_compactSupport (I : ExactCoverInput) (S : List Nat) :
    compactSupportExecutable (I.system.universeSize, S) = compactSupport I S := by
  classical
  rw [compactSupportExecutable_eq_filter]
  rw [List.range_eq_range']
  simp [compactSupport, HittingSet.setContainsBool_eq_decide]

theorem compactSupportExecutable_tm_polytime :
    TMPolyTimeMap
      compactSupportInputEncodedType
      (EncodedType.list EncodedType.nat)
      compactSupportExecutable := by
  simpa [compactSupportInputEncodedType, compactSupportExecutable] using
    SteinerTree.compactSupportExecutable_tm_polytime

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
