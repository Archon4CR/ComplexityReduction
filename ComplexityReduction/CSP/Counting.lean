/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Core.EncodedDecisionProblem

/-!
Counting-problem and counting-reduction metadata.

This module deliberately contains only the generic finite-counting interface.
It distinguishes ordinary decision-preserving routes from count-preserving and
parsimonious routes without asserting any counting hardness theorem.
-/

namespace ComplexityReduction
namespace CSP

/-- A problem whose instances carry a natural-number count of accepting witnesses. -/
structure CountingProblem where
  Instance : EncodedType
  count : Instance.Carrier → Nat

namespace CountingProblem

/-- The associated decision predicate: at least one witness is counted. -/
def isYes (P : CountingProblem) (x : P.Instance.Carrier) : Prop :=
  0 < P.count x

/-- The decision problem obtained by forgetting exact counts. -/
def decisionProblem (P : CountingProblem) : EncodedDecisionProblem where
  Instance := P.Instance
  isYes := P.isYes

@[simp]
theorem decisionProblem_isYes_iff (P : CountingProblem) (x : P.Instance.Carrier) :
    P.decisionProblem.isYes x ↔ 0 < P.count x :=
  Iff.rfl

end CountingProblem

/-- A map preserving exact witness counts. -/
structure CountingReduction (P Q : CountingProblem) where
  map : P.Instance.Carrier → Q.Instance.Carrier
  count_preserving : ∀ x, Q.count (map x) = P.count x

namespace CountingReduction

/-- A count-preserving map preserves the induced decision predicate. -/
theorem map_isYes_iff {P Q : CountingProblem} (R : CountingReduction P Q)
    (x : P.Instance.Carrier) :
    Q.isYes (R.map x) ↔ P.isYes x := by
  simp [CountingProblem.isYes, R.count_preserving x]

end CountingReduction

/--
Parsimonious reductions are recorded separately for planner intent.  Locally
they expose the same exact-count preservation theorem; concrete witness
bijections belong in domain-specific certificates.
-/
structure ParsimoniousReduction (P Q : CountingProblem)
    extends CountingReduction P Q where
  notes : String := ""

namespace ParsimoniousReduction

/-- A parsimonious reduction preserves the induced decision predicate. -/
theorem map_isYes_iff {P Q : CountingProblem} (R : ParsimoniousReduction P Q)
    (x : P.Instance.Carrier) :
    Q.isYes (R.map x) ↔ P.isYes x :=
  R.toCountingReduction.map_isYes_iff x

end ParsimoniousReduction

/-- Planner-facing status for claims about a reduction's witness-count behavior. -/
inductive CountPreservationStatus where
  | decisionOnly
  | countPreserving
  | parsimonious
  | sourceGated
  deriving DecidableEq, Repr

namespace CountPreservationStatus

/-- Stable string label for counting-preservation route metadata. -/
def label : CountPreservationStatus → String
  | decisionOnly => "decision_only"
  | countPreserving => "count_preserving"
  | parsimonious => "parsimonious"
  | sourceGated => "source_gated"

/-- Whether this status exposes a theorem as a count-preservation fact. -/
def generatorMayUseAsCountingTheorem : CountPreservationStatus → Bool
  | countPreserving => true
  | parsimonious => true
  | decisionOnly => false
  | sourceGated => false

@[simp]
theorem decisionOnly_not_countingTheorem :
    CountPreservationStatus.decisionOnly.generatorMayUseAsCountingTheorem = false :=
  rfl

@[simp]
theorem sourceGated_not_countingTheorem :
    CountPreservationStatus.sourceGated.generatorMayUseAsCountingTheorem = false :=
  rfl

@[simp]
theorem countPreserving_countingTheorem :
    CountPreservationStatus.countPreserving.generatorMayUseAsCountingTheorem = true :=
  rfl

@[simp]
theorem parsimonious_countingTheorem :
    CountPreservationStatus.parsimonious.generatorMayUseAsCountingTheorem = true :=
  rfl

end CountPreservationStatus

/-- Planner metadata for one counting route or source-gated counting claim. -/
structure CountingRouteDescriptor where
  name : String
  sourceSymbol : String
  targetSymbol : String
  countTheorem : Option String
  status : CountPreservationStatus
  roles : List String
  notes : List String
  deriving Repr

namespace CountingRouteDescriptor

/-- The route may be used as a count theorem exactly when its status permits it. -/
def generatorMayUseAsCountingTheorem (desc : CountingRouteDescriptor) : Bool :=
  desc.status.generatorMayUseAsCountingTheorem

end CountingRouteDescriptor

end CSP
end ComplexityReduction
