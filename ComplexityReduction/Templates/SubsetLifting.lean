/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Templates.Structural

namespace ComplexityReduction

namespace Templates

/-- A predicate-level subset lift between two decision problems on the same encoding. -/
def subsetLift {X : EncodedType} (A B : X.Carrier → Prop)
    (h : ∀ x, A x ↔ B x) :
    SemanticReduction
      ({ Instance := X, isYes := A } : EncodedDecisionProblem)
      ({ Instance := X, isYes := B } : EncodedDecisionProblem) where
  f := id
  correct := h

/-- Costed subset lifting uses the identity map. -/
def costedSubsetLift {X : EncodedType} (A B : X.Carrier → Prop)
    (h : ∀ x, A x ↔ B x) :
    CostedReduction
      ({ Instance := X, isYes := A } : EncodedDecisionProblem)
      ({ Instance := X, isYes := B } : EncodedDecisionProblem) where
  f := id
  correct := h
  costed := CostedPolyTimeMap.id_map

/-- Log-space subset lifting uses the identity map. -/
def logSubsetLift {X : EncodedType} (A B : X.Carrier → Prop)
    (h : ∀ x, A x ↔ B x) :
    LogReductionCert
      ({ Instance := X, isYes := A } : EncodedDecisionProblem)
      ({ Instance := X, isYes := B } : EncodedDecisionProblem) where
  f := id
  correct := h
  logspace := LogSpaceMap.id_map

end Templates

end ComplexityReduction
