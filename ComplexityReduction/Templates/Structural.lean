/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificates.ReductionCert

namespace ComplexityReduction

namespace Templates

/-- Semantic identity reduction template. -/
def semanticId (A : EncodedDecisionProblem) : SemanticReduction A A :=
  SemanticReduction.id A

/-- Semantic composition template. -/
def semanticComp {A B C : EncodedDecisionProblem}
    (rBC : SemanticReduction B C) (rAB : SemanticReduction A B) :
    SemanticReduction A C :=
  SemanticReduction.comp rBC rAB

/-- Costed identity reduction template. -/
def costedId (A : EncodedDecisionProblem) : CostedReduction A A :=
  CostedReduction.id A

/-- Costed composition template. -/
def costedComp {A B C : EncodedDecisionProblem}
    (rBC : CostedReduction B C) (rAB : CostedReduction A B) :
    CostedReduction A C :=
  CostedReduction.comp rBC rAB

/-- Log-space identity reduction template. -/
def logId (A : EncodedDecisionProblem) : LogReductionCert A A :=
  LogReductionCert.id A

/-- Product constructor for maps at the costed closure level. -/
def costedProdMk {X Y Z : EncodedType}
    {f : X.Carrier → Y.Carrier} {g : X.Carrier → Z.Carrier}
    (hf : CostedPolyTimeMap (X := X) (Y := Y) f)
    (hg : CostedPolyTimeMap (X := X) (Y := Z) g) :
    CostedPolyTimeMap (X := X) (Y := EncodedType.prod Y Z) (fun x => (f x, g x)) :=
  CostedPolyTimeMap.prod_mk_map hf hg

/-- Left sum injection at the log-space closure level. -/
def logInl (X Y : EncodedType) :
    LogSpaceMap (X := X) (Y := EncodedType.sum X Y) (@Sum.inl X.Carrier Y.Carrier) :=
  LogSpaceMap.inl_map

/-- Right sum injection at the log-space closure level. -/
def logInr (X Y : EncodedType) :
    LogSpaceMap (X := Y) (Y := EncodedType.sum X Y) (@Sum.inr X.Carrier Y.Carrier) :=
  LogSpaceMap.inr_map

end Templates

end ComplexityReduction
