/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificates.StrictStreamMap

/-!
Reusable strict streaming certificates for list-shaped maps.

These definitions are deliberately thin wrappers around `StrictStreamMap`
constructors.  They give generated reductions stable names for common list
combinators without changing the certificate boundary.
-/

namespace ComplexityReduction
namespace Templates
namespace StrictLists

/-- Strict streaming certificate for list append. -/
def append (X : EncodedType) :
    StrictStreamMap
      (X := EncodedType.prod (EncodedType.list X) (EncodedType.list X))
      (Y := EncodedType.list X)
      (fun p : List X.Carrier × List X.Carrier => p.1 ++ p.2) :=
  StrictStreamMap.list_append_map

/-- Strict streaming certificate for mapping a certified element map over a list. -/
def map {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (hf : StrictStreamMap (X := X) (Y := Y) f) :
    StrictStreamMap (X := EncodedType.list X) (Y := EncodedType.list Y)
      (fun xs => xs.map f) :=
  StrictStreamMap.list_map_map hf

/--
Strict streaming certificate for bounded-block flatMap when the full composite
has an explicit project-local cost witness.
-/
def flatMapConstBound {X Y : EncodedType} {f : X.Carrier → List Y.Carrier}
    (hf : StrictStreamMap (X := X) (Y := EncodedType.list Y) f)
    (blockBound : Nat)
    (hcosted : CostedPolyTimeMap (X := EncodedType.list X) (Y := EncodedType.list Y)
      (fun xs => xs.flatMap f)) :
    StrictStreamMap (X := EncodedType.list X) (Y := EncodedType.list Y)
      (fun xs => xs.flatMap f) :=
  StrictStreamMap.list_flatMap_constBound hf blockBound hcosted

end StrictLists
end Templates
end ComplexityReduction
