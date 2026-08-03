/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Templates.Structural

namespace ComplexityReduction

namespace Templates

/-- Map over encoded lists using a costed closure certificate for the element map. -/
def costedListMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (hf : CostedPolyTimeMap (X := X) (Y := Y) f) :
    CostedPolyTimeMap (X := EncodedType.list X) (Y := EncodedType.list Y)
      (fun xs => xs.map f) :=
  CostedPolyTimeMap.list_map_map hf

/-- Append encoded lists at the costed closure level. -/
def costedListAppend (X : EncodedType) :
    CostedPolyTimeMap
      (X := EncodedType.prod (EncodedType.list X) (EncodedType.list X))
      (Y := EncodedType.list X)
      (fun p : List X.Carrier × List X.Carrier => p.1 ++ p.2) :=
  CostedPolyTimeMap.list_append_map

/-- Map over encoded lists using a log-space closure certificate for the element map. -/
def logListMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (hf : LogSpaceMap (X := X) (Y := Y) f) :
    LogSpaceMap (X := EncodedType.list X) (Y := EncodedType.list Y) (fun xs => xs.map f) :=
  LogSpaceMap.list_map_map hf

/-- Append encoded lists at the log-space closure level. -/
def logListAppend (X : EncodedType) :
    LogSpaceMap
      (X := EncodedType.prod (EncodedType.list X) (EncodedType.list X))
      (Y := EncodedType.list X)
      (fun p : List X.Carrier × List X.Carrier => p.1 ++ p.2) :=
  LogSpaceMap.list_append_map

end Templates

end ComplexityReduction
