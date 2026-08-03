/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Templates.Lists

namespace ComplexityReduction

namespace Templates

/-- A block is a list of elements. -/
abbrev Block (α : Type) : Type :=
  List α

/-- Concatenate a list of blocks. -/
def concatBlocks {α : Type} : List (Block α) → Block α :=
  List.foldr (fun block acc => block ++ acc) []

/-- A block template packages a block-producing map with a costed closure certificate. -/
structure BlockTemplate (X Elem : EncodedType) where
  blockOf : X.Carrier → Block Elem.Carrier
  block_costed : CostedPolyTimeMap (X := X) (Y := EncodedType.list Elem) blockOf

namespace BlockTemplate

/-- Apply a block template to a list of inputs. -/
def mapBlocks {X Elem : EncodedType} (T : BlockTemplate X Elem) :
    List X.Carrier → List (Block Elem.Carrier) :=
  List.map T.blockOf

/-- Mapping a block template over lists is costed by the generic list-map template. -/
def mapBlocks_costed {X Elem : EncodedType} (T : BlockTemplate X Elem) :
    CostedPolyTimeMap
      (X := EncodedType.list X)
      (Y := EncodedType.list (EncodedType.list Elem))
      T.mapBlocks :=
  costedListMap T.block_costed

end BlockTemplate

end Templates

end ComplexityReduction
