/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Templates.Lists

namespace ComplexityReduction

namespace Templates

/-- A tiny generic formula format as a list of clauses. -/
abbrev Formula (Atom : Type) : Type :=
  List (List Atom)

/-- Append two formulas by concatenating their clause lists. -/
def formulaAppend {Atom : Type} (p : Formula Atom × Formula Atom) : Formula Atom :=
  p.1 ++ p.2

/-- Formula append is available from the generic list append template. -/
def costedFormulaAppend (Atom : EncodedType) :
    CostedPolyTimeMap
      (X := EncodedType.prod (EncodedType.list (EncodedType.list Atom))
        (EncodedType.list (EncodedType.list Atom)))
      (Y := EncodedType.list (EncodedType.list Atom))
      (fun p : Formula Atom.Carrier × Formula Atom.Carrier => formulaAppend p) :=
  costedListAppend (EncodedType.list Atom)

/-- Log-space formula append certificate from the generic list append template. -/
def logFormulaAppend (Atom : EncodedType) :
    LogSpaceMap
      (X := EncodedType.prod (EncodedType.list (EncodedType.list Atom))
        (EncodedType.list (EncodedType.list Atom)))
      (Y := EncodedType.list (EncodedType.list Atom))
      (fun p : Formula Atom.Carrier × Formula Atom.Carrier => formulaAppend p) :=
  logListAppend (EncodedType.list Atom)

end Templates

end ComplexityReduction
