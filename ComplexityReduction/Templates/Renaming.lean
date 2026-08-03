/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Templates.FormulaAppend

namespace ComplexityReduction

namespace Templates

/-- Rename atoms inside a generic formula. -/
def renameFormula {Atom Var : Type} (ρ : Atom → Var) : Formula Atom → Formula Var :=
  List.map (List.map ρ)

/-- Renaming a formula is obtained by two applications of the generic list-map template. -/
def costedRenameFormula {Atom Var : EncodedType} {ρ : Atom.Carrier → Var.Carrier}
    (hρ : CostedPolyTimeMap (X := Atom) (Y := Var) ρ) :
    CostedPolyTimeMap
      (X := EncodedType.list (EncodedType.list Atom))
      (Y := EncodedType.list (EncodedType.list Var))
      (renameFormula ρ) :=
  costedListMap (costedListMap hρ)

/-- Log-space formula renaming from the generic list-map template. -/
def logRenameFormula {Atom Var : EncodedType} {ρ : Atom.Carrier → Var.Carrier}
    (hρ : LogSpaceMap (X := Atom) (Y := Var) ρ) :
    LogSpaceMap
      (X := EncodedType.list (EncodedType.list Atom))
      (Y := EncodedType.list (EncodedType.list Var))
      (renameFormula ρ) :=
  logListMap (logListMap hρ)

end Templates

end ComplexityReduction
