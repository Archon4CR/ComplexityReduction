/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Templates.Renaming

namespace ComplexityReduction

namespace Templates

/-- Substitute each atom by a block of atoms, preserving clause structure. -/
def substituteAtoms {Atom Var : Type} (σ : Atom → List Var) : Formula Atom → Formula Var :=
  List.map (fun clause => clause.flatMap σ)

/-- A lightweight certificate that an atom substitution is admitted by the template. -/
structure SubstitutionTemplate (Atom Var : EncodedType) where
  subst : Atom.Carrier → List Var.Carrier
  subst_costed :
    CostedPolyTimeMap (X := Atom) (Y := EncodedType.list Var) subst

namespace SubstitutionTemplate

/-- The induced formula substitution as a semantic map. -/
def map {Atom Var : EncodedType} (T : SubstitutionTemplate Atom Var) :
    Formula Atom.Carrier → Formula Var.Carrier :=
  substituteAtoms T.subst

end SubstitutionTemplate

end Templates

end ComplexityReduction
