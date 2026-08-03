/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.HColoring.TemplateCatalog

/-!
Source-gated complexity metadata for fixed-template `H`-coloring.

The local Lean library proves graph-homomorphism-to-CSP equivalences, but it
does not contain a proof of the Hell-Nesetril complexity classification.  This
catalog records that boundary explicitly so generated reductions do not treat
the classification as a mounted theorem.
-/

namespace ComplexityReduction
namespace Targets

/-- Status of a graph-homomorphism complexity route. -/
inductive HColoringComplexityStatus where
  | theoremUsable
  | sourceGated
  | blocked
  deriving DecidableEq, Repr

namespace HColoringComplexityStatus

/-- Whether a route may be used as a theorem by generated artifacts. -/
def generatorMayUseAsTheorem : HColoringComplexityStatus → Bool
  | theoremUsable => true
  | sourceGated => false
  | blocked => false

@[simp]
theorem sourceGated_not_usable :
    HColoringComplexityStatus.sourceGated.generatorMayUseAsTheorem = false :=
  rfl

@[simp]
theorem blocked_not_usable :
    HColoringComplexityStatus.blocked.generatorMayUseAsTheorem = false :=
  rfl

end HColoringComplexityStatus

/-- Planner metadata for fixed-template `H`-coloring complexity claims. -/
structure HColoringComplexityRouteDescriptor where
  name : String
  source : String
  theoremSymbol : Option String := none
  status : HColoringComplexityStatus
  roles : List String
  notes : List String
  deriving Repr

namespace HColoringComplexityRouteDescriptor

/-- Whether this descriptor exposes a theorem usable by generated artifacts. -/
def generatorMayUseAsTheorem (route : HColoringComplexityRouteDescriptor) : Bool :=
  route.status.generatorMayUseAsTheorem

end HColoringComplexityRouteDescriptor

/-- Hell-Nesetril-style `H`-coloring classifications remain source-gated locally. -/
def hellNesetrilSourceGatedRoute : HColoringComplexityRouteDescriptor :=
  { name := "hell_nesetril_h_coloring_classification"
    source := "Hell-Nesetril 1990, On the Complexity of H-Coloring"
    theoremSymbol := none
    status := HColoringComplexityStatus.sourceGated
    roles := ["h_coloring", "graph_hom", "complexity_classification", "source_gated"]
    notes :=
      [ "The primary source is recorded as restricted/not locally formalized in this library."
      , "Do not assert non-bipartite-template NP-completeness or dichotomy from this descriptor." ] }

theorem hellNesetrilSourceGatedRoute_not_usable :
    hellNesetrilSourceGatedRoute.generatorMayUseAsTheorem = false :=
  rfl

/-- Public H-coloring complexity metadata catalog. -/
def hColoringComplexityRoutes : List HColoringComplexityRouteDescriptor :=
  [hellNesetrilSourceGatedRoute]

theorem hColoringComplexityRoutes_length :
    hColoringComplexityRoutes.length = 1 :=
  rfl

end Targets
end ComplexityReduction
