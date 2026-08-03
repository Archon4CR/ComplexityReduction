/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.AlgebraicCatalog
import ComplexityReduction.Schaefer.Relations

/-!
Planner-facing Boolean clone and co-clone metadata.

This file records stable names for the Boolean algebraic classes used by the
finite-domain CSP bridge.  It deliberately stores descriptors and theorem-name
anchors only; it does not assert a complete Post lattice, co-clone lattice, or
Schaefer complexity classification.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace BooleanCloneCatalog

/-- Coarse Boolean clone families used by route planners. -/
inductive BooleanCloneKind where
  | custom
  | constantFalse
  | constantTrue
  | semilatticeMeet
  | semilatticeJoin
  | majority
  | affineParity
  | complement
  deriving DecidableEq, Repr

namespace BooleanCloneKind

/-- Stable string label for Boolean clone metadata. -/
def label : BooleanCloneKind -> String
  | custom => "custom"
  | constantFalse => "constant_false"
  | constantTrue => "constant_true"
  | semilatticeMeet => "semilattice_meet"
  | semilatticeJoin => "semilattice_join"
  | majority => "majority"
  | affineParity => "affine_parity"
  | complement => "complement"

end BooleanCloneKind

/-- Coarse Boolean co-clone families used by route planners. -/
inductive BooleanCoCloneKind where
  | custom
  | zeroValid
  | oneValid
  | horn
  | dualHorn
  | bijunctive
  | affine
  | complementive
  | definiteHorn
  | definiteDualHorn
  | widthTwoAffine
  deriving DecidableEq, Repr

namespace BooleanCoCloneKind

/-- Stable string label for Boolean co-clone metadata. -/
def label : BooleanCoCloneKind -> String
  | custom => "custom"
  | zeroValid => "zero_valid"
  | oneValid => "one_valid"
  | horn => "horn"
  | dualHorn => "dual_horn"
  | bijunctive => "bijunctive"
  | affine => "affine"
  | complementive => "complementive"
  | definiteHorn => "definite_horn"
  | definiteDualHorn => "definite_dual_horn"
  | widthTwoAffine => "width_two_affine"

end BooleanCoCloneKind

/-- Boolean Schaefer-style classes exposed to the planner. -/
inductive BooleanSchaeferClass where
  | zeroValid
  | oneValid
  | horn
  | dualHorn
  | bijunctive
  | affine
  | complementive
  | definiteHorn
  | definiteDualHorn
  | widthTwoAffine
  deriving DecidableEq, Repr

namespace BooleanSchaeferClass

/-- Stable string label for Boolean Schaefer-class metadata. -/
def label : BooleanSchaeferClass -> String
  | zeroValid => "zero_valid"
  | oneValid => "one_valid"
  | horn => "horn"
  | dualHorn => "dual_horn"
  | bijunctive => "bijunctive"
  | affine => "affine"
  | complementive => "complementive"
  | definiteHorn => "definite_horn"
  | definiteDualHorn => "definite_dual_horn"
  | widthTwoAffine => "width_two_affine"

end BooleanSchaeferClass

/-- Planner metadata for a Boolean clone/co-clone class and its local theorem anchors. -/
structure BooleanCloneDescriptor where
  name : String
  schaeferClass : BooleanSchaeferClass
  cloneKind : BooleanCloneKind
  coCloneKind : BooleanCoCloneKind
  operationKind : AlgebraicCatalog.OperationKind
  relationPredicateSymbol : String
  languagePredicateSymbol : String
  operationDescriptor : Option String := none
  relationTransportTheorem : Option String := none
  languageTransportTheorem : Option String := none
  supportTheorems : List String := []
  generatorMayUseAsTheorem : Bool := true
  roles : List String := []
  notes : List String := []
  deriving Repr

namespace BooleanCloneDescriptor

private def optionalSymbolList : Option String -> List String
  | some s => [s]
  | none => []

/-- Declaration names referenced by a Boolean clone descriptor. -/
def theoremSymbols (desc : BooleanCloneDescriptor) : List String :=
  optionalSymbolList desc.relationTransportTheorem ++
    optionalSymbolList desc.languageTransportTheorem ++ desc.supportTheorems

end BooleanCloneDescriptor

/-- Horn / weakly-positive class backed by Boolean conjunction. -/
def horn : BooleanCloneDescriptor :=
  { name := "horn"
    schaeferClass := BooleanSchaeferClass.horn
    cloneKind := BooleanCloneKind.semilatticeMeet
    coCloneKind := BooleanCoCloneKind.horn
    operationKind := AlgebraicCatalog.OperationKind.semilatticeLike
    relationPredicateSymbol := "ComplexityReduction.CSP.IsHorn"
    languagePredicateSymbol := "ComplexityReduction.Schaefer.IsHornLanguage"
    operationDescriptor :=
      some "ComplexityReduction.CSP.FiniteDomain.AlgebraicCatalog.boolAnd"
    relationTransportTheorem :=
      some "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesRel_boolAnd_iff_isHorn"
    languageTransportTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolAnd_iff_allRelationsHorn"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Operation.boolAnd_isSemilatticeLike" ]
    roles := ["boolean_clone", "co_clone", "horn", "finite_domain_polymorphism"]
    notes := ["Closure under Boolean conjunction is the local theorem-usable Horn anchor."] }

/-- Dual-Horn / weakly-negative class backed by Boolean disjunction. -/
def dualHorn : BooleanCloneDescriptor :=
  { name := "dual_horn"
    schaeferClass := BooleanSchaeferClass.dualHorn
    cloneKind := BooleanCloneKind.semilatticeJoin
    coCloneKind := BooleanCoCloneKind.dualHorn
    operationKind := AlgebraicCatalog.OperationKind.semilatticeLike
    relationPredicateSymbol := "ComplexityReduction.CSP.IsDualHorn"
    languagePredicateSymbol := "ComplexityReduction.Schaefer.IsDualHornLanguage"
    operationDescriptor :=
      some "ComplexityReduction.CSP.FiniteDomain.AlgebraicCatalog.boolOr"
    relationTransportTheorem :=
      some "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesRel_boolOr_iff_isDualHorn"
    languageTransportTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolOr_iff_allRelationsDualHorn"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Operation.boolOr_isSemilatticeLike" ]
    roles := ["boolean_clone", "co_clone", "dual_horn", "finite_domain_polymorphism"]
    notes := ["Closure under Boolean disjunction is the local theorem-usable dual-Horn anchor."] }

/-- Bijunctive class backed by Boolean majority. -/
def bijunctive : BooleanCloneDescriptor :=
  { name := "bijunctive"
    schaeferClass := BooleanSchaeferClass.bijunctive
    cloneKind := BooleanCloneKind.majority
    coCloneKind := BooleanCoCloneKind.bijunctive
    operationKind := AlgebraicCatalog.OperationKind.majority
    relationPredicateSymbol := "ComplexityReduction.CSP.IsBijunctive"
    languagePredicateSymbol := "ComplexityReduction.Schaefer.IsBijunctiveLanguage"
    operationDescriptor :=
      some "ComplexityReduction.CSP.FiniteDomain.AlgebraicCatalog.boolMajority"
    relationTransportTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesRel_boolMajority_iff_isBijunctive"
    languageTransportTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolMajority_iff_allRelationsBijunctive"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Operation.boolMajority_isMajority"
      , "ComplexityReduction.CSP.FiniteDomain.Operation.boolMajority_isNearUnanimity" ]
    roles := ["boolean_clone", "co_clone", "bijunctive", "finite_domain_polymorphism"]
    notes := ["Majority preservation is the local theorem-usable bijunctive anchor."] }

/-- Affine class backed by Boolean ternary xor. -/
def affine : BooleanCloneDescriptor :=
  { name := "affine"
    schaeferClass := BooleanSchaeferClass.affine
    cloneKind := BooleanCloneKind.affineParity
    coCloneKind := BooleanCoCloneKind.affine
    operationKind := AlgebraicCatalog.OperationKind.minority
    relationPredicateSymbol := "ComplexityReduction.CSP.IsAffine"
    languagePredicateSymbol := "ComplexityReduction.Schaefer.IsAffineLanguage"
    operationDescriptor :=
      some "ComplexityReduction.CSP.FiniteDomain.AlgebraicCatalog.boolTernaryXor"
    relationTransportTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesRel_boolTernaryXor_iff_isAffine"
    languageTransportTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolTernaryXor_iff_allRelationsAffine"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Operation.boolTernaryXor_isMinority"
      , "ComplexityReduction.CSP.FiniteDomain.Operation.boolTernaryXor_isMaltsev" ]
    roles := ["boolean_clone", "co_clone", "affine", "finite_domain_polymorphism"]
    notes := ["Ternary-xor preservation is the local theorem-usable affine anchor."] }

/-- Zero-valid class backed by the nullary false operation. -/
def zeroValid : BooleanCloneDescriptor :=
  { name := "zero_valid"
    schaeferClass := BooleanSchaeferClass.zeroValid
    cloneKind := BooleanCloneKind.constantFalse
    coCloneKind := BooleanCoCloneKind.zeroValid
    operationKind := AlgebraicCatalog.OperationKind.constant
    relationPredicateSymbol := "ComplexityReduction.CSP.IsZeroValid"
    languagePredicateSymbol := "ComplexityReduction.Schaefer.IsZeroValidLanguage"
    operationDescriptor :=
      some "ComplexityReduction.CSP.FiniteDomain.AlgebraicCatalog.boolFalse"
    relationTransportTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesRel_boolFalse_iff_isZeroValid"
    languageTransportTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolFalse_iff_allRelationsZeroValid"
    roles := ["boolean_clone", "co_clone", "zero_valid", "finite_domain_polymorphism"]
    notes := ["The nullary false operation is the local zero-valid anchor."] }

/-- One-valid class backed by the nullary true operation. -/
def oneValid : BooleanCloneDescriptor :=
  { name := "one_valid"
    schaeferClass := BooleanSchaeferClass.oneValid
    cloneKind := BooleanCloneKind.constantTrue
    coCloneKind := BooleanCoCloneKind.oneValid
    operationKind := AlgebraicCatalog.OperationKind.constant
    relationPredicateSymbol := "ComplexityReduction.CSP.IsOneValid"
    languagePredicateSymbol := "ComplexityReduction.Schaefer.IsOneValidLanguage"
    operationDescriptor :=
      some "ComplexityReduction.CSP.FiniteDomain.AlgebraicCatalog.boolTrue"
    relationTransportTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesRel_boolTrue_iff_isOneValid"
    languageTransportTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolTrue_iff_allRelationsOneValid"
    roles := ["boolean_clone", "co_clone", "one_valid", "finite_domain_polymorphism"]
    notes := ["The nullary true operation is the local one-valid anchor."] }

/-- Complementive class backed by unary Boolean complement. -/
def complementive : BooleanCloneDescriptor :=
  { name := "complementive"
    schaeferClass := BooleanSchaeferClass.complementive
    cloneKind := BooleanCloneKind.complement
    coCloneKind := BooleanCoCloneKind.complementive
    operationKind := AlgebraicCatalog.OperationKind.complement
    relationPredicateSymbol := "ComplexityReduction.CSP.IsComplementive"
    languagePredicateSymbol := "ComplexityReduction.CSP.AllRelationsSatisfy _ ComplexityReduction.CSP.IsComplementive"
    operationDescriptor :=
      some "ComplexityReduction.CSP.FiniteDomain.AlgebraicCatalog.boolComplement"
    relationTransportTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesRel_boolComplement_iff_isComplementive"
    languageTransportTheorem :=
      some
        "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolComplement_iff_allRelationsComplementive"
    roles := ["boolean_clone", "co_clone", "complementive", "finite_domain_polymorphism"]
    notes := ["Complement preservation is local metadata; it is not one of the six Schaefer tractable branches by itself."] }

/-- Definite-Horn refinement metadata. -/
def definiteHorn : BooleanCloneDescriptor :=
  { name := "definite_horn"
    schaeferClass := BooleanSchaeferClass.definiteHorn
    cloneKind := BooleanCloneKind.semilatticeMeet
    coCloneKind := BooleanCoCloneKind.definiteHorn
    operationKind := AlgebraicCatalog.OperationKind.semilatticeLike
    relationPredicateSymbol := "metadata:definite_horn_relation"
    languagePredicateSymbol := "metadata:definite_horn_language"
    operationDescriptor :=
      some "ComplexityReduction.CSP.FiniteDomain.AlgebraicCatalog.boolAnd"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolAnd_iff_allRelationsHorn" ]
    generatorMayUseAsTheorem := false
    roles := ["boolean_clone", "co_clone", "definite_horn", "metadata_only"]
    notes := ["Refinement metadata only; generated proofs must cite the broader Horn theorem unless a local definite-Horn theorem is added."] }

/-- Definite-dual-Horn refinement metadata. -/
def definiteDualHorn : BooleanCloneDescriptor :=
  { name := "definite_dual_horn"
    schaeferClass := BooleanSchaeferClass.definiteDualHorn
    cloneKind := BooleanCloneKind.semilatticeJoin
    coCloneKind := BooleanCoCloneKind.definiteDualHorn
    operationKind := AlgebraicCatalog.OperationKind.semilatticeLike
    relationPredicateSymbol := "metadata:definite_dual_horn_relation"
    languagePredicateSymbol := "metadata:definite_dual_horn_language"
    operationDescriptor :=
      some "ComplexityReduction.CSP.FiniteDomain.AlgebraicCatalog.boolOr"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolOr_iff_allRelationsDualHorn" ]
    generatorMayUseAsTheorem := false
    roles := ["boolean_clone", "co_clone", "definite_dual_horn", "metadata_only"]
    notes := ["Refinement metadata only; generated proofs must cite the broader dual-Horn theorem unless a local definite-dual-Horn theorem is added."] }

/-- Width-2 affine refinement metadata. -/
def widthTwoAffine : BooleanCloneDescriptor :=
  { name := "width_two_affine"
    schaeferClass := BooleanSchaeferClass.widthTwoAffine
    cloneKind := BooleanCloneKind.affineParity
    coCloneKind := BooleanCoCloneKind.widthTwoAffine
    operationKind := AlgebraicCatalog.OperationKind.minority
    relationPredicateSymbol := "metadata:width_two_affine_relation"
    languagePredicateSymbol := "metadata:width_two_affine_language"
    operationDescriptor :=
      some "ComplexityReduction.CSP.FiniteDomain.AlgebraicCatalog.boolTernaryXor"
    supportTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolTernaryXor_iff_allRelationsAffine" ]
    generatorMayUseAsTheorem := false
    roles := ["boolean_clone", "co_clone", "width_two_affine", "metadata_only"]
    notes := ["Refined affine metadata only; generated proofs must cite the broader affine theorem unless a local width-2 theorem is added."] }

/-- Boolean clone/co-clone descriptors exposed to the planner. -/
def booleanCloneDescriptors : List BooleanCloneDescriptor :=
  [ horn
  , dualHorn
  , bijunctive
  , affine
  , zeroValid
  , oneValid
  , complementive
  , definiteHorn
  , definiteDualHorn
  , widthTwoAffine
  ]

/-- The descriptors that directly point to local theorem-usable transport anchors. -/
def theoremUsableDescriptors : List BooleanCloneDescriptor :=
  booleanCloneDescriptors.filter (fun desc => desc.generatorMayUseAsTheorem)

theorem booleanCloneDescriptors_length :
    booleanCloneDescriptors.length = 10 :=
  rfl

theorem theoremUsableDescriptors_length :
    theoremUsableDescriptors.length = 7 :=
  rfl

@[simp]
theorem horn_class :
    horn.schaeferClass = BooleanSchaeferClass.horn :=
  rfl

@[simp]
theorem dualHorn_class :
    dualHorn.schaeferClass = BooleanSchaeferClass.dualHorn :=
  rfl

@[simp]
theorem bijunctive_class :
    bijunctive.schaeferClass = BooleanSchaeferClass.bijunctive :=
  rfl

@[simp]
theorem affine_class :
    affine.schaeferClass = BooleanSchaeferClass.affine :=
  rfl

@[simp]
theorem zeroValid_class :
    zeroValid.schaeferClass = BooleanSchaeferClass.zeroValid :=
  rfl

@[simp]
theorem oneValid_class :
    oneValid.schaeferClass = BooleanSchaeferClass.oneValid :=
  rfl

@[simp]
theorem complementive_class :
    complementive.schaeferClass = BooleanSchaeferClass.complementive :=
  rfl

theorem definiteHorn_metadataOnly :
    definiteHorn.generatorMayUseAsTheorem = false :=
  rfl

theorem definiteDualHorn_metadataOnly :
    definiteDualHorn.generatorMayUseAsTheorem = false :=
  rfl

theorem widthTwoAffine_metadataOnly :
    widthTwoAffine.generatorMayUseAsTheorem = false :=
  rfl

#check BooleanCloneKind
#check BooleanCloneKind.label
#check BooleanCoCloneKind
#check BooleanCoCloneKind.label
#check BooleanSchaeferClass
#check BooleanSchaeferClass.label
#check BooleanCloneDescriptor
#check BooleanCloneDescriptor.theoremSymbols
#check booleanCloneDescriptors
#check booleanCloneDescriptors_length
#check theoremUsableDescriptors
#check theoremUsableDescriptors_length
#check horn_class
#check dualHorn_class
#check bijunctive_class
#check affine_class
#check zeroValid_class
#check oneValid_class
#check complementive_class
#check definiteHorn_metadataOnly
#check definiteDualHorn_metadataOnly
#check widthTwoAffine_metadataOnly
#check BoolTransport.preservesLanguage_boolAnd_iff_allRelationsHorn
#check BoolTransport.preservesLanguage_boolOr_iff_allRelationsDualHorn
#check BoolTransport.preservesLanguage_boolMajority_iff_allRelationsBijunctive
#check BoolTransport.preservesLanguage_boolTernaryXor_iff_allRelationsAffine
#check BoolTransport.preservesLanguage_boolFalse_iff_allRelationsZeroValid
#check BoolTransport.preservesLanguage_boolTrue_iff_allRelationsOneValid
#check BoolTransport.preservesLanguage_boolComplement_iff_allRelationsComplementive
#check Schaefer.IsHornLanguage
#check Schaefer.IsDualHornLanguage
#check Schaefer.IsBijunctiveLanguage
#check Schaefer.IsAffineLanguage
#check Schaefer.IsZeroValidLanguage
#check Schaefer.IsOneValidLanguage

end BooleanCloneCatalog
end FiniteDomain
end CSP
end ComplexityReduction
