/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.Polymorphisms.Preservation

/-!
Metadata catalog for finite-domain Boolean polymorphism operations.

This file intentionally records operation descriptors and theorem-name anchors
only.  It does not assert a finite-domain dichotomy, tractability theorem, or
hardness theorem.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace AlgebraicCatalog

/-- Planner-facing algebraic operation families. -/
inductive OperationKind where
  | custom
  | constant
  | complement
  | semilatticeLike
  | majority
  | minority
  | maltsev
  | nearUnanimity
  deriving DecidableEq, Repr

namespace OperationKind

/-- Stable string label for operation-kind metadata. -/
def label : OperationKind → String
  | custom => "custom"
  | constant => "constant"
  | complement => "complement"
  | semilatticeLike => "semilattice_like"
  | majority => "majority"
  | minority => "minority"
  | maltsev => "maltsev"
  | nearUnanimity => "near_unanimity"

end OperationKind

/-- Planner metadata for a named finite-domain operation and its Boolean transport theorem. -/
structure OperationDescriptor where
  name : String
  arity : Nat
  kind : OperationKind := OperationKind.custom
  operationSymbol : String
  schaeferProperty : String
  relationTheorem : String
  languageTheorem : String
  predicateTheorems : List String := []
  roles : List String
  notes : List String
  deriving Repr

/-- Boolean conjunction / Horn-preservation descriptor. -/
def boolAnd : OperationDescriptor :=
  { name := "bool_and"
    arity := 2
    kind := OperationKind.semilatticeLike
    operationSymbol := "ComplexityReduction.CSP.FiniteDomain.Operation.boolAnd"
    schaeferProperty := "horn"
    relationTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesRel_boolAnd_iff_isHorn"
    languageTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolAnd_iff_allRelationsHorn"
    predicateTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Operation.boolAnd_isIdempotent"
      , "ComplexityReduction.CSP.FiniteDomain.Operation.boolAnd_isSemilatticeLike" ]
    roles := ["finite_domain_csp", "polymorphism", "horn"]
    notes := ["Binary meet operation used for Horn-style algebraic side conditions."] }

/-- Boolean disjunction / dual-Horn-preservation descriptor. -/
def boolOr : OperationDescriptor :=
  { name := "bool_or"
    arity := 2
    kind := OperationKind.semilatticeLike
    operationSymbol := "ComplexityReduction.CSP.FiniteDomain.Operation.boolOr"
    schaeferProperty := "dual_horn"
    relationTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesRel_boolOr_iff_isDualHorn"
    languageTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolOr_iff_allRelationsDualHorn"
    predicateTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Operation.boolOr_isIdempotent"
      , "ComplexityReduction.CSP.FiniteDomain.Operation.boolOr_isSemilatticeLike" ]
    roles := ["finite_domain_csp", "polymorphism", "dual_horn"]
    notes := ["Binary join operation used for dual-Horn-style algebraic side conditions."] }

/-- Boolean ternary xor / affine-preservation descriptor. -/
def boolTernaryXor : OperationDescriptor :=
  { name := "bool_ternary_xor"
    arity := 3
    kind := OperationKind.minority
    operationSymbol := "ComplexityReduction.CSP.FiniteDomain.Operation.boolTernaryXor"
    schaeferProperty := "affine"
    relationTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesRel_boolTernaryXor_iff_isAffine"
    languageTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolTernaryXor_iff_allRelationsAffine"
    predicateTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Operation.boolTernaryXor_isMinority"
      , "ComplexityReduction.CSP.FiniteDomain.Operation.boolTernaryXor_isMaltsev" ]
    roles := ["finite_domain_csp", "polymorphism", "affine"]
    notes := ["Ternary xor operation used for affine algebraic side conditions."] }

/-- Boolean majority / bijunctive-preservation descriptor. -/
def boolMajority : OperationDescriptor :=
  { name := "bool_majority"
    arity := 3
    kind := OperationKind.majority
    operationSymbol := "ComplexityReduction.CSP.FiniteDomain.Operation.boolMajority"
    schaeferProperty := "bijunctive"
    relationTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesRel_boolMajority_iff_isBijunctive"
    languageTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolMajority_iff_allRelationsBijunctive"
    predicateTheorems :=
      [ "ComplexityReduction.CSP.FiniteDomain.Operation.boolMajority_isMajority"
      , "ComplexityReduction.CSP.FiniteDomain.Operation.boolMajority_isNearUnanimity" ]
    roles := ["finite_domain_csp", "polymorphism", "bijunctive"]
    notes := ["Majority operation used for bijunctive algebraic side conditions."] }

/-- Boolean complement / complementive-preservation descriptor. -/
def boolComplement : OperationDescriptor :=
  { name := "bool_complement"
    arity := 1
    kind := OperationKind.complement
    operationSymbol := "ComplexityReduction.CSP.FiniteDomain.Operation.boolComplement"
    schaeferProperty := "complementive"
    relationTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesRel_boolComplement_iff_isComplementive"
    languageTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolComplement_iff_allRelationsComplementive"
    roles := ["finite_domain_csp", "polymorphism", "complementive"]
    notes := ["Unary complement operation used for complementive side conditions."] }

/-- Nullary false / zero-valid descriptor. -/
def boolFalse : OperationDescriptor :=
  { name := "bool_false"
    arity := 0
    kind := OperationKind.constant
    operationSymbol := "ComplexityReduction.CSP.FiniteDomain.Operation.boolFalse"
    schaeferProperty := "zero_valid"
    relationTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesRel_boolFalse_iff_isZeroValid"
    languageTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolFalse_iff_allRelationsZeroValid"
    roles := ["finite_domain_csp", "polymorphism", "zero_valid"]
    notes := ["Nullary false operation used for zero-valid side conditions."] }

/-- Nullary true / one-valid descriptor. -/
def boolTrue : OperationDescriptor :=
  { name := "bool_true"
    arity := 0
    kind := OperationKind.constant
    operationSymbol := "ComplexityReduction.CSP.FiniteDomain.Operation.boolTrue"
    schaeferProperty := "one_valid"
    relationTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesRel_boolTrue_iff_isOneValid"
    languageTheorem :=
      "ComplexityReduction.CSP.FiniteDomain.BoolTransport.preservesLanguage_boolTrue_iff_allRelationsOneValid"
    roles := ["finite_domain_csp", "polymorphism", "one_valid"]
    notes := ["Nullary true operation used for one-valid side conditions."] }

/-- Boolean algebraic operation descriptors exposed to the planner. -/
def booleanOperationDescriptors : List OperationDescriptor :=
  [ boolAnd
  , boolOr
  , boolTernaryXor
  , boolMajority
  , boolComplement
  , boolFalse
  , boolTrue
  ]

theorem booleanOperationDescriptors_length :
    booleanOperationDescriptors.length = 7 :=
  rfl

/-- Operation-kind vocabulary exposed to route planners. -/
def operationKinds : List OperationKind :=
  [ OperationKind.custom
  , OperationKind.constant
  , OperationKind.complement
  , OperationKind.semilatticeLike
  , OperationKind.majority
  , OperationKind.minority
  , OperationKind.maltsev
  , OperationKind.nearUnanimity
  ]

theorem operationKinds_length :
    operationKinds.length = 8 :=
  rfl

@[simp]
theorem boolAnd_kind :
    boolAnd.kind = OperationKind.semilatticeLike :=
  rfl

@[simp]
theorem boolOr_kind :
    boolOr.kind = OperationKind.semilatticeLike :=
  rfl

@[simp]
theorem boolTernaryXor_kind :
    boolTernaryXor.kind = OperationKind.minority :=
  rfl

@[simp]
theorem boolMajority_kind :
    boolMajority.kind = OperationKind.majority :=
  rfl

#check Operation.boolAnd
#check Operation.boolOr
#check Operation.boolTernaryXor
#check Operation.boolMajority
#check Operation.boolComplement
#check Operation.boolFalse
#check Operation.boolTrue
#check Operation.IsIdempotent
#check Operation.IsNearUnanimity
#check Operation.IsMajority
#check Operation.IsMinority
#check Operation.IsMaltsev
#check Operation.IsSemilatticeLike
#check Operation.boolAnd_isIdempotent
#check Operation.boolOr_isIdempotent
#check Operation.boolAnd_isSemilatticeLike
#check Operation.boolOr_isSemilatticeLike
#check Operation.boolMajority_isMajority
#check Operation.boolMajority_isNearUnanimity
#check Operation.boolTernaryXor_isMinority
#check Operation.boolTernaryXor_isMaltsev
#check BoolTransport.preservesLanguage_boolAnd_iff_allRelationsHorn
#check BoolTransport.preservesLanguage_boolOr_iff_allRelationsDualHorn
#check BoolTransport.preservesLanguage_boolTernaryXor_iff_allRelationsAffine
#check BoolTransport.preservesLanguage_boolMajority_iff_allRelationsBijunctive
#check BoolTransport.preservesLanguage_boolComplement_iff_allRelationsComplementive
#check BoolTransport.preservesLanguage_boolFalse_iff_allRelationsZeroValid
#check BoolTransport.preservesLanguage_boolTrue_iff_allRelationsOneValid

end AlgebraicCatalog
end FiniteDomain
end CSP
end ComplexityReduction
