/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.PPBounds
import ComplexityReduction.CSP.FiniteDomain.StandardGadgets

/-!
Worked examples for finite-domain derived relations.

The examples use the standard equality/pinning language as the base language.
They demonstrate the automatic expansion wrappers from `PPBounds` for one
derived binary relation and for a finite family of two derived relation symbols.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain
namespace PPDef
namespace Examples

open StandardGadgets

/-- Atomic pp block copying the base equality relation. -/
def equalityCopyBlock {D : Type} [Fintype D] (d : D) :
    RelationFormula (eqPinLanguage d) 2 :=
  atomicRelationFormula (eqPinLanguage d) EqPinSymbol.eq

/-- Atomic pp block copying the base pinning relation. -/
def pinCopyBlock {D : Type} [Fintype D] (d : D) :
    RelationFormula (eqPinLanguage d) 1 :=
  atomicRelationFormula (eqPinLanguage d) EqPinSymbol.pin

/-- One-symbol language adding a derived copy of equality. -/
def singleEqualityCopyLanguage {D : Type} [Fintype D] (d : D) : Language D :=
  singleDerivedLanguage (eqPinLanguage d) (equalityCopyBlock d)

/-- Automatic expansion of formulas over the one-symbol equality-copy extension. -/
noncomputable def expandSingleEqualityCopy {D : Type} [Fintype D] [Inhabited D]
    (d : D) :
    Formula (singleEqualityCopyLanguage d) → Formula (eqPinLanguage d) :=
  formulaViaSingleDerivedRepresentation (eqPinLanguage d) (equalityCopyBlock d)

theorem expandSingleEqualityCopy_satisfiable_iff {D : Type} [Fintype D] [Inhabited D]
    (d : D) (φ : Formula (singleEqualityCopyLanguage d)) :
    Formula.Satisfiable (expandSingleEqualityCopy d φ) ↔ Formula.Satisfiable φ :=
  formulaViaSingleDerivedRepresentation_satisfiable_iff
    (eqPinLanguage d) (equalityCopyBlock d) φ

/-- Two derived symbols: one equality copy and one pinning copy. -/
inductive EqPinCopySymbol where
  | eqCopy
  | pinCopy
  deriving DecidableEq, Fintype, Repr

/-- Arities of the two derived example symbols. -/
def eqPinCopyArity : EqPinCopySymbol → Nat
  | EqPinCopySymbol.eqCopy => 2
  | EqPinCopySymbol.pinCopy => 1

/-- Blocks interpreting the two derived example symbols in the base language. -/
def eqPinCopyBlock {D : Type} [Fintype D] (d : D) :
    ∀ s : EqPinCopySymbol, RelationFormula (eqPinLanguage d) (eqPinCopyArity s)
  | EqPinCopySymbol.eqCopy => equalityCopyBlock d
  | EqPinCopySymbol.pinCopy => pinCopyBlock d

/-- Finite-family extension adding equality and pinning copies together. -/
def eqPinCopyLanguage {D : Type} [Fintype D] (d : D) : Language D :=
  derivedFamilyLanguage (eqPinLanguage d) eqPinCopyArity (eqPinCopyBlock d)

/-- Automatic expansion of formulas over the two-symbol derived-family extension. -/
noncomputable def expandEqPinCopyFamily {D : Type} [Fintype D] [Inhabited D]
    (d : D) :
    Formula (eqPinCopyLanguage d) → Formula (eqPinLanguage d) :=
  formulaViaDerivedFamilyRepresentation (eqPinLanguage d) eqPinCopyArity (eqPinCopyBlock d)

theorem expandEqPinCopyFamily_satisfiable_iff {D : Type} [Fintype D] [Inhabited D]
    (d : D) (φ : Formula (eqPinCopyLanguage d)) :
    Formula.Satisfiable (expandEqPinCopyFamily d φ) ↔ Formula.Satisfiable φ :=
  formulaViaDerivedFamilyRepresentation_satisfiable_iff
    (eqPinLanguage d) eqPinCopyArity (eqPinCopyBlock d) φ

end Examples
end PPDef
end FiniteDomain
end CSP
end ComplexityReduction
