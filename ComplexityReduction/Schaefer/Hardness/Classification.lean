/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Schaefer.Hardness.Representation
import ComplexityReduction.Schaefer.Hardness.LocalRep.Classification.RepExactlyOne

/-!
Typed hard-classification bridge for the local Schaefer route.

The semantic and costed representation machinery lives in
`Hardness.Representation`.  This module adds the next layer: Section 3/4 style
witness shapes, together with the mechanical conversion from such witnesses to
`HardClassificationRoute`.

The nonempty-language witness theorem itself lives in
`Hardness.Constants`, where the constants/no-constants split and empty-relation
precondition are available.
-/

namespace ComplexityReduction
namespace Schaefer
namespace Hardness

namespace HardCaseAssumptions

/-- Failure of zero-validity yields a concrete relation rejecting the all-false tuple. -/
theorem exists_not_zero_valid {Γ : CSP.BoolLanguage} (h : HardCaseAssumptions Γ) :
    ∃ s : Γ.Symbol, ¬ IsZeroValid (Γ.relationOf s) := by
  classical
  by_contra hNo
  exact h.notZeroValid (by
    intro s
    by_contra hs
    exact hNo ⟨s, hs⟩)

/-- Failure of one-validity yields a concrete relation rejecting the all-true tuple. -/
theorem exists_not_one_valid {Γ : CSP.BoolLanguage} (h : HardCaseAssumptions Γ) :
    ∃ s : Γ.Symbol, ¬ IsOneValid (Γ.relationOf s) := by
  classical
  by_contra hNo
  exact h.notOneValid (by
    intro s
    by_contra hs
    exact hNo ⟨s, hs⟩)

/-- Failure of Horn closure yields a concrete binary AND-closure counterexample. -/
theorem exists_horn_failure {Γ : CSP.BoolLanguage} (h : HardCaseAssumptions Γ) :
    ∃ s : Γ.Symbol,
      ∃ a b : CSP.BoolTuple (Γ.relationOf s).arity,
        (Γ.relationOf s).Holds a ∧
          (Γ.relationOf s).Holds b ∧
            ¬ (Γ.relationOf s).Holds (BoolTuple.pointwiseAnd a b) := by
  classical
  by_contra hNo
  exact h.notHorn (by
    intro s a b ha hb
    by_contra hFail
    exact hNo ⟨s, a, b, ha, hb, hFail⟩)

/-- Failure of dual-Horn closure yields a concrete binary OR-closure counterexample. -/
theorem exists_dual_horn_failure {Γ : CSP.BoolLanguage} (h : HardCaseAssumptions Γ) :
    ∃ s : Γ.Symbol,
      ∃ a b : CSP.BoolTuple (Γ.relationOf s).arity,
        (Γ.relationOf s).Holds a ∧
          (Γ.relationOf s).Holds b ∧
            ¬ (Γ.relationOf s).Holds (BoolTuple.pointwiseOr a b) := by
  classical
  by_contra hNo
  exact h.notDualHorn (by
    intro s a b ha hb
    by_contra hFail
    exact hNo ⟨s, a, b, ha, hb, hFail⟩)

/-- Failure of affine closure yields a concrete ternary-xor closure counterexample. -/
theorem exists_affine_failure {Γ : CSP.BoolLanguage} (h : HardCaseAssumptions Γ) :
    ∃ s : Γ.Symbol,
      ∃ a b c : CSP.BoolTuple (Γ.relationOf s).arity,
        (Γ.relationOf s).Holds a ∧
          (Γ.relationOf s).Holds b ∧
            (Γ.relationOf s).Holds c ∧
              ¬ (Γ.relationOf s).Holds (BoolTuple.pointwiseTernaryXor a b c) := by
  classical
  by_contra hNo
  exact h.notAffine (by
    intro s a b c ha hb hc
    by_contra hFail
    exact hNo ⟨s, a, b, c, ha, hb, hc, hFail⟩)

/-- Failure of bijunctive closure yields a concrete majority-closure counterexample. -/
theorem exists_bijunctive_failure {Γ : CSP.BoolLanguage} (h : HardCaseAssumptions Γ) :
    ∃ s : Γ.Symbol,
      ∃ a b c : CSP.BoolTuple (Γ.relationOf s).arity,
        (Γ.relationOf s).Holds a ∧
          (Γ.relationOf s).Holds b ∧
            (Γ.relationOf s).Holds c ∧
              ¬ (Γ.relationOf s).Holds (BoolTuple.pointwiseMajority a b c) := by
  classical
  by_contra hNo
  exact h.notBijunctive (by
    intro s a b c ha hb hc
    by_contra hFail
    exact hNo ⟨s, a, b, c, ha, hb, hc, hFail⟩)

end HardCaseAssumptions

namespace LocalRepBridge

/-- The LocalRep bundled relation corresponding to one current CSP relation symbol. -/
noncomputable def bundledRelOf (Γ : CSP.BoolLanguage) (s : Γ.Symbol) :
    LocalRep.BundledLogRel where
  arity := (Γ.relationOf s).arity
  rel := (Γ.relationOf s).accepts

/-- The finite LocalRep relation family underlying a current CSP language. -/
noncomputable def languageRelFinset (Γ : CSP.BoolLanguage) :
    Finset LocalRep.BundledLogRel :=
  (Finset.univ : Finset Γ.Symbol).image (bundledRelOf Γ)

theorem bundledRelOf_mem_languageRelFinset (Γ : CSP.BoolLanguage) (s : Γ.Symbol) :
    bundledRelOf Γ s ∈ languageRelFinset Γ := by
  classical
  exact Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩

theorem pointwiseTernaryXor_eq {k : Nat}
    (a b c : CSP.BoolTuple k) :
    LocalRep.LogRel.pointwiseTernaryXor a b c =
      BoolTuple.pointwiseTernaryXor a b c := by
  funext i
  by_cases ha : a i <;> by_cases hb : b i <;> by_cases hc : c i <;>
    simp [LocalRep.LogRel.pointwiseTernaryXor, BoolTuple.pointwiseTernaryXor, ha, hb, hc]

theorem pointwiseMajority_eq {k : Nat}
    (a b c : CSP.BoolTuple k) :
    LocalRep.LogRel.pointwiseMaj a b c =
      BoolTuple.pointwiseMajority a b c := by
  funext i
  by_cases ha : a i <;> by_cases hb : b i <;> by_cases hc : c i <;>
    simp [LocalRep.LogRel.pointwiseMaj, BoolTuple.pointwiseMajority, ha, hb, hc]

theorem not_localRep_weaklyPositive_of_not_horn {R : CSP.BoolRel}
    (h : ¬ IsHorn R) :
    ¬ LocalRep.LogRel.IsWeaklyPositive R.accepts := by
  intro hWP
  apply h
  intro a b ha hb
  have hLocal : LocalRep.LogRel.pointwiseAnd a b ∈ R.accepts := hWP ha hb
  simpa [CSP.BoolRel.Holds, BoolTuple.pointwiseAnd, LocalRep.LogRel.pointwiseAnd]
    using hLocal

theorem not_localRep_weaklyNegative_of_not_dualHorn {R : CSP.BoolRel}
    (h : ¬ IsDualHorn R) :
    ¬ LocalRep.LogRel.IsWeaklyNegative R.accepts := by
  intro hWN
  apply h
  intro a b ha hb
  have hLocal : LocalRep.LogRel.pointwiseOr a b ∈ R.accepts := hWN ha hb
  simpa [CSP.BoolRel.Holds, BoolTuple.pointwiseOr, LocalRep.LogRel.pointwiseOr]
    using hLocal

theorem not_localRep_affine_of_not_affine {R : CSP.BoolRel}
    (h : ¬ IsAffine R) :
    ¬ LocalRep.LogRel.IsAffine R.accepts := by
  intro hAff
  apply h
  intro a b c ha hb hc
  have hLocal : LocalRep.LogRel.pointwiseTernaryXor a b c ∈ R.accepts :=
    hAff ha hb hc
  simpa [CSP.BoolRel.Holds, pointwiseTernaryXor_eq a b c] using hLocal

theorem not_localRep_bijunctive_of_not_bijunctive {R : CSP.BoolRel}
    (h : ¬ IsBijunctive R) :
    ¬ LocalRep.LogRel.IsBijunctive R.accepts := by
  intro hBij
  apply h
  intro a b c ha hb hc
  have hLocal : LocalRep.LogRel.pointwiseMaj a b c ∈ R.accepts :=
    hBij ha hb hc
  simpa [CSP.BoolRel.Holds, pointwiseMajority_eq a b c] using hLocal

/--
Section 3, through the copied local PP-closure formalization: the four hard
counterexamples produce an `InRep` derivation of exactly-one over the finite
relation family underlying `Γ`.
-/
noncomputable def exactlyOneInLocalRepOfHardCase {Γ : CSP.BoolLanguage}
    (hHard : HardCaseAssumptions Γ) :
    LocalRep.InRep (languageRelFinset Γ) 3 LocalRep.exactlyOneRel := by
  classical
  rcases HardCaseAssumptions.exists_horn_failure hHard with
    ⟨sWP, aWP, bWP, haWP, hbWP, hFailWP⟩
  rcases HardCaseAssumptions.exists_dual_horn_failure hHard with
    ⟨sWN, aWN, bWN, haWN, hbWN, hFailWN⟩
  rcases HardCaseAssumptions.exists_affine_failure hHard with
    ⟨sAff, aAff, bAff, cAff, haAff, hbAff, hcAff, hFailAff⟩
  rcases HardCaseAssumptions.exists_bijunctive_failure hHard with
    ⟨sBij, aBij, bBij, cBij, haBij, hbBij, hcBij, hFailBij⟩
  let RWP := bundledRelOf Γ sWP
  let RWN := bundledRelOf Γ sWN
  let RAff := bundledRelOf Γ sAff
  let RBij := bundledRelOf Γ sBij
  have hNotWP : ¬ LocalRep.LogRel.IsWeaklyPositive RWP.rel :=
    not_localRep_weaklyPositive_of_not_horn (R := Γ.relationOf sWP) (by
      intro hHorn
      exact hFailWP (hHorn aWP bWP haWP hbWP))
  have hNotWN : ¬ LocalRep.LogRel.IsWeaklyNegative RWN.rel :=
    not_localRep_weaklyNegative_of_not_dualHorn (R := Γ.relationOf sWN) (by
      intro hDual
      exact hFailWN (hDual aWN bWN haWN hbWN))
  have hNotAff : ¬ LocalRep.LogRel.IsAffine RAff.rel :=
    not_localRep_affine_of_not_affine (R := Γ.relationOf sAff) (by
      intro hAff
      exact hFailAff (hAff aAff bAff cAff haAff hbAff hcAff))
  have hNotBij : ¬ LocalRep.LogRel.IsBijunctive RBij.rel :=
    not_localRep_bijunctive_of_not_bijunctive (R := Γ.relationOf sBij) (by
      intro hBij
      exact hFailBij (hBij aBij bBij cBij haBij hbBij hcBij))
  have hNeq : LocalRep.InRep (languageRelFinset Γ) 2 LocalRep.neqRel :=
    LocalRep.neq_in_rep
      RWP (bundledRelOf_mem_languageRelFinset Γ sWP) hNotWP
      RWN (bundledRelOf_mem_languageRelFinset Γ sWN) hNotWN
  have hBinary :
      ∀ T : LocalRep.LogRel 2,
        T.card = 3 → LocalRep.InRep (languageRelFinset Γ) 2 T :=
    LocalRep.three_element_binary_in_rep
      RAff (bundledRelOf_mem_languageRelFinset Γ sAff) hNotAff hNeq
  exact
    LocalRep.exactlyOne_in_rep
      RBij (bundledRelOf_mem_languageRelFinset Γ sBij) hNotBij hNeq hBinary

end LocalRepBridge

/-- The native `Γ` constraint for a relation symbol, with free variables in order. -/
def identityRelationConstraint {Γ : CSP.BoolLanguage} (s : Γ.Symbol) : CSP.Constraint Γ where
  symbol := s
  vars := fun i => i

/-- Represent a native relation symbol by the corresponding one-constraint block. -/
def identityRelationFormula (Γ : CSP.BoolLanguage) (s : Γ.Symbol) :
    RelationFormula Γ (Γ.relationOf s).arity where
  constraints := [identityRelationConstraint s]
  notes := "Native relation symbol represented by one local constraint."

/-- The one-constraint native block represents exactly its underlying relation. -/
theorem identityRelationFormula_represents (Γ : CSP.BoolLanguage) (s : Γ.Symbol) :
    RepresentsRelation Γ (Γ.relationOf s) (identityRelationFormula Γ s) := by
  intro t
  constructor
  · intro ht
    refine ⟨fun _ => false, ?_⟩
    intro c hc
    simp [identityRelationFormula] at hc
    subst c
    have hTuple :
        (identityRelationConstraint s).assignmentTuple
          (extendTupleAssignment t (fun _ => false)) = t := by
      funext i
      exact extendTupleAssignment_of_lt t (fun _ => false) i.isLt
    change (Γ.relationOf s).Holds
      ((identityRelationConstraint s).assignmentTuple
        (extendTupleAssignment t (fun _ => false)))
    rw [hTuple]
    exact ht
  · rintro ⟨aux, hSat⟩
    have hConstraint :
        CSP.Constraint.Satisfies (identityRelationConstraint s)
          (extendTupleAssignment t aux) := by
      exact hSat (identityRelationConstraint s) (by simp [identityRelationFormula])
    have hTuple :
        (identityRelationConstraint s).assignmentTuple
          (extendTupleAssignment t aux) = t := by
      funext i
      exact extendTupleAssignment_of_lt t aux i.isLt
    change (Γ.relationOf s).Holds
      ((identityRelationConstraint s).assignmentTuple (extendTupleAssignment t aux)) at hConstraint
    rw [hTuple] at hConstraint
    exact hConstraint

/-- Every language represents itself through one native constraint per symbol. -/
def identityLanguageRepresentation (Γ : CSP.BoolLanguage) :
    LanguageRepresentation Γ Γ where
  block := identityRelationFormula Γ
  represents := identityRelationFormula_represents Γ
  notes := "Identity language representation."

/-- The generic semantic/costed representation certificate specialized to identity blocks. -/
noncomputable def identityRepresentationReductionCertificate (Γ : CSP.BoolLanguage) :
    RepresentationReductionCertificate Γ Γ :=
  representationReductionCertificateOfLanguageRepresentationAuto
    (identityLanguageRepresentation Γ)

/--
Any existing hard base certificate can be viewed as a classification route for
its own language via the identity representation.
-/
noncomputable def hardClassificationRouteOfBaseCertificate {Γ : CSP.BoolLanguage}
    (base : HardRelationCertificate Γ) :
    HardClassificationRoute Γ where
  Base := Γ
  baseCertificate := base
  representationCertificate := identityRepresentationReductionCertificate Γ
  notes := "Self route obtained from an existing hard base certificate."

/-- Self-route for the fixed local 3SAT-like base language. -/
noncomputable def hardClassificationRoute_threeSATLikeBase :
    HardClassificationRoute CSP.Examples.threeSATLikeLanguage :=
  hardClassificationRouteOfBaseCertificate hardBaseCertificate_threeSATLike

/-- Self-route for the fixed ordinary one-in-three base language. -/
noncomputable def hardClassificationRoute_oneInThreeBase :
    HardClassificationRoute CSP.Examples.oneInThreeLanguage :=
  hardClassificationRouteOfBaseCertificate hardBaseCertificate_oneInThree

/-- Self-route for the fixed ordinary NAE-3SAT base language. -/
noncomputable def hardClassificationRoute_nae3Base :
    HardClassificationRoute CSP.Examples.notAllEqual3Language :=
  hardClassificationRouteOfBaseCertificate hardBaseCertificate_nae3

/-- Section 3/4 witness that the 3SAT-like hard base is representable in `Γ`. -/
structure RepThreeSATLikeWitness (Γ : CSP.BoolLanguage) where
  representation : LanguageRepresentation CSP.Examples.threeSATLikeLanguage Γ
  notes : String := ""

/-- Section 3/4 witness that ordinary one-in-three is representable in `Γ`. -/
structure RepOneInThreeWitness (Γ : CSP.BoolLanguage) where
  representation : LanguageRepresentation CSP.Examples.oneInThreeLanguage Γ
  notes : String := ""

/-- Section 3/4 witness that ordinary NAE-3SAT is representable in `Γ`. -/
structure RepNAEWitness (Γ : CSP.BoolLanguage) where
  representation : LanguageRepresentation CSP.Examples.notAllEqual3Language Γ
  notes : String := ""

namespace RepThreeSATLikeWitness

/-- Build a 3SAT-like witness directly from proof-bearing blocks for the eight clause symbols. -/
def ofBlocks {Γ : CSP.BoolLanguage}
    (block : ∀ s : CSP.Examples.threeSATLikeLanguage.Symbol,
      RelationFormula Γ (CSP.Examples.threeSATLikeLanguage.relationOf s).arity)
    (represents : ∀ s : CSP.Examples.threeSATLikeLanguage.Symbol,
      RepresentsRelation Γ (CSP.Examples.threeSATLikeLanguage.relationOf s) (block s))
    (notes : String := "3SAT-like witness from explicit relation blocks.") :
    RepThreeSATLikeWitness Γ where
  representation :=
    { block := block
      represents := represents
      notes := notes }
  notes := notes

/-- Promote an already assembled language representation to a 3SAT-like witness. -/
def ofLanguageRepresentation {Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation CSP.Examples.threeSATLikeLanguage Γ)
    (notes : String := "3SAT-like witness from an explicit language representation.") :
    RepThreeSATLikeWitness Γ where
  representation := rep
  notes := notes

/-- Convert a 3SAT-like representation witness into a typed hard-classification route. -/
noncomputable def toRoute {Γ : CSP.BoolLanguage} (w : RepThreeSATLikeWitness Γ) :
    HardClassificationRoute Γ where
  Base := CSP.Examples.threeSATLikeLanguage
  baseCertificate := hardBaseCertificate_threeSATLike
  representationCertificate :=
    representationReductionCertificateOfLanguageRepresentationAuto w.representation
  notes := "Section 3/4 witness route through the 3SAT-like base language."

end RepThreeSATLikeWitness

namespace RepOneInThreeWitness

/-- Build an ordinary one-in-three witness from one proof-bearing ternary block. -/
def ofBlock {Γ : CSP.BoolLanguage}
    (block : RelationFormula Γ CSP.Examples.oneInThreeRel.arity)
    (represents : RepresentsRelation Γ CSP.Examples.oneInThreeRel block)
    (notes : String := "One-in-three witness from an explicit relation block.") :
    RepOneInThreeWitness Γ where
  representation :=
    { block := fun
        | CSP.Examples.OneInThreeSymbol.rel => block
      represents := fun
        | CSP.Examples.OneInThreeSymbol.rel => represents
      notes := notes }
  notes := notes

/-- Promote an already assembled language representation to a one-in-three witness. -/
def ofLanguageRepresentation {Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation CSP.Examples.oneInThreeLanguage Γ)
    (notes : String := "One-in-three witness from an explicit language representation.") :
    RepOneInThreeWitness Γ where
  representation := rep
  notes := notes

/-- Convert a one-in-three representation witness into a typed hard-classification route. -/
noncomputable def toRoute {Γ : CSP.BoolLanguage} (w : RepOneInThreeWitness Γ) :
    HardClassificationRoute Γ where
  Base := CSP.Examples.oneInThreeLanguage
  baseCertificate := hardBaseCertificate_oneInThree
  representationCertificate :=
    representationReductionCertificateOfLanguageRepresentationAuto w.representation
  notes := "Section 3/4 witness route through the ordinary one-in-three base language."

end RepOneInThreeWitness

namespace RepNAEWitness

/-- Build an ordinary NAE-3SAT witness from one proof-bearing ternary NAE block. -/
def ofBlock {Γ : CSP.BoolLanguage}
    (block : RelationFormula Γ CSP.Examples.notAllEqual3Rel.arity)
    (represents : RepresentsRelation Γ CSP.Examples.notAllEqual3Rel block)
    (notes : String := "NAE-3SAT witness from an explicit relation block.") :
    RepNAEWitness Γ where
  representation :=
    { block := fun
        | CSP.Examples.NAE3Symbol.rel => block
      represents := fun
        | CSP.Examples.NAE3Symbol.rel => represents
      notes := notes }
  notes := notes

/-- Promote an already assembled language representation to a NAE-3SAT witness. -/
def ofLanguageRepresentation {Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation CSP.Examples.notAllEqual3Language Γ)
    (notes : String := "NAE-3SAT witness from an explicit language representation.") :
    RepNAEWitness Γ where
  representation := rep
  notes := notes

/-- Convert a NAE-3SAT representation witness into a typed hard-classification route. -/
noncomputable def toRoute {Γ : CSP.BoolLanguage} (w : RepNAEWitness Γ) :
    HardClassificationRoute Γ where
  Base := CSP.Examples.notAllEqual3Language
  baseCertificate := hardBaseCertificate_nae3
  representationCertificate :=
    representationReductionCertificateOfLanguageRepresentationAuto w.representation
  notes := "Section 3/4 witness route through the ordinary NAE-3SAT base language."

end RepNAEWitness

/-- The hard base representation alternatives currently supported by the local route. -/
inductive HardBaseRepresentationWitness (Γ : CSP.BoolLanguage) where
  | threeSATLike : RepThreeSATLikeWitness Γ → HardBaseRepresentationWitness Γ
  | oneInThree : RepOneInThreeWitness Γ → HardBaseRepresentationWitness Γ
  | nae3 : RepNAEWitness Γ → HardBaseRepresentationWitness Γ

namespace HardBaseRepresentationWitness

/-- Which already-certified hard base a representation witness uses. -/
def baseKind {Γ : CSP.BoolLanguage} : HardBaseRepresentationWitness Γ → HardBaseRelationKind
  | threeSATLike _ => HardBaseRelationKind.threeSATLike
  | oneInThree _ => HardBaseRelationKind.oneInThree
  | nae3 _ => HardBaseRelationKind.nae3

/-- Package an explicit 3SAT-like language representation as a supported hard-base witness. -/
def ofThreeSATLikeRepresentation {Γ : CSP.BoolLanguage}
    (rep : LanguageRepresentation CSP.Examples.threeSATLikeLanguage Γ) :
    HardBaseRepresentationWitness Γ :=
  threeSATLike (RepThreeSATLikeWitness.ofLanguageRepresentation rep)

/-- Package an explicit one-in-three block as a supported hard-base witness. -/
def ofOneInThreeBlock {Γ : CSP.BoolLanguage}
    (block : RelationFormula Γ CSP.Examples.oneInThreeRel.arity)
    (represents : RepresentsRelation Γ CSP.Examples.oneInThreeRel block) :
    HardBaseRepresentationWitness Γ :=
  oneInThree (RepOneInThreeWitness.ofBlock block represents)

/-- Package an explicit NAE-3SAT block as a supported hard-base witness. -/
def ofNAEBlock {Γ : CSP.BoolLanguage}
    (block : RelationFormula Γ CSP.Examples.notAllEqual3Rel.arity)
    (represents : RepresentsRelation Γ CSP.Examples.notAllEqual3Rel block) :
    HardBaseRepresentationWitness Γ :=
  nae3 (RepNAEWitness.ofBlock block represents)

/-- Convert any supported hard-base representation witness into a classification route. -/
noncomputable def toRoute {Γ : CSP.BoolLanguage} :
    HardBaseRepresentationWitness Γ → HardClassificationRoute Γ
  | threeSATLike w => w.toRoute
  | oneInThree w => w.toRoute
  | nae3 w => w.toRoute

/-- Convert any supported hard-base representation witness into a hard certificate. -/
noncomputable def toHardRelationCertificate {Γ : CSP.BoolLanguage}
    (w : HardBaseRepresentationWitness Γ) :
    HardRelationCertificate Γ :=
  hardRelationCertificateOfClassificationRoute w.toRoute

end HardBaseRepresentationWitness

/--
The remaining Section 3/4 mathematical obligation: from the named hard-case
assumptions, produce one of the supported hard-base representation witnesses.
-/
abbrev Section34ClassificationWitness (Γ : CSP.BoolLanguage) : Type :=
  HardCaseAssumptions Γ → HardBaseRepresentationWitness Γ

/-- A Section 3/4 witness-producing theorem gives the requested typed route. -/
noncomputable def hardClassificationRouteOfSection34 {Γ : CSP.BoolLanguage}
    (classify : Section34ClassificationWitness Γ) :
    HardCaseAssumptions Γ → HardClassificationRoute Γ :=
  fun hHard => (classify hHard).toRoute

/-- A Section 3/4 witness-producing theorem gives the hard certificate builder. -/
noncomputable def hardRelationCertificateOfSection34 {Γ : CSP.BoolLanguage}
    (classify : Section34ClassificationWitness Γ) :
    HardCaseAssumptions Γ → HardRelationCertificate Γ :=
  fun hHard => (classify hHard).toHardRelationCertificate

/-- Package a Section 3/4 witness-producing theorem as the local hard-side statement. -/
theorem hardSideStatement_ofSection34Classification {Γ : CSP.BoolLanguage}
    (classify : Section34ClassificationWitness Γ) :
    hardSideStatement Γ :=
  hardSideStatement_ofHardClassificationRoute
    (hardClassificationRouteOfSection34 classify)

/-- Descriptor for the completed typed bridge from explicit Section 3/4 witness to route. -/
def hardClassificationBridgeDescriptor : StatementDescriptor :=
  { pdfReference := "Section 3 and Section 4 hard-side route"
    informalClaim :=
      "A Section 3/4 hard-base representation witness mechanically yields a typed \
       HardClassificationRoute, HardRelationCertificate, and hard-side statement."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.Hardness.hardClassificationRouteOfSection34"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Hardness.HardBaseRepresentationWitness"
      , "ComplexityReduction.Schaefer.Hardness.RepThreeSATLikeWitness"
      , "ComplexityReduction.Schaefer.Hardness.RepOneInThreeWitness"
      , "ComplexityReduction.Schaefer.Hardness.RepNAEWitness"
      , "ComplexityReduction.Schaefer.Hardness.representationReductionCertificateOfLanguageRepresentationAuto"
      , "ComplexityReduction.Schaefer.Hardness.hardBaseCertificate_threeSATLike"
      , "ComplexityReduction.Schaefer.Hardness.hardBaseCertificate_oneInThree"
      , "ComplexityReduction.Schaefer.Hardness.hardBaseCertificate_nae3"
      ]
    status := ProofStatus.done
    externalSymbols := []
    notes :=
      "This is the typed bridge from explicit witnesses to the hard route.  The \
       concrete nonempty witness builder is section34WitnessOfHardCase in \
       ComplexityReduction.Schaefer.Hardness.Constants." }

/-- Descriptor for the local nonempty Schaefer Section 3/4 witness theorem. -/
def section34WitnessTheoremDescriptor : StatementDescriptor :=
  { pdfReference := "Section 3 and Section 4 hard-side route"
    informalClaim :=
      "Under the paper's nonempty-relation precondition, the named hard-case assumptions \
       produce a supported hard-base representation witness."
    localTargetSymbol :=
      "ComplexityReduction.Schaefer.Hardness.section34WitnessOfHardCase"
    dependencies :=
      [ "ComplexityReduction.Schaefer.Hardness.AllRelationsNonempty"
      , "ComplexityReduction.Schaefer.Hardness.constantOrComplementiveWitnessOfHardCase"
      , "ComplexityReduction.Schaefer.Hardness.hardBaseRepresentationWitnessWithConstantsOfHardCase"
      , "ComplexityReduction.Schaefer.Hardness.repNAEWitnessOfComplementiveHardCase"
      ]
    status := ProofStatus.done
    externalSymbols :=
      [ "SchaeferDichotomy.classification_theorem"
      , "SchaeferDichotomy.constantElimWitnessOfLemma43"
      , "SchaeferDichotomy.schaefer_hardness_no_constants_log_nonempty_failure_witnesses_internal"
      ]
    notes :=
      "The theorem is defined in the downstream constants module because it depends on \
       the constants/complementive split.  Empty relations are handled by the P9 wrapper." }

end Hardness
end Schaefer
end ComplexityReduction
