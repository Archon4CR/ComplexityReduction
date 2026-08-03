/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.CSP.FiniteDomain.Counting

/-!
Solution-bijection tools for finite-domain CSP counting.

The basic counting layer defines `Formula.solutionCount` as the cardinality of a
finite support solution set.  This module supplies proof-carrying wrappers that
turn explicit bijections between those finite solution objects into reusable
count-preservation certificates.
-/

namespace ComplexityReduction
namespace CSP
namespace FiniteDomain

namespace Formula

/-- A finite-support solution valuation of a finite-domain CSP formula. -/
abbrev SolutionValuation {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} (φ : Formula Γ) : Type :=
  { values : {x : Nat // x ∈ FiniteSupport.formulaVars φ} → D //
    values ∈ solutionSet φ }

/-- Solution valuations are finite because both the formula support and domain are finite. -/
noncomputable instance solutionValuation_fintype {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} (φ : Formula Γ) :
    Fintype (SolutionValuation φ) := by
  classical
  unfold SolutionValuation
  infer_instance

/-- `SolutionValuation` is definitionally the subtype of the finite solution set. -/
def solutionValuationEquivOfSubtype {D : Type} [Fintype D] [Inhabited D]
    {Γ : Language D} (φ : Formula Γ) :
    SolutionValuation φ ≃
      { values : {x : Nat // x ∈ FiniteSupport.formulaVars φ} → D //
        values ∈ solutionSet φ } :=
  Equiv.refl _

/-- A proof-carrying equivalence between the finite solution sets of two formulas. -/
structure SolutionEquivCertificate {D : Type} [Fintype D] [Inhabited D]
    {Γ Δ : Language D} (source : Formula Γ) (target : Formula Δ) where
  equiv : SolutionValuation source ≃ SolutionValuation target
  notes : String := ""

/-- A solution-set equivalence gives equality of finite-support solution counts. -/
theorem solutionCount_eq_of_solutionEquiv {D : Type} [Fintype D] [Inhabited D]
    {Γ Δ : Language D} {source : Formula Γ} {target : Formula Δ}
    (cert : SolutionEquivCertificate source target) :
    solutionCount target = solutionCount source := by
  classical
  unfold solutionCount
  have hCard :
      (solutionSet source).card = (solutionSet target).card := by
    refine Finset.card_bij
      (fun values hvalues => (cert.equiv ⟨values, hvalues⟩).1)
      (fun values hvalues => (cert.equiv ⟨values, hvalues⟩).2)
      ?inj
      ?surj
    · intro a ha b hb h
      have hSubtype :
          cert.equiv ⟨a, ha⟩ = cert.equiv ⟨b, hb⟩ := by
        exact Subtype.ext h
      exact congrArg Subtype.val (cert.equiv.injective hSubtype)
    · intro b hb
      refine ⟨(cert.equiv.symm ⟨b, hb⟩).1, (cert.equiv.symm ⟨b, hb⟩).2, ?_⟩
      exact congrArg Subtype.val (cert.equiv.apply_symm_apply ⟨b, hb⟩)
  exact hCard.symm

/-- A bijective map between solution valuations gives equality of solution counts. -/
theorem solutionCount_eq_of_bijective {D : Type} [Fintype D] [Inhabited D]
    {Γ Δ : Language D} {source : Formula Γ} {target : Formula Δ}
    (toFun : SolutionValuation source → SolutionValuation target)
    (hBij : Function.Bijective toFun) :
    solutionCount target = solutionCount source :=
  solutionCount_eq_of_solutionEquiv
    { equiv := Equiv.ofBijective toFun hBij
      notes := "constructed from a bijective map between finite-support solution valuations" }

end Formula

namespace PPDef

/--
Build a count-preserving pp-representation certificate from solution-set
equivalences for every source formula.
-/
noncomputable def countPreservingCertificateOfSolutionEquiv {D : Type}
    [Fintype D] [Inhabited D] {Δ Γ : Language D}
    (rep : LanguageRepresentation Δ Γ)
    (cert :
      ∀ φ : Formula Δ,
        Formula.SolutionEquivCertificate φ (formulaViaRepresentation rep φ))
    (notes : String := "") :
    CountPreservingRepresentationCertificate Δ Γ where
  representation := rep
  count_preserving := fun φ =>
    Formula.solutionCount_eq_of_solutionEquiv (cert φ)
  notes := notes

/-- Rewrite the pp-expanded solution count using a per-formula solution equivalence. -/
theorem solutionCount_viaSolutionEquiv {D : Type} [Fintype D] [Inhabited D]
    {Δ Γ : Language D} (rep : LanguageRepresentation Δ Γ)
    (cert :
      ∀ φ : Formula Δ,
        Formula.SolutionEquivCertificate φ (formulaViaRepresentation rep φ))
    (φ : Formula Δ) :
    Formula.solutionCount (formulaViaRepresentation rep φ) =
      Formula.solutionCount φ :=
  Formula.solutionCount_eq_of_solutionEquiv (cert φ)

end PPDef

end FiniteDomain

namespace CountingReduction

/-- Construct a counting reduction from a map with an exact count-preservation proof. -/
def of_count_eq {P Q : CountingProblem}
    (map : P.Instance.Carrier → Q.Instance.Carrier)
    (hCount : ∀ x, Q.count (map x) = P.count x) :
    CountingReduction P Q where
  map := map
  count_preserving := hCount

end CountingReduction

namespace ParsimoniousReduction

/-- Construct a parsimonious reduction from a map with an exact count-preservation proof. -/
def of_count_eq {P Q : CountingProblem}
    (map : P.Instance.Carrier → Q.Instance.Carrier)
    (hCount : ∀ x, Q.count (map x) = P.count x)
    (notes : String := "") :
    ParsimoniousReduction P Q where
  map := map
  count_preserving := hCount
  notes := notes

end ParsimoniousReduction

end CSP
end ComplexityReduction
