/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Karp21.ThreeDimensionalMatching
import ComplexityReduction.Karp21.SetCovering.Base
import ComplexityReduction.Karp21.HittingSet.StructuredRoute

/-!
Reusable structured projections and tuple reifiers for the compact
Exact-Cover-to-3-Dimensional-Matching route.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

/-! ### Source projections -/

theorem exactCoverSystem_encode (I : ExactCoverInput) :
    setSystemStructuredEncodedType.encode I.system =
      exactCoverStructuredEncodedType.encode I := by
  rfl

noncomputable def exactCoverSystemTMBackedMap :
    TMBackedCostedMap
      exactCoverStructuredEncodedType
      setSystemStructuredEncodedType
      (fun I : ExactCoverInput => I.system) :=
  TMBackedCostedMap.ofEncodingEquiv
    exactCoverStructuredEncodedType
    setSystemStructuredEncodedType
    (fun I : ExactCoverInput => I.system)
    (Equiv.refl exactCoverStructuredEncodedType.Symbol)
    (by
      intro I
      change setSystemStructuredEncodedType.encode I.system =
        (exactCoverStructuredEncodedType.encode I).map id
      simp [exactCoverSystem_encode])

theorem exactCoverSystemTuple_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      setSystemTupleStructuredEncodedType
      (fun I : ExactCoverInput => (I.system.universeSize, I.system.sets)) := by
  have hSystem := exactCoverSystemTMBackedMap.tm_polytime
  have hTuple := HittingSet.setSystemInputToTupleTMBackedMap.tm_polytime
  have hComp := TMPolyTimeMap.comp hTuple hSystem
  simpa [Function.comp, HittingSet.setSystemInputToTuple] using hComp

theorem exactCoverUniverseSize_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      EncodedType.nat
      (fun I : ExactCoverInput => I.system.universeSize) := by
  have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hFst exactCoverSystemTuple_tm_polytime
  simpa [Function.comp, setSystemTupleStructuredEncodedType] using hComp

theorem exactCoverSets_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      setFamilyStructuredEncodedType
      (fun I : ExactCoverInput => I.system.sets) := by
  have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd exactCoverSystemTuple_tm_polytime
  simpa [Function.comp, setSystemTupleStructuredEncodedType] using hComp

theorem exactCoverSetsLength_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      EncodedType.nat
      (fun I : ExactCoverInput => I.system.sets.length) := by
  have hComp := TMPolyTimeMap.comp
    (HittingSet.listLengthTMBackedMap setStructuredEncodedType).tm_polytime
    exactCoverSets_tm_polytime
  simpa [Function.comp, setFamilyStructuredEncodedType] using hComp

/-! ### 3DM tuple reifier -/

def threeDimensionalMatchingTupleToInput
    (p : threeDimensionalMatchingTupleStructuredEncodedType.Carrier) :
    ThreeDimensionalMatchingInput where
  xSize := p.1
  ySize := p.2.1
  zSize := p.2.2.1
  triples := p.2.2.2.1
  k := p.2.2.2.2

theorem threeDimensionalMatchingTupleToInput_encode
    (p : threeDimensionalMatchingTupleStructuredEncodedType.Carrier) :
    threeDimensionalMatchingStructuredEncodedType.encode
        (threeDimensionalMatchingTupleToInput p) =
      threeDimensionalMatchingTupleStructuredEncodedType.encode p := by
  rcases p with ⟨xSize, ySize, zSize, triples, k⟩
  rfl

noncomputable def threeDimensionalMatchingTupleToInputTMBackedMap :
    TMBackedCostedMap
      threeDimensionalMatchingTupleStructuredEncodedType
      threeDimensionalMatchingStructuredEncodedType
      threeDimensionalMatchingTupleToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    threeDimensionalMatchingTupleStructuredEncodedType
    threeDimensionalMatchingStructuredEncodedType
    threeDimensionalMatchingTupleToInput
    (Equiv.refl threeDimensionalMatchingTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change threeDimensionalMatchingStructuredEncodedType.encode
          (threeDimensionalMatchingTupleToInput p) =
        (threeDimensionalMatchingTupleStructuredEncodedType.encode p).map id
      simp [threeDimensionalMatchingTupleToInput_encode])

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
