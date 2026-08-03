import ComplexityReduction.Karp21.ExactCover.StructuredTM

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Direct TM-backed single-block construction for edge/color filler blocks in the
compact Chromatic-Number-to-Exact-Cover route.
-/

def colorFillerBlockInputEncodedType : EncodedType :=
  EncodedType.prod chromaticNumberStructuredEncodedType
    (EncodedType.prod EncodedType.nat EncodedType.nat)

def colorFillerBlockFast (I : ChromaticNumberInput) (i c : Nat) : List Nat :=
  [colorEdgeCodeFast I i c]

def colorFillerBlockExecutable (p : ChromaticNumberInput × (Nat × Nat)) : List Nat :=
  colorFillerBlockFast p.1 p.2.1 p.2.2

theorem colorFillerBlockFast_eq_colorFillerBlock
    {I : ChromaticNumberInput} {i c : Nat}
    (hi : i < I.graph.edges.length) (hc : c < I.colors) :
    colorFillerBlockFast I i c = colorFillerBlock I i c := by
  simp [colorFillerBlockFast, colorFillerBlock, colorEdgeCodeFast_eq_colorEdgeCode hi hc]

theorem colorFillerBlockExecutable_tm_polytime :
    TMPolyTimeMap
      colorFillerBlockInputEncodedType
      setStructuredEncodedType
      colorFillerBlockExecutable := by
  have hCode :
      TMPolyTimeMap
        colorFillerBlockInputEncodedType
        EncodedType.nat
        (fun p : ChromaticNumberInput × (Nat × Nat) =>
          colorEdgeCodeFast p.1 p.2.1 p.2.2) := by
    simpa [colorFillerBlockInputEncodedType, colorEdgeCodeFastInputEncodedType] using
      colorEdgeCodeFast_tm_polytime
  have hSingleton :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hCode
  simpa [Function.comp, colorFillerBlockExecutable, colorFillerBlockFast,
    setStructuredEncodedType] using hSingleton

end ExactCover
end Karp21
end ComplexityReduction
