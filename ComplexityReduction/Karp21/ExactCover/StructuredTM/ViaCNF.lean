import ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.Assembly
import ComplexityReduction.Karp21.Satisfiability.Reductions
import ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute.TextbookMap
import ComplexityReduction.Karp21.ExactCover.StructuredTM.Assembly

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Direct TM-backed assembly of the structured Set-Covering-to-Exact-Cover route
through the compact CNF gadget.
-/

noncomputable def setCoveringToExactCoverViaCNFStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      setCoveringStructuredDecisionProblem
      exactCoverStructuredDecisionProblem :=
  TMBackedCostedReduction.comp
    chromaticNumberToExactCoverStructuredTMBackedKarpReduction
    (TMBackedCostedReduction.comp
      ChromaticNumber.threeSATToChromaticNumberStructuredTMBackedKarpReduction
      (TMBackedCostedReduction.comp
        cnfSATToThreeSATStructuredTMBackedKarpReduction
        setCoveringToSatisfiabilityStructuredTMBackedKarpReduction))

/--
Public P16c structured Set-Covering-to-Exact-Cover reduction via the compact
CNF route, projected from the direct TM-backed assembly.
-/
noncomputable def setCoveringToExactCoverViaCNFStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      setCoveringStructuredDecisionProblem
      exactCoverStructuredDecisionProblem :=
  setCoveringToExactCoverViaCNFStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- Direct TM-facing structured Set-Covering-to-Exact-Cover reduction via CNF. -/
noncomputable def setCoveringToExactCoverViaCNFStructuredTMKarpReduction :
    TMKarpReduction
      setCoveringStructuredDecisionProblem
      exactCoverStructuredDecisionProblem :=
  setCoveringToExactCoverViaCNFStructuredTMBackedKarpReduction.toTMKarpReduction

end ExactCover
end Karp21
end ComplexityReduction
