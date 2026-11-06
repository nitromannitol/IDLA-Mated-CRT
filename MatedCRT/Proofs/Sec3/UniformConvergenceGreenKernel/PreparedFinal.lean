import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.PreparedInteriorStep
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.PreparedBoundaryStep

/-! The prepared-sequence reduction of Lemma 3.3. -/

namespace MatedCRT

/-- Lemma 3.3 from the prepared tightness statement and the remaining
prepared subsequence identification obligation. -/
theorem uniformConvergenceGreenKernel_of_prepared_subsequence
    (𝒮 : SpaceFillingSLEModel)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    (hsub : GreenKernelPreparedSubsequenceStep 𝒮) : UniformConvergenceGreenKernelStmt 𝒮 :=
  uniformConvergenceGreenKernel_of_prepared_interior 𝒮 h210 h34 h214 h28 h31
    (maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮))
    (greenKernelInteriorPreparedStep_of_subsequence 𝒮 hsub)

end MatedCRT
