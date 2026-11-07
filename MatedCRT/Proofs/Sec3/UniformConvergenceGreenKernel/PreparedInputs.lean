import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.PreparedInteriorSubsequence
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedBoundaryProof

/-! Green-kernel convergence with the prepared compactness input discharged. -/

namespace MatedCRT

/-- Lemma 3.3 from the stated Green-kernel inputs and the estimates yielding
prepared discrete potential tightness. -/
theorem uniformConvergenceGreenKernel_of_prepared_inputs
    (𝒮 : SpaceFillingSLEModel)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hm : MepsScalingInput 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮) :
    UniformConvergenceGreenKernelStmt 𝒮 :=
  uniformConvergenceGreenKernel_of_prepared_tightness 𝒮 h210 h34 h214 h28
    (discretePotentialTightnessPrepared_of_inputs hm h217 h218 hH)

end MatedCRT

#print axioms MatedCRT.uniformConvergenceGreenKernel_of_prepared_inputs
