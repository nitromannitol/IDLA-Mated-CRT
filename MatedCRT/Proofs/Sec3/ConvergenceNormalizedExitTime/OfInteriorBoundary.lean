import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BoundaryReduction
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PotentialIdentification

/-! Lemma 3.7 reduced to interior convergence and the discrete boundary estimate. -/

namespace MatedCRT

/-- The continuum potential required in Lemma 3.7 follows from the exit-time
bound, leaving interior convergence and the discrete boundary estimate. -/
theorem convergenceNormalizedExitTime_of_interior_discrete_boundary
    (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h31 : DiscretePotentialTightnessStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (hinterior : NormalizedExitInteriorStep 𝒮)
    (hdisc : DiscreteExitBoundaryStep 𝒮) : ConvergenceNormalizedExitTimeStmt 𝒮 :=
  convergenceNormalizedExitTime_of_discrete_boundary 𝒮 h33 h29 h219 h35 h31 h28 h217
    (normalizedExitPotentialStep_of_boundedExitTime 𝒮 h217) hinterior hdisc

end MatedCRT
