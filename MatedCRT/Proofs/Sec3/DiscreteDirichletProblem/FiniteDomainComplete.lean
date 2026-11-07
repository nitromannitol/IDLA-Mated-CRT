import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.FiniteDomainBridge
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.PreparedVolumeGrowth
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedBoundaryProof

/-! Finite-domain representation for the prepared Dirichlet modulus. -/

namespace MatedCRT

/-- The prepared discrete modulus follows from the finite-domain Green
representation, mesh scaling and the exit-time estimates. -/
theorem dirichletDiscreteModulusPreparedStep_of_estimates
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (hfinite : FiniteDomainDirichletRepresentation) :
    DirichletDiscreteModulusPreparedStep 𝒮 :=
  dirichletDiscreteModulusPreparedStep_of_raw_representation 𝒮 hm h218 h217
    (dirichletRawRepresentationPreparedStep_of_finiteDomain 𝒮 hfinite)

/-- The prepared interior step follows from pointwise convergence, volume
growth, and the finite-domain representation. Its boundary data are those of
the frozen Dirichlet statement, not the projected data in the corrected paper. -/
theorem dirichletInteriorPreparedStep_of_finiteDomain
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hP : DirichletPointwiseStep 𝒮)
    (hfinite : FiniteDomainDirichletRepresentation) : DirichletInteriorPreparedStep 𝒮 :=
  dirichletInteriorPreparedStep_of_volumeGrowth 𝒮 h27 hP
    (dirichletDiscreteModulusPreparedStep_of_estimates 𝒮 hm h218
      (boundedExitTimeRV_of_steps h27) hfinite)

end MatedCRT

#print axioms MatedCRT.dirichletDiscreteModulusPreparedStep_of_estimates
#print axioms MatedCRT.dirichletInteriorPreparedStep_of_finiteDomain
