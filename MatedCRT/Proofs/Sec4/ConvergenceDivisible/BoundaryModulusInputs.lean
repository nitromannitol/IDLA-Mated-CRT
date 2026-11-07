import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CorrectedConeScaling
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryCrossModulus

/-! Corrected Dirichlet and divisible-sandpile reductions using boundary-pair control. -/

namespace MatedCRT

/-- Corrected Lemma 3.5 from pointwise convergence, finite-domain representation,
    and boundary equicontinuity in probability. -/
theorem discreteDirichletProblemCorrected_of_boundary_modulus
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮)
    (hfinite : FiniteDomainDirichletRepresentation) (hP : ProjectedDirichletPointwiseStep 𝒮)
    (hboundary : ProjectedDirichletBoundaryModulusStep 𝒮) :
    DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  discreteDirichletProblemCorrected_of_pointwise_and_estimates 𝒮 h27 hm h218 hH h28
    hfinite hP (projectedDirichletBoundaryStep_of_boundary_modulus 𝒮 h27 hm hboundary)

/-- Divisible-sandpile convergence using the boundary-pair modulus in place of
    the full projected Dirichlet boundary-layer input. -/
theorem convergenceDivisible_of_boundary_modulus_coneScaling
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt) (hcone : ConeEnvironmentScalingStep 𝒮)
    (hfinite : FiniteDomainDirichletRepresentation) (hP : ProjectedDirichletPointwiseStep 𝒮)
    (hboundary : ProjectedDirichletBoundaryModulusStep 𝒮) : ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_projected_steps_coneScaling 𝒮 hm h210 h34 h214 h28 h218 hH h27 hcone
    hfinite hP (projectedDirichletBoundaryStep_of_boundary_modulus 𝒮 h27 hm hboundary)

end MatedCRT

#print axioms MatedCRT.discreteDirichletProblemCorrected_of_boundary_modulus
#print axioms MatedCRT.convergenceDivisible_of_boundary_modulus_coneScaling
