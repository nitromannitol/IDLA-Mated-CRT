import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CorrectedDirichletSteps
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.PreparedConeScaling
import MatedCRT.Proofs.Sec4.SubsequentialProperties.DirichletBoundaryComparison

/-! Prepared divisible-sandpile convergence with projected Dirichlet data. -/

namespace MatedCRT

/-- Theorem 4.1 from corrected projected Dirichlet data and cone-environment
scaling. All Green-kernel, tightness and boundary-comparison inputs are explicit. -/
theorem convergenceDivisible_of_corrected_dirichlet_coneScaling
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮) (h27 : VolumeGrowthStmt)
    (hcone : ConeEnvironmentScalingStep 𝒮) : ConvergenceDivisibleStmt 𝒮 := by
  have h217 := boundedExitTimeRV_of_steps h27
  have h33 := uniformConvergenceGreenKernel_of_prepared_inputs 𝒮 h210 h34 h214 h28 hm h217 h218 hH
  have h37 := convergenceNormalizedExitTime_of_corrected_prepared_estimates 𝒮 hm h33 h35 h217 h218 hH
  have hid := odometerPropertiesPreparedIdentificationStep_of_projection_stability 𝒮 h33 h35 h37
    (maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)) h28 (hatDirichletProjectionStabilityStep 𝒮)
  have h48 := subsequentialPropertiesPrepared_of_corrected_estimates 𝒮 hm
    (equibounded_of_inputs h27 h218 hm) (discreteLaplacianBoundCorrected 𝒮)
    h33 h35 h218 hH h217 h27 hid
  exact convergenceDivisible_of_prepared_properties 𝒮 h48 (obstacleLimitUniqueness 𝒮)
    (convergenceDivisibleEventMeasurable_of_scaling 𝒮 h27 hcone)

/-- The projected Dirichlet input reduces to the finite-domain representation,
pointwise convergence and boundary-barrier obligations. -/
theorem convergenceDivisible_of_projected_steps_coneScaling
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt) (hcone : ConeEnvironmentScalingStep 𝒮)
    (hfinite : FiniteDomainDirichletRepresentation) (hP : ProjectedDirichletPointwiseStep 𝒮)
    (hboundary : ProjectedDirichletBoundaryStep 𝒮) : ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_corrected_dirichlet_coneScaling 𝒮 hm h210 h34 h214 h28
    (discreteDirichletProblemCorrected_of_pointwise_and_estimates 𝒮 h27 hm h218 hH h28 hfinite hP hboundary)
    h218 hH h27 hcone

end MatedCRT

#print axioms MatedCRT.convergenceDivisible_of_corrected_dirichlet_coneScaling
#print axioms MatedCRT.convergenceDivisible_of_projected_steps_coneScaling
