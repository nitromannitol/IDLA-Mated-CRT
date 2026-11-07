import MatedCRT.Proofs.Sec4.SubsequentialProperties.PreparedIdentification
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.PreparedProperties
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ConeScalingPositivity
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.PreparedInputs

/-! Theorem 4.1 from prepared estimates and cone scaling. -/

namespace MatedCRT

/-- Theorem 4.1 from Green-kernel convergence, the prepared estimates and
cone-environment scaling, without a separate exit-measurability hypothesis. -/
theorem convergenceDivisible_of_prepared_green_coneScaling
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt) (hcone : ConeEnvironmentScalingStep 𝒮) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_prepared_properties 𝒮
    (subsequentialPropertiesPrepared_of_identified_estimates 𝒮 hm
      (equibounded_of_inputs h27 h218 hm) (discreteLaplacianBoundCorrected 𝒮)
      h33 h35 h218 hH (boundedExitTimeRV_of_steps h27) h27)
    (obstacleLimitUniqueness 𝒮) (convergenceDivisibleEventMeasurable_of_scaling 𝒮 h27 hcone)

/-- Theorem 4.1 with Green-kernel convergence derived from its prepared
inputs. The cone-environment scaling step remains an explicit hypothesis. -/
theorem convergenceDivisible_of_prepared_discrete_coneScaling
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮) (h27 : VolumeGrowthStmt)
    (hcone : ConeEnvironmentScalingStep 𝒮) : ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_prepared_green_coneScaling 𝒮 hm
    (uniformConvergenceGreenKernel_of_prepared_inputs 𝒮 h210 h34 h214 h28 hm
      (boundedExitTimeRV_of_steps h27) h218 hH) h35 h218 hH h27 hcone

end MatedCRT

#print axioms MatedCRT.convergenceDivisible_of_prepared_green_coneScaling
#print axioms MatedCRT.convergenceDivisible_of_prepared_discrete_coneScaling
