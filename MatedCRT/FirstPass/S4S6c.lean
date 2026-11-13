import MatedCRT.FirstPass.Frozen.S3S4
import MatedCRT.FirstPass.Frozen.S4S6c
import MatedCRT.FirstPass.S4S6c.ConeScalingLaw
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.PreparedConeScaling

/-!
# First pass, Section 4: Theorem 4.1 with the frozen cone-scaling law

`firstPass_4_1_coneLaw` is `firstPass_4_1` (FirstPass/S3S4.lean) with the hypothesis
`FrozenConeEnvironmentScaling` replaced by the cone-scaling law `FrozenConeScalingLaw`
(Frozen/S4S6c.lean). The chain below is the prepared-estimate route of `PreparedConeScaling.lean`, with the
event-measurability step taken from `FirstPass/S4S6c/ConeScalingLaw.lean`.
-/

namespace MatedCRT

/-- Theorem 4.1 (prepared green-kernel route) with the frozen cone-scaling law. -/
theorem convergenceDivisible_of_prepared_green_coneScalingLaw
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt) (hcone : FrozenConeScalingLaw 𝒮) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_prepared_properties 𝒮
    (subsequentialPropertiesPrepared_of_identified_estimates 𝒮 hm
      (equibounded_of_inputs h27 h218 hm) (discreteLaplacianBoundCorrected 𝒮)
      h33 h35 h218 hH (boundedExitTimeRV_of_steps h27) h27)
    (obstacleLimitUniqueness 𝒮) (convergenceDivisibleEventMeasurable_of_scalingLaw 𝒮 h27 hcone)

/-- Theorem 4.1 (discrete route, prepared inputs) with the frozen cone-scaling law. -/
theorem convergenceDivisible_of_prepared_discrete_coneScalingLaw
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮) (h27 : VolumeGrowthStmt)
    (hcone : FrozenConeScalingLaw 𝒮) : ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_prepared_green_coneScalingLaw 𝒮 hm
    (uniformConvergenceGreenKernel_of_prepared_inputs 𝒮 h210 h34 h214 h28 hm
      (boundedExitTimeRV_of_steps h27) h218 hH) h35 h218 hH h27 hcone

/-- **Theorem 4.1** (theorem:convergence-divisible), cone-scaling-law form. Hypotheses as in `firstPass_4_1`
(FirstPass/S3S4.lean), except the cone environment scaling, which is the frozen cone-scaling law
`FrozenConeScalingLaw` (DMS14 Prop 4.13(i) in law; truth-checked). -/
theorem firstPass_4_1_coneLaw {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_prepared_discrete_coneScalingLaw 𝒮 hm h210 h34 h214 h28 h35 h218 hH h27 hcone

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.firstPass_4_1_coneLaw
