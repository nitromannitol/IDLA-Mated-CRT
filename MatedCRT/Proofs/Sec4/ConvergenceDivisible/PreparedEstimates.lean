import MatedCRT.Proofs.Sec4.ConvergenceDivisible.PreparedProperties
import MatedCRT.Proofs.Sec4.SubsequentialProperties.PreparedInputs
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.PreparedInputs
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.FromInputs

/-! Theorem 4.1 from the prepared subsequential properties and discrete estimates. -/

namespace MatedCRT

open MeasureTheory _root_.HarmonicBalls

/-- Theorem 4.1 with prepared compactness and normalized exit-time convergence
derived from the Green-kernel, exit-time and Hölder estimates. -/
theorem convergenceDivisible_of_prepared_green_estimates
    (𝒮 : SpaceFillingSLEModel) (hscale : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h27 : VolumeGrowthStmt)
    (hid : OdometerPropertiesPreparedIdentificationStep 𝒮)
    (hu : ObstacleLimitUniquenessStep 𝒮) (hmeas : ConvergenceDivisibleEventMeasurableStep 𝒮) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_prepared_properties 𝒮
    (subsequentialPropertiesPrepared_of_green_and_estimates 𝒮 hscale h47 h44 h33 h35
      h218 hH h217 h27 hid) hu hmeas

/-- Theorem 4.1 with Green-kernel convergence also supplied by the prepared
tightness estimates and the cited Green-kernel inputs. -/
theorem convergenceDivisible_of_prepared_discrete_estimates
    (𝒮 : SpaceFillingSLEModel) (hscale : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h27 : VolumeGrowthStmt) (hid : OdometerPropertiesPreparedIdentificationStep 𝒮)
    (hu : ObstacleLimitUniquenessStep 𝒮) (hmeas : ConvergenceDivisibleEventMeasurableStep 𝒮) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_prepared_green_estimates 𝒮 hscale h47 h44
    (uniformConvergenceGreenKernel_of_prepared_inputs 𝒮 h210 h34 h214 h28 hscale h217 h218 hH)
    h35 h218 hH h217 h27 hid hu hmeas

/-- Theorem 4.1 from the prepared discrete estimates, with obstacle uniqueness
proved and convergence-event measurability reduced to the cluster exit event. -/
theorem convergenceDivisible_of_prepared_estimates_local_exit
    (𝒮 : SpaceFillingSLEModel) (hscale : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h27 : VolumeGrowthStmt) (hid : OdometerPropertiesPreparedIdentificationStep 𝒮)
    (hexit : ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      ∀ t : ℝ, 0 < t → NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_prepared_discrete_estimates 𝒮 hscale h47 h44 h210 h34 h214 h28
    h35 h218 hH h217 h27 hid (obstacleLimitUniqueness 𝒮)
    (convergenceDivisibleEventMeasurable_of_local_exit_inputs 𝒮 h27 hexit)

end MatedCRT

#print axioms MatedCRT.convergenceDivisible_of_prepared_green_estimates
#print axioms MatedCRT.convergenceDivisible_of_prepared_discrete_estimates
#print axioms MatedCRT.convergenceDivisible_of_prepared_estimates_local_exit
