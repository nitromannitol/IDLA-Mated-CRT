import MatedCRT.Proofs.Sec4.ConvergenceDivisible.PreparedEstimates
import MatedCRT.Proofs.Sec4.SubsequentialProperties.PreparedIdentification

/-! Theorem 4.1 with the prepared identification obligation discharged. -/

namespace MatedCRT

open MeasureTheory _root_.HarmonicBalls

/-- Theorem 4.1 from discrete estimates, with every-limit identification
proved from Green-kernel and normalized exit-time convergence. -/
theorem convergenceDivisible_of_prepared_estimates_identified
    (𝒮 : SpaceFillingSLEModel) (hscale : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h27 : VolumeGrowthStmt)
    (hexit : ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      ∀ t : ℝ, 0 < t → NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    ConvergenceDivisibleStmt 𝒮 := by
  have h33 := uniformConvergenceGreenKernel_of_prepared_inputs 𝒮 h210 h34 h214 h28
    hscale h217 h218 hH
  have h37 := convergenceNormalizedExitTime_of_prepared_estimates 𝒮 hscale h33 h35 h217 h218 hH
  have h213 : MaximumPrincipleStmt 𝒮 := maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)
  exact convergenceDivisible_of_prepared_estimates_local_exit 𝒮 hscale h47 h44 h210 h34 h214 h28
    h35 h218 hH h217 h27 (odometerPropertiesPreparedIdentificationStep_of_inputs 𝒮 h33 h35 h37 h213)
    hexit

end MatedCRT

#print axioms MatedCRT.convergenceDivisible_of_prepared_estimates_identified
