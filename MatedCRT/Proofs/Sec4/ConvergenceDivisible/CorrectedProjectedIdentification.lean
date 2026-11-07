import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ProjectedIdentification
import MatedCRT.Proofs.Sec4.SubsequentialProperties.DirichletBoundaryComparison

/-! Divisible-sandpile convergence with projected Dirichlet data. -/

namespace MatedCRT

open MeasureTheory _root_.HarmonicBalls

/-- Theorem 4.1 from the corrected Dirichlet statement and the displayed
estimates; the hat boundary comparison is proved by small-cell estimates. -/
theorem convergenceDivisible_of_corrected_projected_estimates
    (𝒮 : SpaceFillingSLEModel) (hscale : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h35 : DiscreteDirichletProblemCorrectedStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h27 : VolumeGrowthStmt)
    (hexit : ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      ∀ t : ℝ, 0 < t → NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_projection_stability 𝒮 hscale h47 h44 h210 h34 h214 h28
    h35 h218 hH h217 h27 (hatDirichletProjectionStabilityStep 𝒮) hexit

end MatedCRT

#print axioms MatedCRT.convergenceDivisible_of_corrected_projected_estimates
