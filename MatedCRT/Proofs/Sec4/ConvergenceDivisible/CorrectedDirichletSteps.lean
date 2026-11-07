import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CorrectedProjectedIdentification
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.CorrectedContinuum

namespace MatedCRT

open MeasureTheory _root_.HarmonicBalls

/-- Divisible-sandpile convergence with corrected 3.5 reduced to the
projected pointwise, boundary-barrier, and finite-domain obligations. -/
theorem convergenceDivisible_of_projected_dirichlet_steps
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h27 : VolumeGrowthStmt)
    (hfinite : FiniteDomainDirichletRepresentation) (hP : ProjectedDirichletPointwiseStep 𝒮)
    (hboundary : ProjectedDirichletBoundaryStep 𝒮)
    (hexit : ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      ∀ t : ℝ, 0 < t → NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_corrected_projected_estimates 𝒮 hm h47 h44 h210 h34 h214 h28
    (discreteDirichletProblemCorrected_of_pointwise_and_estimates 𝒮 h27 hm h218 hH h28 hfinite hP hboundary)
    h218 hH h217 h27 hexit


/-- The existing pointwise Dirichlet step also supplies the projected step
needed for divisible-sandpile convergence. -/
theorem convergenceDivisible_of_dirichlet_pointwise_step
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h47 : EquiboundedStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h27 : VolumeGrowthStmt)
    (hfinite : FiniteDomainDirichletRepresentation) (hP : DirichletPointwiseStep 𝒮)
    (h36 : ConvergenceHarmonicFunctionsStmt 𝒮)
    (hboundary : ProjectedDirichletBoundaryStep 𝒮)
    (hexit : ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      ∀ t : ℝ, 0 < t → NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_projected_dirichlet_steps 𝒮 hm h47 h44 h210 h34 h214 h28
    h218 hH h217 h27 hfinite
    (projectedDirichletPointwiseStep_of_pointwise 𝒮 hP h36 h34
      (expectedExitTimeExplicitBound_of_steps h217 h218) h28) hboundary hexit


end MatedCRT

#print axioms MatedCRT.convergenceDivisible_of_projected_dirichlet_steps
#print axioms MatedCRT.convergenceDivisible_of_dirichlet_pointwise_step
