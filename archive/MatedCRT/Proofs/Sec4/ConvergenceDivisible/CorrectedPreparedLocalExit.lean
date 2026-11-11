import MatedCRT.Proofs.Sec4.ConvergenceDivisible.PreparedPathwiseMeasurability
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.CorrectedHarmonicPrepared

/-! Corrected divisible-sandpile convergence from cluster exit measurability. -/

namespace MatedCRT

open MeasureTheory Set _root_.HarmonicBalls

/-- Corrected harmonic convergence and the discrete estimates imply divisible
sandpile convergence when the cluster exit event is null measurable. -/
theorem convergenceDivisible_of_corrected_harmonic_measurable_exit
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h210 : DegreeMeasureConvergenceStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (h27 : VolumeGrowthStmt) (hfinite : FiniteDomainDirichletRepresentation)
    (h36 : CorrectedHarmonicConvergenceStmt 𝒮)
    (hexit : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      ∀ t : ℝ, 0 < t → NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_prepared_properties_measurable_exit 𝒮
    (subsequentialPropertiesPrepared_of_corrected_harmonic_estimates 𝒮 hm h210 h34 h214 h28
      h218 hH h27 hfinite h36) (obstacleLimitUniqueness 𝒮) (adjacentCellsMeetAeStep 𝒮) hexit

end MatedCRT

#print axioms MatedCRT.convergenceDivisible_of_corrected_harmonic_measurable_exit
