import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EventMeasurableOfVolumeGrowth
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LocalExitReduction
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.MaximumPrinciple
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-! # Convergence-event measurability from the mated-CRT inputs -/

namespace MatedCRT

open MeasureTheory HarmonicBalls Filter Metric Set

/-- Almost sure volume growth on each ball implies convergence-event
measurability for the mated-CRT map. -/
theorem convergenceDivisibleEventMeasurable_of_volumeGrowth_inputs
    (𝒮 : SpaceFillingSLEModel)
    (hV : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ R : ℝ, 0 < R → ∀ᵐ ω ∂S.P, ∃ βminus βplus,
        VolumeGrowth (S.μ ω) R βminus βplus) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 :=
  convergenceDivisibleEventMeasurable_of_volumeGrowth 𝒮 (adjacentCellsMeetAeStep 𝒮) hV

/-- With subsequential convergence and uniqueness, volume growth is needed
only on the positive integer-radius balls. -/
theorem convergenceDivisibleEventMeasurable_of_integer_volumeGrowth_inputs
    (𝒮 : SpaceFillingSLEModel) (h48 : SubsequentialPropertiesStmt 𝒮)
    (h46 : SubsequentialConvergenceStmt 𝒮) (hu : ObstacleLimitUniquenessStep 𝒮)
    (hV : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ n : ℕ, ∀ᵐ ω ∂S.P, ∃ βminus βplus,
        VolumeGrowth (S.μ ω) ((n : ℝ) + 1) βminus βplus) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 :=
  convergenceDivisibleEventMeasurable_of_integer_volumeGrowth 𝒮 h48 h46 hu
    (adjacentCellsMeetAeStep 𝒮) hV

/-- Lemma 2.7 and exit-event measurability imply convergence-event
measurability for the mated-CRT map. -/
theorem convergenceDivisibleEventMeasurable_of_local_exit_inputs
    (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt)
    (hexit : ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      ∀ t : ℝ, 0 < t → NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 :=
  convergenceDivisibleEventMeasurable_of_local_exit 𝒮 h27 (adjacentCellsMeetAeStep 𝒮) hexit

/-- Theorem 4.1 from subsequential convergence, Lemma 2.7, and null
measurability of the harmonic-ball exit event. -/
theorem convergenceDivisible_of_local_exit_inputs
    (𝒮 : SpaceFillingSLEModel) (h48 : SubsequentialPropertiesStmt 𝒮)
    (h46 : SubsequentialConvergenceStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hexit : ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      ∀ t : ℝ, 0 < t → NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_steps 𝒮 h48 h46 (obstacleLimitUniqueness 𝒮)
    (convergenceDivisibleEventMeasurable_of_local_exit_inputs 𝒮 h27 hexit)

/-- Theorem 4.1 from subsequential convergence and almost sure volume growth
on positive integer-radius balls. -/
theorem convergenceDivisible_of_integer_volumeGrowth_inputs
    (𝒮 : SpaceFillingSLEModel) (h48 : SubsequentialPropertiesStmt 𝒮)
    (h46 : SubsequentialConvergenceStmt 𝒮)
    (hV : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ n : ℕ, ∀ᵐ ω ∂S.P, ∃ βminus βplus,
        VolumeGrowth (S.μ ω) ((n : ℝ) + 1) βminus βplus) :
    ConvergenceDivisibleStmt 𝒮 :=
  convergenceDivisible_of_steps 𝒮 h48 h46 (obstacleLimitUniqueness 𝒮)
    (convergenceDivisibleEventMeasurable_of_integer_volumeGrowth_inputs 𝒮 h48 h46
      (obstacleLimitUniqueness 𝒮) hV)

end MatedCRT
