import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LeastMeasurableOfVolumeGrowth
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ContinuumOutsideBall

/-! # Convergence-event measurability from volume growth -/

namespace MatedCRT

open MeasureTheory Filter Metric HarmonicBalls

/-- Almost sure volume growth on each ball and intersection of adjacent
cells imply measurability of the convergence events. -/
theorem convergenceDivisibleEventMeasurable_of_volumeGrowth
    (𝒮 : SpaceFillingSLEModel) (hcell : AdjacentCellsMeetAeStep 𝒮)
    (hV : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ R : ℝ, 0 < R → ∀ᵐ ω ∂S.P, ∃ βminus βplus,
        VolumeGrowth (S.μ ω) R βminus βplus) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  apply convergenceDivisibleEventMeasurable_of_pointwise_on_ball 𝒮 hcell
  intro γ hγ hγ' Ω _ S hS R t hR ht x hx
  exact hS.aemeasurable_leastSupersolution_of_volumeGrowth R t 0 x hR ht
    (mem_ball_self hR) (ball_subset_closedBall hx) (hV γ hγ hγ' Ω S hS R hR)

end MatedCRT
