import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LeastMeasurableOfVolumeGrowth
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ContinuumOutsideBall
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.PathwiseEventMeasurability

/-! # Convergence-event measurability from volume growth -/

namespace MatedCRT

open MeasureTheory Filter Metric HarmonicBalls Set TopologicalSpace

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

/-- The pathwise convergence inputs reduce the volume-growth requirement to
the countable family of balls with positive integer radii. -/
theorem convergenceDivisibleEventMeasurable_of_integer_volumeGrowth
    (𝒮 : SpaceFillingSLEModel) (h48 : SubsequentialPropertiesStmt 𝒮)
    (h46 : SubsequentialConvergenceStmt 𝒮) (hu : ObstacleLimitUniquenessStep 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮)
    (hV : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ n : ℕ, ∀ᵐ ω ∂S.P, ∃ βminus βplus,
        VolumeGrowth (S.μ ω) ((n : ℝ) + 1) βminus βplus) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  obtain ⟨C₀, hcount, hdense⟩ := TopologicalSpace.exists_countable_dense ℂ
  let C : Set ℂ := C₀ ∪ {0}
  have hC : C.Countable := hcount.union (countable_singleton 0)
  have hd : Dense C := hdense.mono subset_union_left
  have hzero : (0 : ℂ) ∈ C := Or.inr rfl
  apply convergenceDivisibleEventMeasurable_of_countable_continuum_evaluations
    𝒮 h48 h46 hu hcell C hC hd hzero
  intro γ hγ hγ' Ω _ S hS q hq n x _
  have hR : 0 < (n : ℝ) + 1 := by positivity
  by_cases hx : x ∈ closedBall (0 : ℂ) ((n : ℝ) + 1)
  · exact hS.aemeasurable_leastSupersolution_of_volumeGrowth _ _ 0 x hR hq
      (mem_ball_self hR) hx (hV γ hγ hγ' Ω S hS n)
  · have heq : (fun ω => leastSupersolution (S.μ ω) ((n : ℝ) + 1) 0 q x) =
        fun _ => 0 := by
      funext ω
      exact leastSupersolution_eq_zero_of_notMem_closedBall (S.μ ω) _ _ 0 x hq.le hx
    rw [heq]
    exact aemeasurable_const

end MatedCRT
