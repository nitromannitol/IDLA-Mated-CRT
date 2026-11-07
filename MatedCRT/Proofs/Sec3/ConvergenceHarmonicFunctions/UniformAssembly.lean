import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ContinuumLimit

/-! # Uniform Poisson-extension step for corrected Lemma 3.6 -/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric _root_.HarmonicBalls MarkovProcess InnerProductSpace
open scoped ENNReal NNReal

/-- Uniform convergence of the projected discrete harmonic extensions to the
Poisson extension. This is the compactness and boundary-control part of
`LEMMA36-REPLACEMENT.md`, lines 491–589. -/
def CorrectedPoissonUniformStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ : ℂ → ℝ, ContinuousOn ψ (closedBall z r) →
    TendstoUniformlyOnInProbability S.P (projectedDiscreteHarmonicExtension S r z ψ)
      (fun _ => discPoissonExtension ψ z r) (closedBall z r)

/-- The uniform Poisson-extension step supplies every convergence and
continuum-identification clause of corrected Lemma 3.6. -/
theorem correctedHarmonicConvergence_of_uniform (𝒮 : SpaceFillingSLEModel)
    (huniform : CorrectedPoissonUniformStep 𝒮) : CorrectedHarmonicConvergenceStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ hψ
  have hu := huniform γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ hψ
  refine ⟨discPoissonExtension ψ z r,
    continuousOn_discPoissonExtension hr (hψ.mono sphere_subset_closedBall),
    harmonicOnNhd_discPoissonExtension ((hψ.mono sphere_subset_closedBall).circleIntegrable hr.le),
    ?_, ?_, hu⟩
  · intro x hx
    exact discPoissonExtension_of_notMem (disjoint_left.mp sphere_disjoint_ball hx)
  · intro y hy
    refine ⟨?_, correctedHarmonic_pointwise_of_uniform S r z ψ _ hu (ball_subset_closedBall hy)⟩
    have hm₀ := hS.m₀_pos hγ hγ2
    filter_upwards [hS.isLQGClock] with ω hc
    rw [discPoissonExtension_of_mem hy, ← integral_pathExitPosition_eq_discPoissonIntegral hr hψ hy]
    refine integral_congr_ae ?_
    filter_upwards [(hc y).2, ae_planarBrownianMotion_eval_zero y,
      ae_planarBrownianMotion_exit_any_ball_lt_top y z r] with b hclock hstart hfin
    rw [rescaledLBMExitPosition_eq_brownianExitPosition isOpen_ball hclock
      (by rw [hstart]; exact hy) hfin hm₀, pathExitPosition_eq_eval_exitTime]

/-- The corrected lemma follows from the uniform Poisson step and the
separately stated quantitative same-walk comparison. -/
theorem correctedLemma36_of_steps (𝒮 : SpaceFillingSLEModel)
    (huniform : CorrectedPoissonUniformStep 𝒮) (hrate : CorrectedHarmonicSameWalkRateStmt 𝒮) :
    CorrectedLemma36Stmt 𝒮 :=
  ⟨correctedHarmonicConvergence_of_uniform 𝒮 huniform, hrate⟩

end MatedCRT
