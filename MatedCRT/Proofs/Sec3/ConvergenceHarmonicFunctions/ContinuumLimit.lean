import MatedCRT.Draft.Section3HarmonicCorrected
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.Limit

/-! # Continuum harmonic extension for corrected Lemma 3.6 -/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric _root_.HarmonicBalls MarkovProcess InnerProductSpace
open scoped ENNReal NNReal

/-- For continuous closed-disc data, the rescaled LBM exit expectation is the
deterministic Poisson extension. See `LEMMA36-REPLACEMENT.md`, lines 471–490. -/
theorem correctedHarmonic_continuum_of_inputs {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {r : ℝ} {z : ℂ}
    (hr : 0 < r) {ψ : ℂ → ℝ} (hψ : ContinuousOn ψ (closedBall z r)) :
    ∃ u : ℂ → ℝ, ContinuousOn u (closedBall z r) ∧ HarmonicOnNhd u (ball z r) ∧
      (∀ x ∈ sphere z r, u x = ψ x) ∧ ∀ y ∈ ball z r, ∀ᵐ ω ∂S.P,
        (∫ b, ψ (pathExitPosition (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))
          ∂planarBrownianMotion y) = u y := by
  refine ⟨discPoissonExtension ψ z r,
    continuousOn_discPoissonExtension hr (hψ.mono sphere_subset_closedBall),
    harmonicOnNhd_discPoissonExtension ((hψ.mono sphere_subset_closedBall).circleIntegrable hr.le),
    ?_, ?_⟩
  · intro x hx
    exact discPoissonExtension_of_notMem (disjoint_left.mp sphere_disjoint_ball hx)
  · intro y hy
    have hm₀ := hS.m₀_pos hγ hγ2
    filter_upwards [hS.isLQGClock] with ω hc
    rw [discPoissonExtension_of_mem hy, ← integral_pathExitPosition_eq_discPoissonIntegral hr hψ hy]
    refine integral_congr_ae ?_
    filter_upwards [(hc y).2, ae_planarBrownianMotion_eval_zero y,
      ae_planarBrownianMotion_exit_any_ball_lt_top y z r] with b hclock hstart hfin
    rw [rescaledLBMExitPosition_eq_brownianExitPosition isOpen_ball hclock
      (by rw [hstart]; exact hy) hfin hm₀, pathExitPosition_eq_eval_exitTime]

/-- Uniform convergence in probability on the closed disc implies pointwise
convergence there, without measurability assumptions on the supremum event. -/
theorem correctedHarmonic_pointwise_of_uniform {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (r : ℝ) (z : ℂ) (ψ u : ℂ → ℝ)
    (hu : TendstoUniformlyOnInProbability S.P (projectedDiscreteHarmonicExtension S r z ψ)
      (fun _ => u) (closedBall z r)) {y : ℂ} (hy : y ∈ closedBall z r) :
    TendstoInProbability S.P (fun ε ω => projectedDiscreteHarmonicExtension S r z ψ ε ω y)
      (fun _ => u y) := by
  intro δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hu δ hδ)
    (fun _ => zero_le) fun ε => ?_
  apply measure_mono
  intro ω hω
  exact ⟨y, hy, hω⟩

end MatedCRT
