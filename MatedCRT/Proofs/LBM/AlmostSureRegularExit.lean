import MatedCRT.Proofs.LBM.OutwardCrossing

/-! Transfer of Brownian radial excursions to LBM regular exits. -/

namespace MatedCRT

open MeasureTheory Set Filter Topology HarmonicBalls MarkovProcess Metric
open scoped ENNReal NNReal InnerProductSpace

/-- Almost-sure Brownian outward radial excursions imply almost-sure regular
exit of normalized Liouville Brownian motion, for almost every environment. -/
theorem MatedCRTEnv.IsValid.ae_rescaledLBM_ball_regular_of_brownian_outward_radial_excursion
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hm : 0 < S.m₀) {y z : ℂ} {r : ℝ}
    (hy : y ∈ ball z r)
    (hexcursion : ∀ᵐ b ∂planarBrownianMotion y,
      ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (ball z r) b).toNNReal,
        0 < ⟪b (ContinuousPath.exitTime (ball z r) b).toNNReal - z,
          b t - b (ContinuousPath.exitTime (ball z r) b).toNNReal⟫_ℝ) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      ∃ᶠ t in 𝓝[>] (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toNNReal,
        rescaledLBMPath (S.clock ω) S.m₀ b t ∉ closure (ball z r) := by
  filter_upwards [hS.isLQGClock] with ω hclock
  filter_upwards [(hclock y).2, ae_planarBrownianMotion_eval_zero y,
    ae_planarBrownianMotion_exit_any_ball_lt_top y z r, hexcursion] with b hb hstart hfin hexc
  exact rescaledLBM_ball_regular_of_brownian_outward_radial_excursion hb
    (hstart ▸ hy) hfin hm hexc

end MatedCRT
