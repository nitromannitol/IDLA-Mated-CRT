import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ClockInverseUniform
import MatedCRT.Proofs.LBM.TimeChangeContinuity

/-!
# Locally uniform convergence of inverse clocks and of time-changed Brownian paths

For time-change clocks (continuous, strictly increasing, started at `0`, tending to `∞`), locally uniform convergence
of the clocks `A n → A₀` on `[0, ∞)` gives locally uniform convergence of their inverses
`clockInverse (A n) → clockInverse A₀`: the inverse values are bracketed using uniform bounds on the clocks and the
positive increments of the limiting clock (`clockInverse_tendsto_uniform`). Composing with a fixed continuous
Brownian path `b` preserves locally uniform convergence (continuity of post-composition in the compact-open
topology), so the Liouville Brownian motion paths `b ∘ (F n b)⁻¹` converge locally uniformly to `b ∘ (F₀ b)⁻¹`,
and likewise the rescaled paths `t ↦ b ((F n b)⁻¹ (m₀ t))` of eq:rescaled-lbm (line 723).

Terminology: positive continuous additive functional (the LQG clock), its right-continuous inverse, and the time
change `𝓑_{F⁻¹(t)}` of planar Brownian motion (Garban-Rhodes-Vargas, *Liouville Brownian motion*, Definition 2.17).
-/

namespace MatedCRT

open Filter Topology Set HarmonicBalls MarkovProcess
open scoped NNReal

/-- Locally uniform convergence of time-change clocks gives locally uniform convergence of their inverses. -/
theorem tendstoLocallyUniformly_clockInverse {A : ℕ → ℝ≥0 → ℝ} {A₀ : ℝ≥0 → ℝ}
    (hA : ∀ n, IsTimeChangeClock (A n)) (hA₀ : IsTimeChangeClock A₀)
    (hconv : TendstoLocallyUniformly A A₀ atTop) :
    TendstoLocallyUniformly (fun n => clockInverse (A n)) (clockInverse A₀) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at hconv ⊢
  intro K hK
  obtain ⟨U, hU⟩ := hK.bddAbove
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have hconv' : ∀ T : ℝ≥0, ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ t ≤ T, |A n t - A₀ t| < δ := by
    intro T δ hδ
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hconv (Icc 0 T) isCompact_Icc) δ hδ] with n hn t ht
    rw [abs_sub_comm, ← Real.dist_eq]
    exact hn t ⟨zero_le, ht⟩
  have hunb : ∀ᶠ n in atTop, ∀ u : ℝ≥0, u ≤ U → ∃ s : ℝ≥0, (u : ℝ) < A n s :=
    Eventually.of_forall fun n u _ =>
      ((hA n).tendsto_atTop.eventually (eventually_gt_atTop (u : ℝ))).exists
  filter_upwards [clockInverse_tendsto_uniform hA₀ (fun n => (hA n).strictMono) U hunb hconv' η hη]
    with n hn t ht
  rw [NNReal.dist_eq, abs_sub_comm]
  exact hn t (hU ht)

/-- Locally uniform convergence of time-change clocks along a fixed Brownian path `b` gives locally uniform
convergence of the time-changed paths `b ∘ (F n b)⁻¹` (Liouville Brownian motion paths). -/
theorem tendstoLocallyUniformly_liouvilleBrownianPath (b : ContinuousPath ℂ)
    {F : ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ} {F₀ : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : ∀ n, IsTimeChangeClock (F n b)) (hF₀ : IsTimeChangeClock (F₀ b))
    (hconv : TendstoLocallyUniformly (fun n => F n b) (F₀ b) atTop) :
    TendstoLocallyUniformly (fun n => liouvilleBrownianPath (F n) b) (liouvilleBrownianPath F₀ b) atTop := by
  have hlim : Tendsto
      (fun n => (⟨clockInverse (F n b), IsTimeChangeClock.continuous_clockInverse (hF n)⟩ : C(ℝ≥0, ℝ≥0)))
      atTop (𝓝 ⟨clockInverse (F₀ b), IsTimeChangeClock.continuous_clockInverse hF₀⟩) := by
    rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly]
    exact tendstoLocallyUniformly_clockInverse hF hF₀ hconv
  have hcomp := ((ContinuousMap.continuous_postcomp (b : C(ℝ≥0, ℂ))).tendsto _).comp hlim
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly] at hcomp
  exact hcomp

/-- Locally uniform convergence of time-change clocks along a fixed Brownian path `b` gives locally uniform
convergence of the rescaled Liouville Brownian motion paths `t ↦ b ((F n b)⁻¹ (m₀ t))` (eq:rescaled-lbm). -/
theorem tendstoLocallyUniformly_rescaledLBMPath (m₀ : ℝ) (b : ContinuousPath ℂ)
    {F : ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ} {F₀ : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : ∀ n, IsTimeChangeClock (F n b)) (hF₀ : IsTimeChangeClock (F₀ b))
    (hconv : TendstoLocallyUniformly (fun n => F n b) (F₀ b) atTop) :
    TendstoLocallyUniformly (fun n => rescaledLBMPath (F n) m₀ b) (rescaledLBMPath F₀ m₀ b) atTop :=
  (tendstoLocallyUniformly_liouvilleBrownianPath b hF hF₀ hconv).comp (fun t : ℝ≥0 => m₀.toNNReal * t)
    (continuous_const.mul continuous_id)

end MatedCRT
