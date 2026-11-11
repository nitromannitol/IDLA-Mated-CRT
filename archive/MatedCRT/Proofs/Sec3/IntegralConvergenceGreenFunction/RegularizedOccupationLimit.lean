import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ClockInverseConvergence
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxClockOccupation

/-! # Limits of regularized clock occupation integrals -/

namespace MatedCRT

open Filter HarmonicBalls Topology MeasureTheory MarkovProcess
open scoped NNReal

/-- Bounded continuous integrands permit a convergent upper endpoint to move
through an interval-integral limit, uniformly in the integrand index. -/
theorem tendsto_intervalIntegral_moving_endpoint
    {ι : Type*} {l : Filter ι} {φ : ι → ℝ → ℝ} {v : ι → ℝ} {U L C : ℝ}
    (hcont : ∀ i, Continuous (φ i)) (hbound : ∀ i s, ‖φ i s‖ ≤ C)
    (hv : Tendsto v l (𝓝 U))
    (hfixed : Tendsto (fun i => ∫ s in (0 : ℝ)..U, φ i s) l (𝓝 L)) :
    Tendsto (fun i => ∫ s in (0 : ℝ)..v i, φ i s) l (𝓝 L) := by
  have hsmall : Tendsto (fun i => ∫ s in U..v i, φ i s) l (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun i => C * |v i - U|) l (𝓝 0) by
      have hvzero : Tendsto (fun i => v i - U) l (𝓝 0) := by
        simpa using hv.sub (tendsto_const_nhds : Tendsto (fun _ : ι => U) l (𝓝 U))
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ι => C) l (𝓝 C)).mul hvzero.abs)
    exact Filter.Eventually.of_forall fun i =>
      intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => hbound i s)
  have hadd := hfixed.add hsmall
  have heq : (fun i => (∫ s in (0 : ℝ)..U, φ i s) + ∫ s in U..v i, φ i s) =
      (fun i => ∫ s in (0 : ℝ)..v i, φ i s) := by
    funext i
    exact intervalIntegral.integral_add_adjacent_intervals
      ((hcont i).intervalIntegrable _ _) ((hcont i).intervalIntegrable _ _)
  simpa only [heq, add_zero] using hadd

/-- Pointwise convergence of circle-average clocks implies convergence of
their weighted Brownian occupation integrals on every finite time interval. -/
theorem tendsto_lqgClockApprox_weighted_occupation
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (γ : ℝ) (ε : ι → ℝ) (hε : ℝ → ℂ → ℝ) (b : ContinuousPath ℂ)
    (hεpos : ∀ i, 0 < ε i) (hfield : ∀ i, Continuous (hε (ε i)))
    (G : ℝ≥0 → ℝ) (hGzero : G 0 = 0) (hGcont : Continuous G)
    (hGmono : StrictMono G)
    (hconv : ∀ t, Tendsto (fun i => lqgClockApprox γ hε (ε i) b t) l (𝓝 (G t)))
    (T : ℝ≥0) (f : ℂ → ℝ) (hf : Continuous f) (C : ℝ)
    (hbound : ∀ z, ‖f z‖ ≤ C) :
    Tendsto (fun i => ∫ t in (0 : ℝ)..(T : ℝ), f (b t.toNNReal) *
      ((ε i) ^ (γ ^ 2 / 2) * Real.exp (γ * hε (ε i) (b t.toNNReal)))) l
      (𝓝 (∫ s in (0 : ℝ)..G T, f (b (clockInverse G s.toNNReal)))) := by
  let F : ι → ℝ≥0 → ℝ := fun i => lqgClockApprox γ hε (ε i) b
  let H : ι → ℝ≥0 → ℝ := fun i => stoppedClockExtension (F i) T
  let K : ℝ≥0 → ℝ := stoppedClockExtension G T
  have hz : ∀ i, F i 0 = 0 := by
    intro i
    simp [F, lqgClockApprox]
  have hc : ∀ i, Continuous (F i) := fun i =>
    lqgClockApprox_continuous γ (ε i) hε b (hfield i)
  have hm : ∀ i, StrictMono (F i) := fun i =>
    lqgClockApprox_strictMono γ (ε i) hε b (hεpos i) (hfield i)
  have hH : ∀ i, IsTimeChangeClock (H i) := fun i =>
    stoppedClockExtension_isTimeChangeClock T (hz i) (hc i) (hm i)
  have hK : IsTimeChangeClock K := stoppedClockExtension_isTimeChangeClock T hGzero hGcont hGmono
  have hext : ∀ t, Tendsto (fun i => H i t) l (𝓝 (K t)) := by
    intro t
    simpa [H, K, F, stoppedClockExtension] using
      (hconv (min t T)).add_const (max ((t : ℝ) - T) 0)
  have hfixed := tendsto_clockInverse_occupation hH hK hext b f hf C hbound (G T)
  have hφcont : ∀ i, Continuous (fun s : ℝ => f (b (clockInverse (H i) s.toNNReal))) := by
    intro i
    exact hf.comp (b.continuous.comp ((IsTimeChangeClock.continuous_clockInverse (hH i)).comp continuous_real_toNNReal))
  have hconvT : Tendsto (fun i => F i T) l (𝓝 (G T)) := hconv T
  have hmoving := tendsto_intervalIntegral_moving_endpoint hφcont (fun _ s => hbound _) hconvT hfixed
  have hnonneg : 0 ≤ G T := by
    simpa [hGzero] using hGmono.monotone (show (0 : ℝ≥0) ≤ T from bot_le)
  have hlimit : (∫ s in (0 : ℝ)..G T, f (b (clockInverse K s.toNNReal))) =
      ∫ s in (0 : ℝ)..G T, f (b (clockInverse G s.toNNReal)) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hnonneg]
    intro s hs
    have hs' : (s.toNNReal : ℝ) ≤ G T := by simpa [Real.coe_toNNReal _ hs.1] using hs.2
    dsimp only [K]
    rw [stoppedClockExtension_inverse_eq hGzero hGcont hGmono hs']
  have hleft : ∀ i, (∫ s in (0 : ℝ)..F i T, f (b (clockInverse (H i) s.toNNReal))) =
      ∫ t in (0 : ℝ)..(T : ℝ), f (b t.toNNReal) *
        ((ε i) ^ (γ ^ 2 / 2) * Real.exp (γ * hε (ε i) (b t.toNNReal))) := by
    intro i
    have hFnonneg : 0 ≤ F i T := by
      simpa [hz i] using (hm i).monotone (show (0 : ℝ≥0) ≤ T from bot_le)
    have heq : (∫ s in (0 : ℝ)..F i T, f (b (clockInverse (H i) s.toNNReal))) =
        ∫ s in (0 : ℝ)..F i T, f (b (clockInverse (F i) s.toNNReal)) := by
      apply intervalIntegral.integral_congr
      rw [Set.uIcc_of_le hFnonneg]
      intro s hs
      have hs' : (s.toNNReal : ℝ) ≤ F i T := by simpa [Real.coe_toNNReal _ hs.1] using hs.2
      dsimp only [H]
      rw [stoppedClockExtension_inverse_eq (hz i) (hc i) (hm i) hs']
    rw [heq]
    exact (lqgClockApprox_occupation_substitution_local γ (ε i) hε b
      (hεpos i) (hfield i) T f hf).symm
  simpa only [hleft, hlimit] using hmoving

end MatedCRT
