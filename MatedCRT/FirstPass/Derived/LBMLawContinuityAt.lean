import MatedCRT.FirstPass.Derived.LBMApproxLevelLimit
import MatedCRT.FirstPass.Derived.ConeRefApproxClockTail
import LatticeProb.Prob.GaussianShiftTotalVariation

/-!
# Continuity in the starting point of the law of the time-changed path

Let `F` be an LQG clock of planar Brownian motion from every start (`IsLQGClock`) that is almost
surely a time-change clock, with time-changed path map `Φ = lbmContinuousPath F`, for circle
averages continuous at every dyadic radius and satisfying the stopped heat bound
`E^z ∫_0^{t ∧ τ} ε_k^{γ²/2} e^{γ h_{ε_k}(b_s)} ds ≤ C t^β` (`β > 0`) for all starts `|z| ≤ R`.

* `aestronglyMeasurable_lbmContinuousPath_clockValue`: `b ↦ H(Φ b, F(b, δ))` is almost
  everywhere strongly measurable for continuous `H`, as the almost sure limit of the
  approximations along a subsequence.
* `tendsto_integral_min_delayAdvanceBound_zero`: `e*(θ) = E^z min(2, L J_θ(Φ b, F(b, θ))) → 0` as
  `θ → 0`, by dominated convergence.
* `tendsto_integral_lbmContinuousPath_nhds`: for `|z₀| < R` and every `G` bounded by `1` and
  Lipschitz for `dUnif`, `E^z G(Φ b) → E^{z₀} G(Φ b)` as `z → z₀`. The constants are chosen as
  follows: first `θ` with `e*(θ)` small and `a := θ`; then `δ ≤ θ` with the delay terms and the
  clock tails `P^w(A_k(b, δ) > θ)` small uniformly in the level and the start `|w| ≤ R`; then `z`
  close to `z₀` with the total variation distance of the heat kernels `p_δ(z, ·)`, `p_δ(z₀, ·)`
  small (strong Feller property).
-/

open MeasureTheory ProbabilityTheory Set MarkovProcess Filter Topology
open _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

variable {γ : ℝ} {hε : ℝ → ℂ → ℝ}

/-- For a continuous `H`, the map `b ↦ H(Φ b, F(b, δ))` is almost everywhere strongly
measurable: it is the almost sure limit of `H(Φ_k b, A_k(b, δ))` along a subsequence. -/
theorem aestronglyMeasurable_lbmContinuousPath_clockValue {z : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : IsLQGClock planarBrownianMotion γ hε z F)
    (hFc : ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b))
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) (δ : ℝ≥0)
    {H : ContinuousPath ℂ × ℝ → ℝ} (hH : Continuous H) :
    AEStronglyMeasurable (fun b => H (lbmContinuousPath F b, F b δ))
      (planarBrownianMotion z) := by
  obtain ⟨φ, -, hae⟩ := exists_strictMono_ae_forall_eventually_close (planarBrownianMotion z)
    (fun k b t => lqgApproxClockPlus γ hε k b t) F
    (fun T η hη => IsLQGClock.tendsto_measure_lqgApproxClockPlus hF T hη)
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun j b => H (lbmContinuousPath (lqgApproxClockPlus γ hε (φ j)) b,
      lqgApproxClockPlus γ hε (φ j) b δ))
    (fun j => (hH.comp ((continuous_lbmContinuousPath_lqgApproxClockPlus (hcont (φ j))).prodMk
      (continuous_lqgApproxClockPlus_apply (hcont (φ j)) δ))).measurable.aestronglyMeasurable) ?_
  filter_upwards [hae, hFc] with b hb hFb
  refine (hH.tendsto _).comp (Tendsto.prodMk_nhds ?_ ?_)
  · exact tendsto_lbmContinuousPath_of_forall_eventually_close (ns := fun j => φ j) hcont hFb hb
  · exact Metric.tendsto_nhds.2 fun η hη => (hb δ η hη).mono fun j hj => by
      rw [Real.dist_eq]
      exact hj δ le_rfl

/-- **The term `e*(θ)` tends to `0`.** For an LQG clock that is almost surely a time-change clock,
`E^z min(2, L J_θ(Φ b, F(b, θ))) → 0` as `θ → 0`, by dominated convergence: `J_θ(y, c)` is jointly
continuous and vanishes at `θ = c = 0`, and `F(b, θ) → F(b, 0) = 0`. -/
theorem tendsto_integral_min_delayAdvanceBound_zero {z : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : IsLQGClock planarBrownianMotion γ hε z F)
    (hFc : ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b))
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) {L : ℝ} (hL : 0 ≤ L) :
    Tendsto (fun θ : ℝ≥0 => ∫ b, min 2 (L * delayAdvanceBound θ (lbmContinuousPath F b, F b θ))
      ∂planarBrownianMotion z) (𝓝 0) (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := planarBrownianMotion z)
    (l := 𝓝 (0 : ℝ≥0)) (f := fun _ => (0 : ℝ)) (fun _ => (2 : ℝ))
    (Eventually.of_forall fun θ => aestronglyMeasurable_lbmContinuousPath_clockValue hF hFc
      hcont θ (H := fun p => min 2 (L * delayAdvanceBound θ p))
      (continuous_const.min (continuous_const.mul (continuous_delayAdvanceBound θ))))
    (Eventually.of_forall fun θ => ae_of_all _ fun b => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_two
        (mul_nonneg hL (delayAdvanceBound_nonneg _ _)))]
      exact min_le_left _ _)
    (integrable_const _) ?_
  · simpa only [integral_zero] using h
  filter_upwards [hFc] with b hb
  set y := lbmContinuousPath F b
  have hd : Continuous fun a : ℝ≥0 => LatticeProb.delayModulus a y :=
    LatticeProb.continuous_delayModulus.comp (continuous_id.prodMk continuous_const)
  have ha : Continuous fun c : ℝ≥0 => LatticeProb.advanceModulus c y :=
    LatticeProb.continuous_advanceModulus.comp (continuous_id.prodMk continuous_const)
  have hd0 : LatticeProb.delayModulus 0 y = 0 :=
    tendsto_nhds_unique (hd.tendsto 0) (LatticeProb.tendsto_delayModulus_zero y)
  have ha0 : LatticeProb.advanceModulus 0 y = 0 :=
    tendsto_nhds_unique (ha.tendsto 0) (LatticeProb.tendsto_advanceModulus_zero y)
  have hc : Continuous fun θ : ℝ≥0 => min 2 (L * delayAdvanceBound θ (y, F b θ)) :=
    continuous_const.min (continuous_const.mul (hd.add (continuous_const.mul
      (ha.comp (continuous_real_toNNReal.comp hb.continuous)))))
  have h0 : min 2 (L * delayAdvanceBound 0 (y, F b 0)) = 0 := by
    simp only [delayAdvanceBound, hb.map_zero, Real.toNNReal_zero, hd0, ha0, mul_zero, add_zero]
    exact min_eq_right zero_le_two
  simpa only [h0] using hc.tendsto 0

/-- Monotonicity in the restart time: for `δ ≤ θ`,
`E^z min(2, L J_θ(Φ b, F(b, δ))) ≤ E^z min(2, L J_θ(Φ b, F(b, θ)))`. -/
theorem integral_min_delayAdvanceBound_le_of_le {z : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : IsLQGClock planarBrownianMotion γ hε z F)
    (hFc : ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b))
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) {L : ℝ} (hL : 0 ≤ L) {δ θ : ℝ≥0}
    (hδθ : δ ≤ θ) :
    ∫ b, min 2 (L * delayAdvanceBound θ (lbmContinuousPath F b, F b δ))
        ∂planarBrownianMotion z ≤
      ∫ b, min 2 (L * delayAdvanceBound θ (lbmContinuousPath F b, F b θ))
        ∂planarBrownianMotion z := by
  have hJc : Continuous fun p : ContinuousPath ℂ × ℝ => min 2 (L * delayAdvanceBound θ p) :=
    continuous_const.min (continuous_const.mul (continuous_delayAdvanceBound θ))
  have hJb : ∀ p : ContinuousPath ℂ × ℝ, ‖min 2 (L * delayAdvanceBound θ p)‖ ≤ 2 := fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_two
      (mul_nonneg hL (delayAdvanceBound_nonneg θ p)))]
    exact min_le_left _ _
  refine integral_mono_ae
    (Integrable.of_bound (aestronglyMeasurable_lbmContinuousPath_clockValue hF hFc hcont δ hJc) 2
      (ae_of_all _ fun b => hJb _))
    (Integrable.of_bound (aestronglyMeasurable_lbmContinuousPath_clockValue hF hFc hcont θ hJc) 2
      (ae_of_all _ fun b => hJb _)) ?_
  filter_upwards [hFc] with b hb
  refine min_le_min_left _ (mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (LatticeProb.advanceModulus_mono
      (Real.toNNReal_le_toNNReal (hb.strictMono.monotone hδθ)) _) zero_le_two)) hL)

/-- **Continuity in the starting point (weak form).** Let `F` be an LQG clock of planar Brownian
motion from every start that is almost surely a time-change clock, for circle averages continuous
at every dyadic radius and satisfying the stopped heat bound with exponent `β > 0` for all starts
`|z| ≤ R`. Let `G` be continuous, bounded by `1` and `L`-Lipschitz for `dUnif`. Then for
`|z₀| < R`, `E^z G(Φ b) → E^{z₀} G(Φ b)` as `z → z₀`. -/
theorem tendsto_integral_lbmContinuousPath_nhds {z0 : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : ∀ z, IsLQGClock planarBrownianMotion γ hε z F)
    (hFc : ∀ z, ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b))
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) {R β C : ℝ} (hR : ‖z0‖ < R)
    (hβ : 0 < β)
    (hheat : ∀ z : ℂ, ‖z‖ ≤ R → ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t →
      ∫⁻ b, (∫⁻ s in Ioc 0 (min t (ContinuousPath.exitTime (Metric.ball (0 : ℂ) (R + 1)) b).toReal),
          ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
            Real.exp (γ * hε (LatticeProb.LQG.dyadicScale k) (b s.toNNReal))))
        ∂(planarBrownianMotion z) ≤ ENNReal.ofReal (C * t ^ β))
    {G : ContinuousPath ℂ → ℝ} (hGc : Continuous G) (hG1 : ∀ x, |G x| ≤ 1) {L : ℝ} (hL : 0 ≤ L)
    (hGL : ∀ x y, |G x - G y| ≤ L * LatticeProb.dUnif x y) :
    Tendsto (fun z => ∫ b, G (lbmContinuousPath F b) ∂planarBrownianMotion z) (𝓝 z0)
      (𝓝 (∫ b, G (lbmContinuousPath F b) ∂planarBrownianMotion z0)) := by
  refine Metric.tendsto_nhds.2 fun ε hε0 => ?_
  set e : ℝ := ε / 8 with he
  have hepos : 0 < e := by positivity
  -- the scale `θ = a` with `e*(θ) ≤ e / 2`
  obtain ⟨θ, hθe, hθ0⟩ := (((tendsto_integral_min_delayAdvanceBound_zero (hF z0) (hFc z0) hcont
    hL).eventually (ge_mem_nhds (half_pos hepos))).filter_mono nhdsWithin_le_nhds |>.and
    (self_mem_nhdsWithin : Ioi (0 : ℝ≥0) ∈ 𝓝[>] 0)).exists
  have hθ0' : 0 < θ := hθ0
  -- the restart time `δ ≤ θ`
  have hm := eventually_integral_min_dUnif_lbmContinuousPath_lqgApproxClockPlus_delay_le
    (γ := γ) (hε := hε) hL hepos
  have hP := eventually_planarBrownianMotion_lt_lqgApproxClockPlus_le hβ hheat hθ0'
    (ENNReal.ofReal_pos.2 (half_pos hepos))
  have hδθ : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), δ < θ :=
    eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hθ0')
  obtain ⟨δ, ⟨⟨hδm, hδP⟩, hδθ⟩, hδ0⟩ :=
    (((hm.and hP).and hδθ).and (self_mem_nhdsWithin : Ioi (0 : ℝ≥0) ∈ 𝓝[>] 0)).exists
  have hδ0' : δ ≠ 0 := (show 0 < δ from hδ0).ne'
  -- the start `z` close to `z₀`
  have hTV := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (LatticeProb.tendsto_tvDist_complexGaussian z0 hδ0')
  have hzR : ∀ᶠ z in 𝓝 z0, ‖z‖ < R := (continuous_norm.tendsto z0).eventually (gt_mem_nhds hR)
  filter_upwards [hTV.eventually (gt_mem_nhds (by positivity : (0 : ℝ≥0∞).toReal < e / 4)), hzR]
    with z hzTV hz
  have hTV' : (QuantumZipper.TV.tvDist (planarHeatSemigroup δ z)
      (planarHeatSemigroup δ z0)).toReal < e / 4 := by
    simpa only [planarHeatSemigroup_apply, planarGaussian, Function.comp_apply] using hzTV
  have hPw : ∀ k, ∀ w : ℂ, ‖w‖ ≤ R →
      (planarBrownianMotion w {b | (θ : ℝ) < lqgApproxClockPlus γ hε k b δ}).toReal ≤ e / 2 :=
    fun k w hw => by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hδP k (hcont k) w hw)
      rwa [ENNReal.toReal_ofReal (half_pos hepos).le] at this
  have hbound := abs_integral_sub_integral_lbmContinuousPath_le_of_eventually_le (hF z) (hF z0)
    (hFc z) (hFc z0) hcont hGc hG1 hL hGL (δ := δ) (a := θ) (B := 4 * e)
    (Eventually.of_forall fun n => by
      have h1 := hδm n (hcont n) z
      have h2 := hδm n (hcont n) z0
      have h3 := hPw n z hz.le
      have h4 := hPw n z0 hR.le
      linarith)
  have hmono := integral_min_delayAdvanceBound_le_of_le (hF z0) (hFc z0) hcont hL hδθ.le
  rw [Real.dist_eq]
  linarith

end MatedCRT.FirstPass.Derived
