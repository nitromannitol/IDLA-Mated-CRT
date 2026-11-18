import MatedCRT.FirstPass.Derived.LBMApproxLevelEstimate
import LatticeProb.Prob.PathDelayModulus

/-!
# The level-`k` estimate in the limit `k → ∞`

Let `A_k = lqgApproxClockPlus γ hε k`, `Φ_k = lbmContinuousPath A_k`, and let `F` be an LQG clock
of planar Brownian motion (`IsLQGClock`) that is almost surely a time-change clock, with time-changed
path map `Φ = lbmContinuousPath F`. The approximate path of the path restarted at time `δ` is the
approximate path advanced by the clock value: `Φ_k(θ_δ b) = Φ_k(b)(A_k(b, δ) + ·)`. Hence its delay
modulus at level `a` is at most `J_a(Φ_k b, A_k(b, δ))`, where
`J_a(y, c) = delayModulus a y + 2 · advanceModulus c y` is jointly continuous. Passing to the limit
in the level-`k` estimate with the joint convergence of `(Φ_k b, A_k(b, δ))` gives:

* `abs_integral_sub_integral_lbmContinuousPath_le_of_eventually_le`: if the delay and clock-tail
  terms of the level-`k` estimate are eventually at most `B`, then
  `|E^z G(Φ b) - E^{z₀} G(Φ b)| ≤ B + 2 E^{z₀} min(2, L J_a(Φ b, F(b, δ))) + 4 TV(p_δ(z, ·), p_δ(z₀, ·))`.
-/

open MeasureTheory ProbabilityTheory Set MarkovProcess Filter Topology
open _root_.HarmonicBalls
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

variable {γ : ℝ} {hε : ℝ → ℂ → ℝ} {n : ℕ}

/-- **The restarted approximate path is the advanced approximate path.** For circle averages
continuous at the scale `2^{-n}`, `Φ_n(θ_δ b) = Φ_n(b)(A_n(b, δ) + ·)`. -/
theorem lbmContinuousPath_lqgApproxClockPlus_shift_eq_pathShift
    (hcont : Continuous (hε (dyadicScale n))) (b : ContinuousPath ℂ) (δ : ℝ≥0) :
    lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b) =
      LatticeProb.pathShift (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)
        (lqgApproxClockPlus γ hε n b δ).toNNReal := by
  ext u
  rw [LatticeProb.pathShift_apply]
  exact (lbmContinuousPath_lqgApproxClockPlus_clockValue_add hcont b δ u).symm

/-- The bound `J_a(y, c) = delayModulus a y + 2 · advanceModulus c⁺ y` for the delay modulus of an
advanced path. -/
noncomputable def delayAdvanceBound (a : ℝ≥0) (p : ContinuousPath ℂ × ℝ) : ℝ :=
  LatticeProb.delayModulus a p.1 + 2 * LatticeProb.advanceModulus p.2.toNNReal p.1

theorem delayAdvanceBound_nonneg (a : ℝ≥0) (p : ContinuousPath ℂ × ℝ) :
    0 ≤ delayAdvanceBound a p :=
  add_nonneg (LatticeProb.delayModulus_nonneg _ _)
    (mul_nonneg zero_le_two (LatticeProb.advanceModulus_nonneg _ _))

theorem continuous_delayAdvanceBound (a : ℝ≥0) : Continuous (delayAdvanceBound a) :=
  (LatticeProb.continuous_delayModulus.comp (continuous_const.prodMk continuous_fst)).add
    (continuous_const.mul (LatticeProb.continuous_advanceModulus.comp
      ((continuous_real_toNNReal.comp continuous_snd).prodMk continuous_fst)))

/-- The delay modulus of the restarted approximate path is at most `J_a(Φ_n b, A_n(b, δ))`. -/
theorem delayModulus_lbmContinuousPath_lqgApproxClockPlus_shift_le
    (hcont : Continuous (hε (dyadicScale n))) (b : ContinuousPath ℂ) (δ a : ℝ≥0) :
    LatticeProb.delayModulus a
        (lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b)) ≤
      delayAdvanceBound a (lbmContinuousPath (lqgApproxClockPlus γ hε n) b,
        lqgApproxClockPlus γ hε n b δ) := by
  rw [lbmContinuousPath_lqgApproxClockPlus_shift_eq_pathShift hcont]
  exact LatticeProb.delayModulus_pathShift_le a _ _

/-- **The level-`k` estimate in the limit.** Let `F` be an LQG clock of planar Brownian motion from
`z` and from `z₀`, almost surely a time-change clock under both, for circle averages continuous at
every dyadic scale. Let `G` be continuous, bounded by `1` and `L`-Lipschitz for `dUnif`. If the
delay terms `m_n(z) + m_n(z₀)` plus the clock tails `2 P^z(A_n(b, δ) > a) + 2 P^{z₀}(A_n(b, δ) > a)`
are eventually at most `B`, then
`|E^z G(Φ b) - E^{z₀} G(Φ b)| ≤ B + 2 E^{z₀} min(2, L J_a(Φ b, F(b, δ))) + 4 TV(p_δ(z, ·), p_δ(z₀, ·))`. -/
theorem abs_integral_sub_integral_lbmContinuousPath_le_of_eventually_le {z z0 : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hFz : IsLQGClock planarBrownianMotion γ hε z F)
    (hFz0 : IsLQGClock planarBrownianMotion γ hε z0 F)
    (hFcz : ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b))
    (hFcz0 : ∀ᵐ b ∂planarBrownianMotion z0, IsTimeChangeClock (F b))
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) {G : ContinuousPath ℂ → ℝ}
    (hGc : Continuous G) (hG1 : ∀ x, |G x| ≤ 1) {L : ℝ} (hL : 0 ≤ L)
    (hGL : ∀ x y, |G x - G y| ≤ L * LatticeProb.dUnif x y) {δ a : ℝ≥0} {B : ℝ}
    (hB : ∀ᶠ n in atTop,
      ∫ b, min 2 (L * LatticeProb.dUnif (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)
          (continuousPathDelay (lqgApproxClockPlus γ hε n b δ).toNNReal
            (lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b))))
          ∂planarBrownianMotion z +
        ∫ b, min 2 (L * LatticeProb.dUnif (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)
          (continuousPathDelay (lqgApproxClockPlus γ hε n b δ).toNNReal
            (lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b))))
          ∂planarBrownianMotion z0 +
        2 * (planarBrownianMotion z
          {b | (a : ℝ) < lqgApproxClockPlus γ hε n b δ}).toReal +
        2 * (planarBrownianMotion z0
          {b | (a : ℝ) < lqgApproxClockPlus γ hε n b δ}).toReal ≤ B) :
    |∫ b, G (lbmContinuousPath F b) ∂planarBrownianMotion z -
        ∫ b, G (lbmContinuousPath F b) ∂planarBrownianMotion z0| ≤
      B + 2 * ∫ b, min 2 (L * delayAdvanceBound a (lbmContinuousPath F b, F b δ))
          ∂planarBrownianMotion z0 +
        4 * (QuantumZipper.TV.tvDist (planarHeatSemigroup δ z)
          (planarHeatSemigroup δ z0)).toReal := by
  have hJc : Continuous fun p : ContinuousPath ℂ × ℝ => min 2 (L * delayAdvanceBound a p) :=
    continuous_const.min (continuous_const.mul (continuous_delayAdvanceBound a))
  have hJb : ∀ p : ContinuousPath ℂ × ℝ, ‖min 2 (L * delayAdvanceBound a p)‖ ≤ 2 := fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_two
      (mul_nonneg hL (delayAdvanceBound_nonneg a p)))]
    exact min_le_left _ _
  let H1 : ContinuousPath ℂ × ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => G p.1) (hGc.comp continuous_fst) 1 fun p => by
      rw [Real.norm_eq_abs]; exact hG1 _
  let H2 : ContinuousPath ℂ × ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => min 2 (L * delayAdvanceBound a p)) hJc 2 hJb
  have t1 : Tendsto (fun n : ℕ => ∫ b, G (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)
      ∂planarBrownianMotion z) atTop (𝓝 (∫ b, G (lbmContinuousPath F b) ∂planarBrownianMotion z)) :=
    tendsto_integral_lbmContinuousPath_clockValue_lqgApproxClockPlus hFz hFcz hcont δ H1
  have t2 : Tendsto (fun n : ℕ => ∫ b, G (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)
      ∂planarBrownianMotion z0) atTop
      (𝓝 (∫ b, G (lbmContinuousPath F b) ∂planarBrownianMotion z0)) :=
    tendsto_integral_lbmContinuousPath_clockValue_lqgApproxClockPlus hFz0 hFcz0 hcont δ H1
  have t3 : Tendsto (fun n : ℕ => ∫ b, min 2 (L * delayAdvanceBound a
        (lbmContinuousPath (lqgApproxClockPlus γ hε n) b, lqgApproxClockPlus γ hε n b δ))
      ∂planarBrownianMotion z0) atTop
      (𝓝 (∫ b, min 2 (L * delayAdvanceBound a (lbmContinuousPath F b, F b δ))
        ∂planarBrownianMotion z0)) :=
    tendsto_integral_lbmContinuousPath_clockValue_lqgApproxClockPlus hFz0 hFcz0 hcont δ H2
  refine le_of_tendsto_of_tendsto ((t1.sub t2).abs)
    (((t3.const_mul 2).const_add B).add_const (4 * (QuantumZipper.TV.tvDist
      (planarHeatSemigroup δ z) (planarHeatSemigroup δ z0)).toReal)) ?_
  filter_upwards [hB] with n hn
  have hψm : Measurable (LatticeProb.delayModulus a : ContinuousPath ℂ → ℝ) :=
    (LatticeProb.continuous_delayModulus.comp (continuous_const.prodMk continuous_id)).measurable
  have hM7 := abs_integral_sub_integral_lbmContinuousPath_lqgApproxClockPlus_le (hcont n)
    hGc.measurable hG1 hL hGL hψm (γ := γ) (δ := δ) (a := a)
    (fun y s hs => LatticeProb.dUnif_pathDelay_le_delayModulus hs y) z z0
  -- the delay-modulus term is dominated by the `J_a` term
  have hΦ : Continuous (lbmContinuousPath (lqgApproxClockPlus γ hε n)) :=
    continuous_lbmContinuousPath_lqgApproxClockPlus (hcont n)
  have hJn : Continuous fun b : ContinuousPath ℂ => min 2 (L * delayAdvanceBound a
      (lbmContinuousPath (lqgApproxClockPlus γ hε n) b, lqgApproxClockPlus γ hε n b δ)) :=
    hJc.comp (hΦ.prodMk (continuous_lqgApproxClockPlus_apply (hcont n) δ))
  have hdom : ∫ b, min 2 (L * LatticeProb.delayModulus a
        (lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b)))
        ∂planarBrownianMotion z0 ≤
      ∫ b, min 2 (L * delayAdvanceBound a
        (lbmContinuousPath (lqgApproxClockPlus γ hε n) b, lqgApproxClockPlus γ hε n b δ))
        ∂planarBrownianMotion z0 := by
    refine integral_mono_of_nonneg (ae_of_all _ fun b => le_min zero_le_two
      (mul_nonneg hL (LatticeProb.delayModulus_nonneg _ _)))
      (Integrable.of_bound hJn.measurable.aestronglyMeasurable 2
        (ae_of_all _ fun b => hJb _)) (ae_of_all _ fun b => ?_)
    exact min_le_min_left _ (mul_le_mul_of_nonneg_left
      (delayModulus_lbmContinuousPath_lqgApproxClockPlus_shift_le (hcont n) b δ a) hL)
  linarith

end MatedCRT.FirstPass.Derived
