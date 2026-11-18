import MatedCRT.FirstPass.Derived.LBMApproxClockTail
import MatedCRT.FirstPass.Derived.ConeReferenceStoppedHeatBound

/-!
# Uniform small-time tail of the approximating LQG clock of the reference cone

Let `A_k = lqgApproxClockPlus γ hε k` be the approximating LQG clock with drift at the dyadic scale
`2^{-k}`.

* `harmonicBalls_dyadicScale_eq`: the two spellings of the dyadic scale `2^{-k}` agree.
* `eventually_planarBrownianMotion_lt_lqgApproxClockPlus_le`: if the stopped heat bound
  `E^z ∫_0^{t ∧ τ_{B(0,R+1)}} ε_k^{γ²/2} e^{γ h_{ε_k}(b_s)} ds ≤ C t^β` (`β > 0`) holds for all
  starts `|z| ≤ R`, all levels `k` and all `t ≥ 0`, then for `a > 0` and `ε > 0`, for all small
  `δ > 0`, `P^w(A_k(b, δ) > a) ≤ ε` for every level `k` and every start `|w| ≤ R`.
* `ae_coneRef_eventually_planarBrownianMotion_lt_lqgApproxClockPlus_le`: almost surely this holds for
  the circle averages of the reference cone, by the stopped heat bound for its approximants.

This is the clock tail term in the comparison of the laws of the approximate Liouville Brownian
paths from two starting points through the restart at a fixed small time (Garban–Rhodes–Vargas,
*Liouville Brownian motion*, Ann. Probab. 44 (2016), proof of Proposition 2.19).
-/

open MeasureTheory ProbabilityTheory Set HarmonicBalls LQGMetric MarkovProcess
open Filter Topology Metric
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- The dyadic scale `2^{-k}` of the Harmonic-Balls definitions is that of the Lattice-Probability
LQG measure. -/
theorem harmonicBalls_dyadicScale_eq (k : ℕ) :
    HarmonicBalls.dyadicScale k = LatticeProb.LQG.dyadicScale k := by
  unfold HarmonicBalls.dyadicScale LatticeProb.LQG.dyadicScale
  simp

/-- **Uniform small-time tail of the approximating clock.** Under the stopped heat bound with
exponent `β > 0` for all starts `|z| ≤ R`, levels `k` and times `t ≥ 0`, for `a > 0` and `ε > 0`,
for all small `δ > 0`: `P^w(A_k(b, δ) > a) ≤ ε` for every level `k` with continuous circle averages
at the scale `2^{-k}` and every start `|w| ≤ R`. -/
theorem eventually_planarBrownianMotion_lt_lqgApproxClockPlus_le
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {R β C : ℝ} (hβ : 0 < β)
    (hheat : ∀ z : ℂ, ‖z‖ ≤ R → ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t →
      ∫⁻ b, (∫⁻ s in Ioc 0 (min t (ContinuousPath.exitTime (ball (0 : ℂ) (R + 1)) b).toReal),
          ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
            Real.exp (γ * hε (LatticeProb.LQG.dyadicScale k) (b s.toNNReal))))
        ∂(planarBrownianMotion z) ≤ ENNReal.ofReal (C * t ^ β))
    {a : ℝ≥0} (ha : 0 < a) {ε : ℝ≥0∞} (hεpos : 0 < ε) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), ∀ k : ℕ, Continuous (hε (dyadicScale k)) → ∀ w : ℂ, ‖w‖ ≤ R →
      planarBrownianMotion w {b | (a : ℝ) < lqgApproxClockPlus γ hε k b δ} ≤ ε := by
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hεpos.ne'
  -- the exit probability of the unit disc by time `δ` is small
  have h1 := tendsto_planarBrownianMotion_exitTime_unitBall_le.eventually (gt_mem_nhds hε2)
  -- the heat term `2 C δ^β / a` is small
  have hcontδ : Continuous fun δ : ℝ≥0 => ENNReal.ofReal (2 * C * (δ : ℝ) ^ β / a) :=
    ENNReal.continuous_ofReal.comp (((continuous_const.mul
      ((Real.continuous_rpow_const hβ.le).comp NNReal.continuous_coe))).div_const _)
  have ht : Tendsto (fun δ : ℝ≥0 => ENNReal.ofReal (2 * C * (δ : ℝ) ^ β / a)) (𝓝 0) (𝓝 0) := by
    convert hcontδ.tendsto 0 using 2
    simp [Real.zero_rpow hβ.ne']
  have h2 : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0, ENNReal.ofReal (2 * C * (δ : ℝ) ^ β / a) < ε / 2 :=
    (tendsto_nhdsWithin_of_tendsto_nhds ht).eventually (gt_mem_nhds hε2)
  -- eventually `2 δ ≤ a`
  have h3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), δ < a / 2 :=
    eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (half_pos ha))
  filter_upwards [h1, h2, h3] with δ hδ1 hδ2 hδ3 k hcont w hw
  have hδa : 2 * δ ≤ a := by
    have := mul_lt_mul_of_pos_left hδ3 (by norm_num : (0 : ℝ≥0) < 2)
    rw [mul_div_cancel₀ _ (two_ne_zero)] at this
    exact this.le
  have hb := hheat w hw k δ δ.2
  rw [← harmonicBalls_dyadicScale_eq] at hb
  refine (planarBrownianMotion_lt_lqgApproxClockPlus_le hcont hw ha hδa hb).trans ?_
  calc _ ≤ ε / 2 + ε / 2 := add_le_add hδ1.le hδ2.le
    _ = ε := ENNReal.add_halves ε

/-- **Uniform small-time tail of the approximating clock of the reference cone.** Almost surely,
for every `R > 0`, `a > 0` and `ε > 0`, for all small `δ > 0`, `P^w(A_k(b, δ) > a) ≤ ε` for every
level `k` with continuous circle averages at the scale `2^{-k}` and every start `|w| ≤ R`, where
`A_k` is the approximating clock of the circle averages of the reference cone. -/
theorem ae_coneRef_eventually_planarBrownianMotion_lt_lqgApproxClockPlus_le
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {hC : DistC → (ℂ → ℝ) → ℝ} {c : DistC → ℝ → ℂ → ℝ}
    (hp : ∀ x (φ : TestC), hC x φ = x φ)
    (hc : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2))
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : Ω → ContinuousPath ℝ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ a : ℝ≥0, 0 < a → ∀ ε : ℝ≥0∞, 0 < ε →
      ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), ∀ k : ℕ,
        Continuous (coneRefCircle γ (c (Y ω)) (w ω) (dyadicScale k)) → ∀ z : ℂ, ‖z‖ ≤ R →
          planarBrownianMotion z
            {b | (a : ℝ) < lqgApproxClockPlus γ (coneRefCircle γ (c (Y ω)) (w ω)) k b δ} ≤ ε := by
  filter_upwards [ae_coneRef_stopped_heat_bound hY hp hc hcont hmeas hγ hγ2 w]
    with ω hω R hR a ha ε hεpos
  obtain ⟨β, C, hβ, -, hb⟩ := hω R hR
  exact eventually_planarBrownianMotion_lt_lqgApproxClockPlus_le hβ hb ha hεpos

end MatedCRT.FirstPass.Derived
