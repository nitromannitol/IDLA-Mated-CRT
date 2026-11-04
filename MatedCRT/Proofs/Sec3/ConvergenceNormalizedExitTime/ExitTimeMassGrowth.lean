import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ExitTimeMassBound
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Geometry
import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-! Almost-sure small-scale mass growth from the exit-time estimate. -/

namespace MatedCRT

open Set Metric MeasureTheory HarmonicBalls Filter Topology
open scoped ENNReal

/-- A dyadic power bound on all small-ball masses implies an all-scales
bound with any smaller positive exponent. -/
theorem smallBallMass_of_eventual_dyadic
    (μ : Measure ℂ) {ρ q β : ℝ} (hβ : 0 < β) (hβq : β < q)
    (N : ℕ) (hN : ∀ n : ℕ, N ≤ n → ∀ x ∈ ball (0 : ℂ) ρ,
      μ (ball x ((1 / 2 : ℝ) ^ n)) ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ q)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ x ∈ ball (0 : ℂ) ρ,
      μ (ball x r) ≤ ENNReal.ofReal (r ^ β) := by
  have hpow := eventually_mul_rpow_le ((2 : ℝ) ^ q) (a := q) (b := β) hβq
  obtain ⟨s, hs, hsbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hpow
  let r₀ := min s (((1 / 2 : ℝ) ^ N) / 2)
  have hr₀ : 0 < r₀ := lt_min hs (by positivity)
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr hrr x hx
  have hrs : r < s := hrr.trans_le (min_le_left _ _)
  have hrN : 2 * r < (1 / 2 : ℝ) ^ N := by
    have h := hrr.trans_le (min_le_right _ _)
    linarith
  have hN1 : (1 / 2 : ℝ) ^ N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨n, hnlo, hnhi⟩ := ConstantOrderDiv.exists_half_pow_mem (by positivity : 0 < 2 * r)
    (by linarith)
  have hnN : N ≤ n := by
    by_contra hn
    have hnlt : n < N := by omega
    have hle := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hnlt.le
    linarith
  have hlarge : r ≤ (1 / 2 : ℝ) ^ n := by linarith
  have hq : 0 ≤ q := (hβ.le.trans hβq.le)
  calc
    μ (ball x r) ≤ μ (ball x ((1 / 2 : ℝ) ^ n)) := measure_mono (ball_subset_ball hlarge)
    _ ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ q) := hN n hnN x hx
    _ ≤ ENNReal.ofReal ((2 * r) ^ q) := ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (by positivity) hnhi hq)
    _ = ENNReal.ofReal (((2 : ℝ) ^ q) * r ^ q) := by rw [Real.mul_rpow (by norm_num) hr.le]
    _ ≤ ENNReal.ofReal (r ^ β) := ENNReal.ofReal_le_ofReal (hsbound ⟨hr, hrs⟩)

/-- Lemma 2.17 gives an almost-sure upper power bound for small-ball mass,
uniformly over centres in a fixed ambient ball. -/
theorem ae_smallBallMass_all_small_radii (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hcone : IsConeField γ P hC hcirc μ) :
    ∃ β : ℝ, 0 < β ∧ ∀ᵐ ω ∂P, ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r < r₀ → ∀ x ∈ ball (0 : ℂ) ρ,
        μ ω (ball x r) ≤ ENNReal.ofReal (r ^ β) := by
  obtain ⟨q, hq, hprob⟩ := smallBallMass_polyHighProb h217 hγ hγ2
  refine ⟨q / 2, by linarith, ?_⟩
  filter_upwards [(hprob ρ hρ hρ1 Ω P hC hcirc μ hcone).ae_eventually_dyadic] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.mp hω
  apply smallBallMass_of_eventual_dyadic (μ ω) (by linarith : 0 < q / 2) (by linarith : q / 2 < q) N
  intro n hn x hx
  simpa only [one_div] using hN n hn x hx

end MatedCRT
