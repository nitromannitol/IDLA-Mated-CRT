import Mathlib

/-!
# Amplification arithmetic for the printed Lemma 6.8 (q2, task fp-S4S6c; LEMMA68 "Proof of Lemma 6.8", eqs (23)-(27), (3))

Pure real analysis used at the end of the multi-test argument of `notes/fp-gaps/LEMMA68.md`. If a per-test failure
probability `c/(1+|log r|)²` holds for `N ≥ κ r^{-ζ}` successive tests, then the probability that all of them succeed
is at most `(1 - c/(1+|log r|)²)^N ≤ exp(-cκ r^{-ζ}/(1+|log r|)²)`, which is at most `1/2` for all small `r`.

Not here: the successive tests themselves (stopping times (27), conditional probabilities given the field and the
mating-of-trees curve, and the count `N = ⌊r/(100√δ)⌋` of (26)). Those are the open NEW steps of Lemma 6.8.
-/

open Filter Topology

namespace MatedCRT

/-- `r ^ (-ζ) / (1 + |log r|)²` tends to infinity as `r` decreases to `0`. -/
theorem tendsto_rpow_neg_div_one_add_abs_log_sq {ζ : ℝ} (hζ : 0 < ζ) :
    Tendsto (fun r : ℝ => r ^ (-ζ) / (1 + |Real.log r|) ^ 2) (𝓝[>] 0) atTop := by
  have hu : Tendsto (fun r : ℝ => -Real.log r) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hy : Tendsto (fun r : ℝ => ζ * -Real.log r) (𝓝[>] 0) atTop :=
    Tendsto.const_mul_atTop hζ hu
  have hg : Tendsto (fun r : ℝ => Real.exp (ζ * -Real.log r) / (ζ * -Real.log r) ^ 2)
      (𝓝[>] 0) atTop :=
    (Real.tendsto_exp_div_pow_atTop 2).comp hy
  have hlow : Tendsto (fun r : ℝ => ζ ^ 2 / 4 * (Real.exp (ζ * -Real.log r) / (ζ * -Real.log r) ^ 2))
      (𝓝[>] 0) atTop :=
    Tendsto.const_mul_atTop (by positivity) hg
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
    hu.eventually_ge_atTop 1] with r hr hu1
  have hr0 : 0 < r := hr.1
  have hlog : Real.log r < 0 := Real.log_neg hr.1 hr.2
  have habs : |Real.log r| = -Real.log r := abs_of_neg hlog
  have hrp : r ^ (-ζ) = Real.exp (ζ * -Real.log r) := by
    rw [Real.rpow_def_of_pos hr0]
    congr 1
    ring
  rw [habs, hrp]
  set u := -Real.log r with hu_def
  have hζne : ζ ≠ 0 := hζ.ne'
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu1; norm_num at hu1
  have key : ζ ^ 2 / 4 * (Real.exp (ζ * u) / (ζ * u) ^ 2) = Real.exp (ζ * u) / (4 * u ^ 2) := by
    field_simp
  rw [key]
  apply div_le_div_of_nonneg_left (Real.exp_pos _).le (pow_pos (by linarith) 2)
  nlinarith

/-- For `c > 0`, `exp(-c · r^{-ζ}/(1+|log r|)²) ≤ 1/2` for all small `r > 0`. -/
theorem eventually_exp_neg_mul_le_half {c ζ : ℝ} (hc : 0 < c) (hζ : 0 < ζ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), Real.exp (-(c * (r ^ (-ζ) / (1 + |Real.log r|) ^ 2))) ≤ 1 / 2 := by
  have h := (tendsto_rpow_neg_div_one_add_abs_log_sq hζ).const_mul_atTop hc
  filter_upwards [h.eventually_ge_atTop (Real.log 2)] with r hr
  have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log two_pos]
    norm_num
  have h3 : Real.exp (-(c * (r ^ (-ζ) / (1 + |Real.log r|) ^ 2))) ≤ Real.exp (-Real.log 2) :=
    Real.exp_le_exp.2 (by linarith)
  exact h3.trans h2.le

/-- For `c > 0`, `c/(1+|log r|)² ≤ 1` for all small `r > 0`. -/
theorem eventually_div_one_add_abs_log_sq_le_one {c : ℝ} (hc : 0 < c) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), c / (1 + |Real.log r|) ^ 2 ≤ 1 := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).eventually_ge_atTop c] with r hr hcr
  have hlog : Real.log r < 0 := Real.log_neg hr.1 hr.2
  have hu : c ≤ -Real.log r := hcr
  have hpos : 0 < -Real.log r := lt_of_lt_of_le hc hu
  rw [abs_of_neg hlog, div_le_one (pow_pos (by linarith [hpos]) 2)]
  nlinarith [sq_nonneg (-Real.log r)]

/-- The elementary bound `(1 - q)^N ≤ exp(-q N)` for `0 ≤ q ≤ 1`. -/
theorem pow_one_sub_le_exp_neg_mul {q : ℝ} (hq1 : q ≤ 1) (N : ℕ) :
    (1 - q) ^ N ≤ Real.exp (-(q * N)) := by
  have h1 : 0 ≤ 1 - q := by linarith
  have h2 : 1 - q ≤ Real.exp (-q) := by linarith [Real.add_one_le_exp (-q)]
  have h3 : Real.exp (-(q * N)) = Real.exp (-q) ^ N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h3]
  exact pow_le_pow_left₀ h1 h2 N

/-- **Amplification arithmetic.** If each of `N ≥ κ r^{-ζ}` successive tests has failure probability
`c/(1+|log r|)²`, then the probability that all of them succeed is at most `1/2` for all small `r > 0`. -/
theorem eventually_amplified_le_half {c κ ζ : ℝ} (hc : 0 < c) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ N : ℕ, κ * r ^ (-ζ) ≤ N →
      (1 - c / (1 + |Real.log r|) ^ 2) ^ N ≤ 1 / 2 := by
  filter_upwards [eventually_exp_neg_mul_le_half (mul_pos hc hκ) hζ,
    eventually_div_one_add_abs_log_sq_le_one hc] with r hexp hq1 N hN
  have hq0 : 0 ≤ c / (1 + |Real.log r|) ^ 2 := by positivity
  have hpow := pow_one_sub_le_exp_neg_mul hq1 N
  have hqN : c / (1 + |Real.log r|) ^ 2 * (κ * r ^ (-ζ)) ≤ c / (1 + |Real.log r|) ^ 2 * N :=
    mul_le_mul_of_nonneg_left hN hq0
  have hid : c * κ * (r ^ (-ζ) / (1 + |Real.log r|) ^ 2) =
      c / (1 + |Real.log r|) ^ 2 * (κ * r ^ (-ζ)) := by ring
  have hle : Real.exp (-(c / (1 + |Real.log r|) ^ 2 * N)) ≤
      Real.exp (-(c * κ * (r ^ (-ζ) / (1 + |Real.log r|) ^ 2))) :=
    Real.exp_le_exp.2 (by linarith)
  exact hpow.trans (hle.trans hexp)

end MatedCRT
