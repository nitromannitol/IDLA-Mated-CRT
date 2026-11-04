import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.PolynomialFloor

/-! Polynomial mesh scales dominate any fixed polylogarithmic shell horizon. -/

namespace MatedCRT.Sec7

open Filter Topology

/-- Every positive power dominates every natural power of the logarithm. -/
theorem tendsto_rpow_mul_log_loss_pow {α : ℝ} (hα : 0 < α) (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ α * (1 + |Real.log x|) ^ n) (𝓝[>] 0) (𝓝 0) := by
  cases n with
  | zero =>
    have hp := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
    simpa [Real.zero_rpow hα.ne'] using hp.mono_left nhdsWithin_le_nhds
  | succ n =>
    let e := α / ((n + 1 : ℕ) : ℝ)
    have he : 0 < e := by dsimp [e]; positivity
    have hp : Tendsto (fun x : ℝ => x ^ e) (𝓝[>] 0) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const 0 e (Or.inr he.le)).tendsto
      simpa [Real.zero_rpow he.ne'] using h.mono_left nhdsWithin_le_nhds
    have hl := (tendsto_log_mul_rpow_nhdsGT_zero he).abs
    have hsum : Tendsto (fun x : ℝ => x ^ e + |Real.log x * x ^ e|)
        (𝓝[>] 0) (𝓝 0) := by simpa using hp.add hl
    have h := hsum.pow (n + 1)
    have h' : Tendsto (fun x : ℝ => (x ^ e + |Real.log x * x ^ e|) ^ (n + 1))
        (𝓝[>] 0) (𝓝 0) := by simpa using h
    apply h'.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le e)]
    have heq : x ^ e + |Real.log x| * x ^ e = x ^ e * (1 + |Real.log x|) := by ring
    rw [heq, mul_pow, ← Real.rpow_mul_natCast hx.le]
    have heα : e * ((n + 1 : ℕ) : ℝ) = α := by dsimp [e]; field_simp
    rw [heα]

/-- A positive mesh power dominates the polylogarithmic loss associated with
any constant multiple of a power of the mesh. -/
theorem tendsto_rpow_mul_log_polynomial_floor_pow
    {α ω A : ℝ} (hα : 0 < α) (hA : 0 < A) (n : ℕ) :
    Tendsto (fun ε : ℝ => ε ^ α * (1 + |Real.log (A * ε ^ ω)|) ^ n)
      (𝓝[>] 0) (𝓝 0) := by
  let C := 1 + |Real.log A| + |ω|
  have hlim := (tendsto_rpow_mul_log_loss_pow hα n).const_mul (C ^ n)
  have hlim' : Tendsto (fun ε : ℝ => C ^ n *
      (ε ^ α * (1 + |Real.log ε|) ^ n)) (𝓝[>] 0) (𝓝 0) := by simpa using hlim
  apply squeeze_zero' ?_ ?_ hlim'
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mul_nonneg (Real.rpow_nonneg hε.le α) (pow_nonneg (by positivity) _)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hpow : ε ^ ω ≠ 0 := (Real.rpow_pos_of_pos hε ω).ne'
    have hlog : |Real.log (A * ε ^ ω)| ≤ |Real.log A| + |ω| * |Real.log ε| := by
      rw [Real.log_mul hA.ne' hpow, Real.log_rpow hε]
      simpa only [abs_mul] using abs_add_le (Real.log A) (ω * Real.log ε)
    have hbound : 1 + |Real.log (A * ε ^ ω)| ≤ C * (1 + |Real.log ε|) := by
      dsimp [C]
      nlinarith [abs_nonneg (Real.log A), abs_nonneg ω, abs_nonneg (Real.log ε)]
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |Real.log (A * ε ^ ω)|)
      hbound n
    have hmul := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hε.le α)
    rw [mul_pow] at hmul
    nlinarith

/-- A polylogarithmic number of shells times a polynomial mesh error vanishes. -/
theorem tendsto_polylog_horizon_mul_rpow
    {α ω A C : ℝ} (hα : 0 < α) (hA : 0 < A) (n : ℕ) (horizon : ℝ → ℕ)
    (hbound : ∀ᶠ ε in 𝓝[>] 0, (horizon ε : ℝ) ≤
      C * (1 + |Real.log (A * ε ^ ω)|) ^ n) :
    Tendsto (fun ε : ℝ => (horizon ε : ℝ) * ε ^ α) (𝓝[>] 0) (𝓝 0) := by
  have hlim := (tendsto_rpow_mul_log_polynomial_floor_pow (ω := ω) hα hA n).const_mul C
  have hlim' : Tendsto (fun ε : ℝ => C *
      (ε ^ α * (1 + |Real.log (A * ε ^ ω)|) ^ n)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hlim
  apply squeeze_zero' ?_ ?_ hlim'
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hε.le α)
  · filter_upwards [self_mem_nhdsWithin, hbound] with ε hε hεbound
    have h := mul_le_mul_of_nonneg_right hεbound (Real.rpow_nonneg hε.le α)
    nlinarith

end MatedCRT.Sec7
