import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LogLossSeries

/-! Logarithmic losses for polynomial lower bounds on shell radii. -/

namespace MatedCRT.Sec7

open Filter Topology

/-- A positive power of the mesh dominates the quadratic logarithmic loss
associated with any positive constant times a power of the mesh. -/
theorem tendsto_rpow_mul_log_polynomial_floor
    {α ω A : ℝ} (hα : 0 < α) (hA : 0 < A) :
    Tendsto (fun ε : ℝ => ε ^ α * (1 + |Real.log (A * ε ^ ω)|) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let C := 1 + |Real.log A| + |ω|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlim := (tendsto_rpow_mul_quadratic_log_loss hα).const_mul (C ^ 2)
  have hlim' : Tendsto (fun ε : ℝ => C ^ 2 *
      (ε ^ α * (1 + |Real.log ε|) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hlim
  apply squeeze_zero' ?_ ?_ hlim'
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mul_nonneg (Real.rpow_nonneg hε.le α) (sq_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hpow : ε ^ ω ≠ 0 := (Real.rpow_pos_of_pos hε ω).ne'
    have hlog : |Real.log (A * ε ^ ω)| ≤ |Real.log A| + |ω| * |Real.log ε| := by
      rw [Real.log_mul hA.ne' hpow, Real.log_rpow hε]
      simpa only [abs_mul] using abs_add_le (Real.log A) (ω * Real.log ε)
    have hlognonneg : 0 ≤ |Real.log ε| := abs_nonneg _
    have hbound : 1 + |Real.log (A * ε ^ ω)| ≤ C * (1 + |Real.log ε|) := by
      dsimp [C]
      nlinarith [abs_nonneg (Real.log A), abs_nonneg ω]
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |Real.log (A * ε ^ ω)|)
      hbound 2
    have hmul := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hε.le α)
    nlinarith

end MatedCRT.Sec7
