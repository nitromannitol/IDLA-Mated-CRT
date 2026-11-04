import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicDelayedBootstrap
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.PolynomialFloor

/-! Qualitative vanishing of the initial part of the delayed dyadic budget. -/

namespace MatedCRT.Sec7

open Filter Topology

/-- A bounded additive logarithmic term does not affect the vanishing of a
positive power times the quadratic logarithmic loss. -/
theorem tendsto_rpow_mul_shifted_log_polynomial_floor
    {α ω A L : ℝ} (hα : 0 < α) (hA : 0 < A) (hL : 0 ≤ L) :
    Tendsto (fun x : ℝ => x ^ α * (1 + |Real.log (A * x ^ ω)| + L) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hlim := (tendsto_rpow_mul_log_polynomial_floor (ω := ω) hα hA).const_mul
    ((1 + L) ^ 2)
  have hlim' : Tendsto (fun x : ℝ => (1 + L) ^ 2 *
      (x ^ α * (1 + |Real.log (A * x ^ ω)|) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hlim
  apply squeeze_zero' ?_ ?_ hlim'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le α) (sq_nonneg _)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have habs := abs_nonneg (Real.log (A * x ^ ω))
    have hbound : 1 + |Real.log (A * x ^ ω)| + L ≤
        (1 + L) * (1 + |Real.log (A * x ^ ω)|) := by nlinarith
    have hsq := pow_le_pow_left₀ (by positivity :
      0 ≤ 1 + |Real.log (A * x ^ ω)| + L) hbound 2
    have hmul := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hx.le α)
    nlinarith

/-- The initial dyadic radius contribution vanishes as the rescaled initial
odometer tends to zero, without a polynomial-rate assumption. -/
theorem tendsto_delayed_dyadic_initial_log_budget
    {α c : ℝ} (hα : 0 < α) (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ α *
      (1 + |Real.log ((c / 8) * (x * (1 / 2 : ℝ)) ^ α)| +
        |Real.log ((1 / 2 : ℝ) ^ α)|) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  let A : ℝ := (c / 8) * (1 / 2 : ℝ) ^ α
  have hA : 0 < A := by dsimp [A]; positivity
  have hlim := tendsto_rpow_mul_shifted_log_polynomial_floor
    (α := α) (ω := α) (A := A) (L := |Real.log ((1 / 2 : ℝ) ^ α)|)
    hα hA (abs_nonneg _)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have heq : (c / 8) * (x * (1 / 2 : ℝ)) ^ α = A * x ^ α := by
    rw [Real.mul_rpow hx.le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    dsimp [A]
    ring
  rw [heq]

/-- Combining qualitative initial-odometer control with the floor and
diameter limits makes the entire delayed dyadic spatial budget vanish. -/
theorem tendsto_delayed_dyadic_total_budget
    {ι : Type*} {l : Filter ι} {α c C T : ℝ} (hα : 0 < α) (hc : 0 < c)
    (x r₀ F H D : ι → ℝ)
    (hx : Tendsto x l (𝓝[>] 0)) (hr₀ : Tendsto r₀ l (𝓝 0))
    (hfloor : Tendsto (fun i => F i * H i) l (𝓝 0))
    (hdiam : Tendsto (fun i => (H i + 1) * (2 * D i)) l (𝓝 0)) :
    Tendsto (fun i => r₀ i + (x i ^ α * C *
      ((1 + |Real.log ((c / 8) * (x i * (1 / 2 : ℝ)) ^ α)| +
        |Real.log ((1 / 2 : ℝ) ^ α)|) ^ 2 * T) + F i * H i) +
      (H i + 1) * (2 * D i)) l (𝓝 0) := by
  have hi := (tendsto_delayed_dyadic_initial_log_budget hα hc).comp hx
  have htotal := ((hr₀.add (hi.const_mul (C * T))).add hfloor).add hdiam
  have htotal' : Tendsto (fun i => r₀ i + (C * T) * (x i ^ α *
      (1 + |Real.log ((c / 8) * (x i * (1 / 2 : ℝ)) ^ α)| +
        |Real.log ((1 / 2 : ℝ) ^ α)|) ^ 2) + F i * H i +
      (H i + 1) * (2 * D i)) l (𝓝 0) := by
    simpa using htotal
  apply htotal'.congr'
  filter_upwards [] with i
  ring

end MatedCRT.Sec7
