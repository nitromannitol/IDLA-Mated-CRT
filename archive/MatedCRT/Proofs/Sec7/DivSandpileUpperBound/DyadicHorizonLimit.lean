import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicChooseHorizon
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.PolylogBudget

/-! Polynomial mesh errors over a cubic-log shell horizon. -/

namespace MatedCRT.Sec7

open Filter Topology

/-- A cubic-log bound on a natural horizon also controls the extra shell in
the diameter term, after multiplication by a positive power of the mesh. -/
theorem tendsto_cubic_log_horizon_add_one_mul_rpow
    {α C : ℝ} (hα : 0 < α) (horizon : ℝ → ℕ)
    (hbound : ∀ᶠ ε in 𝓝[>] 0, (horizon ε : ℝ) ≤
      C * (1 + |Real.log ε|) ^ 3 + 2) :
    Tendsto (fun ε : ℝ => ((horizon ε : ℝ) + 1) * ε ^ α)
      (𝓝[>] 0) (𝓝 0) := by
  have hbound' : ∀ᶠ ε in 𝓝[>] 0, (horizon ε : ℝ) ≤
      (C + 2) * (1 + |Real.log ((1 : ℝ) * ε ^ (1 : ℝ))|) ^ 3 := by
    filter_upwards [hbound] with ε hε
    simp only [Real.rpow_one, one_mul]
    have hone : (1 : ℝ) ≤ 1 + |Real.log ε| := by linarith [abs_nonneg (Real.log ε)]
    have hcub := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hone 3
    norm_num at hcub
    nlinarith
  have hh := tendsto_polylog_horizon_mul_rpow (ω := 1) (A := 1) hα
    (by norm_num) 3 horizon hbound'
  have hp : Tendsto (fun ε : ℝ => ε ^ α) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
    simpa [Real.zero_rpow hα.ne'] using h.mono_left nhdsWithin_le_nhds
  have hh' : Tendsto (fun ε : ℝ => (horizon ε : ℝ) * ε ^ α + ε ^ α)
      (𝓝[>] 0) (𝓝 0) := by simpa using hh.add hp
  apply hh'.congr'
  filter_upwards [] with ε
  ring

/-- A nonnegative polynomially bounded mesh error times a real horizon
dominated by a cubic-log natural horizon tends to zero. -/
theorem tendsto_cubic_log_real_horizon_mul_error
    {α C E : ℝ} (hα : 0 < α) (hE : 0 ≤ E)
    (horizon : ℝ → ℕ) (H F : ℝ → ℝ)
    (hbound : ∀ᶠ ε in 𝓝[>] 0, (horizon ε : ℝ) ≤
      C * (1 + |Real.log ε|) ^ 3 + 2)
    (hH : ∀ᶠ ε in 𝓝[>] 0, 0 ≤ H ε ∧ H ε ≤ horizon ε)
    (hF : ∀ᶠ ε in 𝓝[>] 0, 0 ≤ F ε ∧ F ε ≤ E * ε ^ α) :
    Tendsto (fun ε : ℝ => (H ε + 1) * F ε) (𝓝[>] 0) (𝓝 0) := by
  have hlim := (tendsto_cubic_log_horizon_add_one_mul_rpow hα horizon hbound).const_mul E
  have hlim' : Tendsto (fun ε : ℝ => E * (((horizon ε : ℝ) + 1) * ε ^ α))
      (𝓝[>] 0) (𝓝 0) := by simpa using hlim
  apply squeeze_zero' ?_ ?_ hlim'
  · filter_upwards [hH, hF] with ε hεH hεF
    exact mul_nonneg (by linarith [hεH.1]) hεF.1
  · filter_upwards [self_mem_nhdsWithin, hH, hF] with ε hε hεH hεF
    have h₁ := mul_le_mul_of_nonneg_left hεF.2
      (show 0 ≤ H ε + 1 by linarith [hεH.1])
    have h₂ := mul_le_mul_of_nonneg_right (add_le_add_right hεH.2 1)
      (mul_nonneg hE (Real.rpow_nonneg hε.le α))
    nlinarith

/-- The floor and diameter contributions in the delayed dyadic budget
vanish when both are polynomially bounded and the horizon is cubic-log. -/
theorem tendsto_dyadic_floor_and_diameter_budgets
    {α β C E₁ E₂ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (horizon : ℝ → ℕ) (H F D : ℝ → ℝ)
    (hbound : ∀ᶠ ε in 𝓝[>] 0, (horizon ε : ℝ) ≤
      C * (1 + |Real.log ε|) ^ 3 + 2)
    (hH : ∀ᶠ ε in 𝓝[>] 0, 0 ≤ H ε ∧ H ε ≤ horizon ε)
    (hF : ∀ᶠ ε in 𝓝[>] 0, 0 ≤ F ε ∧ F ε ≤ E₁ * ε ^ α)
    (hD : ∀ᶠ ε in 𝓝[>] 0, 0 ≤ D ε ∧ D ε ≤ E₂ * ε ^ β) :
    Tendsto (fun ε : ℝ => F ε * H ε) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ε : ℝ => (H ε + 1) * (2 * D ε)) (𝓝[>] 0) (𝓝 0) := by
  have hplusF := tendsto_cubic_log_real_horizon_mul_error hα hE₁ horizon H F
    hbound hH hF
  have hplusD := tendsto_cubic_log_real_horizon_mul_error hβ hE₂ horizon H D
    hbound hH hD
  constructor
  · apply squeeze_zero' ?_ ?_ hplusF
    · filter_upwards [hH, hF] with ε hεH hεF
      exact mul_nonneg hεF.1 hεH.1
    · filter_upwards [hF] with ε hεF
      have h := mul_le_mul_of_nonneg_right (show H ε ≤ H ε + 1 by linarith) hεF.1
      nlinarith
  · have hh := hplusD.const_mul 2
    have hh' : Tendsto (fun ε : ℝ => 2 * ((H ε + 1) * D ε)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hh
    apply hh'.congr'
    filter_upwards [] with ε
    ring

end MatedCRT.Sec7
