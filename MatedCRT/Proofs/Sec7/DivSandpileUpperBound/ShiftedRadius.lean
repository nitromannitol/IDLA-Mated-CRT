import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RadiusSlack

/-! Radius admissibility for the one-step-delayed shell recurrence. -/

namespace MatedCRT.Sec7

/-- A radius selected using the previous maximum also controls the current
maximum when that maximum has contracted. -/
theorem shifted_shell_radius_controls_current_maximum
    {O₀ O₁ ε K α q r : ℝ}
    (hO₀ : 0 ≤ O₀) (hO₁ : 0 ≤ O₁) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hα : 0 ≤ α) (hq : q ≤ 1) (hcontract : O₁ ≤ q * O₀)
    (hradius : (O₀ * ε * K) ^ α ≤ r) :
    (O₁ * ε * K) ^ α ≤ r := by
  have hle : O₁ ≤ O₀ := hcontract.trans (by nlinarith)
  have hbase : 0 ≤ O₁ * ε * K := mul_nonneg (mul_nonneg hO₁ hε) hK
  have hmul : O₁ * ε * K ≤ O₀ * ε * K :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hε) hK
  exact (Real.rpow_le_rpow hbase hmul hα).trans hradius

/-- Earlier contractions make every shifted shell radius admissible for the
maximum at its current shell. -/
theorem shifted_shell_radii_control_current_maxima
    (O r : ℕ → ℝ) (ε K α q : ℝ) (n : ℕ)
    (hO : ∀ k ≤ n, 0 ≤ O k) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hα : 0 ≤ α) (hq : q ≤ 1)
    (hfirst : (O 0 * ε * K) ^ α ≤ r 0)
    (hr : ∀ k < n, (O k * ε * K) ^ α ≤ r (k + 1))
    (hcontract : ∀ k < n, O (k + 1) ≤ q * O k) :
    ∀ k ≤ n, (O k * ε * K) ^ α ≤ r k := by
  intro k hk
  cases k with
  | zero => exact hfirst
  | succ k =>
    exact shifted_shell_radius_controls_current_maximum
      (hO k (by omega)) (hO (k + 1) hk) hε hK hα hq
      (hcontract k (by omega)) (hr k (by omega))

end MatedCRT.Sec7
