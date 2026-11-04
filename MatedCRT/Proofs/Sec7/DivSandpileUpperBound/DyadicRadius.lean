import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicVanishing

/-! Radius scales within successive odometer-halving blocks. -/

namespace MatedCRT.Sec7

/-- A lower bound on the current odometer in a geometric block yields the
geometric lower bound on the survival-test radius used in that block. -/
theorem shell_test_radius_ge_of_geometric_odometer
    (O₀ O K α c r q : ℝ) (j : ℕ)
    (hO₀ : 0 ≤ O₀) (hK : 0 ≤ K) (hα : 0 ≤ α) (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hO : O₀ * q ^ (j + 1) ≤ O) (hrad : (O * K) ^ α ≤ r) :
    ((c / 8) * (O₀ * K * q) ^ α) * (q ^ α) ^ j ≤ (c / 8) * r := by
  have hbase : O₀ * q ^ (j + 1) * K ≤ O * K :=
    mul_le_mul_of_nonneg_right hO hK
  have hpow := Real.rpow_le_rpow (mul_nonneg (mul_nonneg hO₀ (pow_nonneg hq _)) hK)
    hbase hα
  have heq : (O₀ * q ^ (j + 1) * K) ^ α = (O₀ * K * q) ^ α * (q ^ α) ^ j := by
    rw [show O₀ * q ^ (j + 1) * K = (O₀ * K * q) * q ^ j by rw [pow_succ]; ring,
      Real.mul_rpow (mul_nonneg (mul_nonneg hO₀ hK) hq) (pow_nonneg hq j),
      ← Real.rpow_natCast_mul hq j α, mul_comm (j : ℝ) α,
      Real.rpow_mul_natCast hq α j]
  rw [heq] at hpow
  have htest := mul_le_mul_of_nonneg_left (hpow.trans hrad) (show 0 ≤ c / 8 by positivity)
  nlinarith

end MatedCRT.Sec7
