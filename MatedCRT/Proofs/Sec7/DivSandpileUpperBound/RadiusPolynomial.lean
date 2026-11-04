import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RadiusChoice

/-! Polynomial upper envelopes for the delayed shell radius. -/

namespace MatedCRT.Sec7

open Filter Topology

/-- A polynomial upper bound on the initial odometer maximum gives a
polynomial upper bound on the initial delayed shell radius. -/
theorem delayedShellRadius_initial_polynomial_bound
    (O : ℕ → ℝ) (ε A K p α q : ℝ)
    (hε : 0 < ε) (hA : 0 ≤ A) (hK : 0 ≤ K) (hO : 0 ≤ O 0)
    (hα : 0 ≤ α) (hupper : O 0 ≤ A * ε ^ (-p)) :
    delayedShellRadius O (ε * K) α (ε ^ q) 0 ≤
      (A * K) ^ α * ε ^ ((1 - p) * α) + ε ^ q := by
  have hbase : O 0 * (ε * K) ≤ (A * K) * ε ^ (1 - p) := by
    calc
      O 0 * (ε * K) ≤ (A * ε ^ (-p)) * (ε * K) :=
        mul_le_mul_of_nonneg_right hupper (mul_nonneg hε.le hK)
      _ = (A * K) * ε ^ (1 - p) := by
        rw [show 1 - p = 1 + -p by ring, Real.rpow_add hε, Real.rpow_one]
        ring
  have hpow := Real.rpow_le_rpow (mul_nonneg hO (mul_nonneg hε.le hK)) hbase hα
  have heq : ((A * K) * ε ^ (1 - p)) ^ α =
      (A * K) ^ α * ε ^ ((1 - p) * α) := by
    rw [Real.mul_rpow (mul_nonneg hA hK) (Real.rpow_nonneg hε.le _),
      ← Real.rpow_mul hε.le]
  rw [delayedShellRadius_zero]
  apply max_le
  · rw [heq] at hpow
    exact hpow.trans (le_add_of_nonneg_right (Real.rpow_nonneg hε.le _))
  · exact le_add_of_nonneg_left
      (mul_nonneg (Real.rpow_nonneg (mul_nonneg hA hK) _) (Real.rpow_nonneg hε.le _))

/-- The polynomial upper envelope vanishes when the initial maximum has
growth exponent below one and the mesh floor has positive exponent. -/
theorem tendsto_delayedShellRadius_polynomial_envelope
    (A K p α q : ℝ) (hp : p < 1) (hα : 0 < α) (hq : 0 < q) :
    Tendsto (fun ε : ℝ => (A * K) ^ α * ε ^ ((1 - p) * α) + ε ^ q)
      (𝓝[>] 0) (𝓝 0) := by
  have h1 := tendsto_rpow_nhdsGT_zero (mul_pos (sub_pos.mpr hp) hα)
  have h2 := tendsto_rpow_nhdsGT_zero hq
  simpa using (h1.const_mul ((A * K) ^ α)).add h2

end MatedCRT.Sec7
