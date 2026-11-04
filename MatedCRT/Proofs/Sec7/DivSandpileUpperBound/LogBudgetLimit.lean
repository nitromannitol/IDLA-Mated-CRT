import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RpowBudget
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.PolynomialFloor

/-! Vanishing shell-radius budget for polynomial mesh scales. -/

namespace MatedCRT.Sec7

open Filter Topology

/-- The geometric sum of radii vanishes when the initial radius is bounded by
a positive power of the mesh and the tested radius has a polynomial floor. -/
theorem tendsto_log_shell_radius_budget
    {α β ω A s : ℝ} (hα : 0 < α) (hβ : 0 < β) (hA : 0 < A)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    Tendsto (fun ε : ℝ => ε ^ α /
      (1 - (1 - s / (1 + |Real.log (A * ε ^ ω)|) ^ 2) ^ β))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hβ
  let N := n + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hNβ : 1 / (N : ℝ) ≤ β := by
    dsimp [N]
    simpa only [Nat.cast_add, Nat.cast_one] using hn.le
  have hlim := (tendsto_rpow_mul_log_polynomial_floor (ω := ω) hα hA).const_mul
    ((N : ℝ) / s)
  have hlim' : Tendsto (fun ε : ℝ => (N : ℝ) / s *
      (ε ^ α * (1 + |Real.log (A * ε ^ ω)|) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hlim
  apply squeeze_zero' ?_ ?_ hlim'
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hL : 1 ≤ (1 + |Real.log (A * ε ^ ω)|) ^ 2 := by
      have h := abs_nonneg (Real.log (A * ε ^ ω))
      nlinarith
    have hp : 0 < s / (1 + |Real.log (A * ε ^ ω)|) ^ 2 := div_pos hs (by linarith)
    have hp1 : s / (1 + |Real.log (A * ε ^ ω)|) ^ 2 ≤ 1 :=
      (div_le_one₀ (by linarith)).2 (hs1.trans hL)
    have hq : 0 ≤ 1 - s / (1 + |Real.log (A * ε ^ ω)|) ^ 2 := sub_nonneg.mpr hp1
    have hq1 : 1 - s / (1 + |Real.log (A * ε ^ ω)|) ^ 2 < 1 := by linarith
    exact div_nonneg (Real.rpow_nonneg hε.le α)
      (sub_nonneg.mpr (Real.rpow_lt_one hq hq1 hβ).le)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hL : 1 ≤ (1 + |Real.log (A * ε ^ ω)|) ^ 2 := by
      have h := abs_nonneg (Real.log (A * ε ^ ω))
      nlinarith
    have hbound := log_contraction_geometric_sum_le (ε ^ α) s (A * ε ^ ω) β N
      (Real.rpow_nonneg hε.le α) hs (hs1.trans hL) hN hNβ
    convert hbound using 1
    ring

end MatedCRT.Sec7
