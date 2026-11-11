import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.BudgetBootstrap
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.HalvingTime

/-! Spatial-budget bootstrap for shell contraction with logarithmic loss. -/

namespace MatedCRT.Sec7

/-- A uniform lower bound on the tested radius converts logarithmic shell
contraction into a geometric majorant. This closes the spatial-budget
bootstrap while retaining the original radius-dependent contraction. -/
theorem exists_shell_threshold_of_log_budget_bootstrap
    (O r u : ℕ → ℝ) (s a K α R D B δ : ℝ) (n : ℕ)
    (hs : 0 < s) (ha : 0 < a)
    (hsbound : s ≤ (1 + |Real.log a|) ^ 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hr0 : 0 ≤ r 0) (hO : ∀ k ≤ n, 0 ≤ O k)
    (hu : ∀ k < n, a ≤ u k ∧ u k ≤ 1)
    (hend : O 0 * (1 - s / (1 + |Real.log a|) ^ 2) ^ n ≤ B)
    (hr : ∀ k < n, r (k + 1) ≤ max ((O k * K) ^ α) R)
    (hstep : ∀ k < n, B < O k →
      (∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D) ≤ δ →
      (∀ j < k, O (j + 1) ≤ O j) →
      O (k + 1) ≤ (1 - s / (1 + |Real.log (u k)|) ^ 2) * O k)
    (hbudget : r 0 + (O 0 * K) ^ α /
      (1 - (1 - s / (1 + |Real.log a|) ^ 2) ^ α) +
      (n : ℝ) * R + ((n : ℝ) + 1) * (2 * D) ≤ δ) :
    ∃ τ : ℕ, τ ≤ n ∧ O τ ≤ B ∧ (∀ k < τ, B < O k) ∧
      (∑ j ∈ Finset.range τ, r j) + ((τ : ℝ) + 1) * (2 * D) ≤ δ := by
  let L := 1 + |Real.log a|
  let p := s / L ^ 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hLsq : 0 < L ^ 2 := by positivity
  have hp : 0 < p := div_pos hs hLsq
  have hp1 : p ≤ 1 := (div_le_one₀ hLsq).2 hsbound
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hq1 : 1 - p < 1 := by linarith
  apply exists_shell_threshold_of_budget_bootstrap O r (1 - p) K α R D B δ n
    hq hq1 hK hα hR hD hr0 hO hend hr ?_ hbudget
  intro k hk habove hbudgetk hprev
  have hmono : ∀ j < k, O (j + 1) ≤ O j := by
    intro j hj
    have hmul := mul_nonneg hp.le (hO j (by omega))
    have h := hprev j hj
    nlinarith
  have hden : 0 < (1 + |Real.log (u k)|) ^ 2 := by positivity
  have hlog : 1 + |Real.log (u k)| ≤ L :=
    log_loss_le_of_radius_lower_bound ha (hu k hk).1 (hu k hk).2
  have hsq : (1 + |Real.log (u k)|) ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlog 2
  have hrate : p ≤ s / (1 + |Real.log (u k)|) ^ 2 :=
    div_le_div_of_nonneg_left hs.le hden hsq
  have hmul := mul_le_mul_of_nonneg_right hrate (hO k (by omega))
  have h := hstep k hk habove hbudgetk hmono
  nlinarith

end MatedCRT.Sec7
