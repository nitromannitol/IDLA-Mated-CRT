import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.BudgetBootstrap
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShiftedRadius

/-! Closing the bootstrap for the delayed radius recurrence. -/

namespace MatedCRT.Sec7

/-- If a shell contracts once its current radius controls its current maximum,
the delayed radius recurrence and all earlier contractions provide exactly that
control. This closes the radius and spatial-budget bootstrap simultaneously. -/
theorem exists_shell_threshold_of_shifted_radius_bootstrap
    (O r : ℕ → ℝ) (q K α R D B δ : ℝ) (n : ℕ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hK : 0 ≤ K) (hα : 0 < α)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hr0 : 0 ≤ r 0) (hO : ∀ k ≤ n, 0 ≤ O k)
    (hend : O 0 * q ^ n ≤ B)
    (hfirst : (O 0 * K) ^ α ≤ r 0)
    (hrlo : ∀ k < n, (O k * K) ^ α ≤ r (k + 1))
    (hrhi : ∀ k < n, r (k + 1) ≤ max ((O k * K) ^ α) R)
    (hstep : ∀ k < n, B < O k →
      (∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D) ≤ δ →
      (O k * K) ^ α ≤ r k → O (k + 1) ≤ q * O k)
    (hbudget : r 0 + (O 0 * K) ^ α / (1 - q ^ α) +
      (n : ℝ) * R + ((n : ℝ) + 1) * (2 * D) ≤ δ) :
    ∃ τ : ℕ, τ ≤ n ∧ O τ ≤ B ∧ (∀ k < τ, B < O k) ∧
      (∑ j ∈ Finset.range τ, r j) + ((τ : ℝ) + 1) * (2 * D) ≤ δ := by
  apply exists_shell_threshold_of_budget_bootstrap O r q K α R D B δ n
    hq hq1 hK hα hR hD hr0 hO hend hrhi ?_ hbudget
  intro k hk habove hbudgetk hprev
  apply hstep k hk habove hbudgetk
  have h := shifted_shell_radii_control_current_maxima O r 1 K α q k
    (fun j hj => hO j (by omega)) (by norm_num) hK hα.le hq1.le
    (by simpa using hfirst) (fun j hj => by simpa using hrlo j (by omega)) hprev k le_rfl
  simpa using h

end MatedCRT.Sec7
