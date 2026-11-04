import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicBudgetBootstrap
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicRadius
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShiftedRadius

/-! Survival-test radii in the delayed dyadic shell construction. -/

namespace MatedCRT.Sec7

/-- A delayed shell radius controls the current dyadic test radius whenever
the preceding odometer maxima are nonincreasing. -/
theorem dyadic_test_radius_bounds_of_shifted_radii
    (O r : ℕ → ℝ) (S K α c : ℝ) (j k : ℕ)
    (hS : 0 ≤ S) (hK : 0 ≤ K) (hα : 0 ≤ α) (hc : 0 ≤ c)
    (hO : ∀ i ≤ k, 0 ≤ O i)
    (hfirst : (O 0 * K) ^ α ≤ r 0)
    (hshift : ∀ i < k, (O i * K) ^ α ≤ r (i + 1))
    (hprev : ∀ i < k, O (i + 1) ≤ O i)
    (hactive : S * (1 / 2 : ℝ) ^ (j + 1) ≤ O k)
    (hupper : (c / 8) * r k ≤ 1) :
    ((c / 8) * (S * K * (1 / 2 : ℝ)) ^ α) *
        ((1 / 2 : ℝ) ^ α) ^ j ≤ (c / 8) * r k ∧ (c / 8) * r k ≤ 1 := by
  have hfirst' : (O 0 * 1 * K) ^ α ≤ r 0 := by simpa using hfirst
  have hshift' : ∀ i < k, (O i * 1 * K) ^ α ≤ r (i + 1) := by
    intro i hi
    simpa using hshift i hi
  have hprev' : ∀ i < k, O (i + 1) ≤ 1 * O i := by simpa using hprev
  have hrad := shifted_shell_radii_control_current_maxima O r 1 K α 1 k hO
    (by norm_num) hK hα (by norm_num) hfirst' hshift' hprev' k le_rfl
  have hrad' : (O k * K) ^ α ≤ r k := by simpa using hrad
  exact ⟨shell_test_radius_ge_of_geometric_odometer S (O k) K α c (r k)
    (1 / 2) j hS hK hα hc (by norm_num) hactive hrad', hupper⟩

end MatedCRT.Sec7
