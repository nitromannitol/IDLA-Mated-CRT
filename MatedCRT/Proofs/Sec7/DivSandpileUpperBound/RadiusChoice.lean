import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.RadiusMargins

/-! The delayed radius choice for the shell iteration. -/

namespace MatedCRT.Sec7

/-- The radius of the first shell uses the initial maximum; each subsequent
radius uses the maximum at the preceding shell, with a positive mesh floor. -/
noncomputable def delayedShellRadius (O : ℕ → ℝ) (K α R : ℝ) (k : ℕ) : ℝ :=
  max ((O k.pred * K) ^ α) R

theorem delayedShellRadius_zero (O : ℕ → ℝ) (K α R : ℝ) :
    delayedShellRadius O K α R 0 = max ((O 0 * K) ^ α) R := rfl

theorem delayedShellRadius_succ (O : ℕ → ℝ) (K α R : ℝ) (k : ℕ) :
    delayedShellRadius O K α R (k + 1) = max ((O k * K) ^ α) R := rfl

/-- Every radius dominates the mesh floor and the appropriate delayed
odometer scale. -/
theorem delayedShellRadius_bounds (O : ℕ → ℝ) (K α R : ℝ) :
    ((O 0 * K) ^ α ≤ delayedShellRadius O K α R 0) ∧
      (∀ k, (O k * K) ^ α ≤ delayedShellRadius O K α R (k + 1)) ∧
      (∀ k, R ≤ delayedShellRadius O K α R k) := by
  exact ⟨le_max_left _ _, fun _ => le_max_left _ _, fun _ => le_max_right _ _⟩

/-- A positive mesh floor makes every delayed shell radius positive. -/
theorem delayedShellRadius_pos (O : ℕ → ℝ) (K α R : ℝ) (hR : 0 < R) (k : ℕ) :
    0 < delayedShellRadius O K α R k :=
  hR.trans_le ((delayedShellRadius_bounds O K α R).2.2 k)

/-- The survival-test radius stays between a positive floor and one whenever
the shell radius lies between its floor and one. -/
theorem shell_test_radius_bounds
    (c R r : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 < R)
    (hfloor : R ≤ r) (hr1 : r ≤ 1) :
    0 < (c / 8) * R ∧ (c / 8) * R ≤ (c / 8) * r ∧ (c / 8) * r ≤ 1 := by
  have hc8 : 0 < c / 8 := by positivity
  have hcoeff : c / 8 ≤ 1 := by linarith
  have hr : 0 ≤ r := hR.le.trans hfloor
  have hmul : (c / 8) * r ≤ r := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoeff hr
  exact ⟨mul_pos hc8 hR, mul_le_mul_of_nonneg_left hfloor hc8.le,
    hmul.trans hr1⟩

end MatedCRT.Sec7
