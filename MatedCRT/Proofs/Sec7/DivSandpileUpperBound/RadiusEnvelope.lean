import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShiftedRadius

/-! A uniform envelope for the delayed shell radii. -/

namespace MatedCRT.Sec7

/-- Before the boundary maxima stop decreasing, every shell radius is bounded
by the initial radius or by the radius chosen from the initial maximum. -/
theorem shell_radii_le_initial_envelope
    (O r : ℕ → ℝ) (K α R : ℝ) (n : ℕ)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hO : ∀ k < n, 0 ≤ O k)
    (hmono : ∀ k < n, O (k + 1) ≤ O k)
    (hr : ∀ k < n, r (k + 1) ≤ max ((O k * K) ^ α) R) :
    ∀ k ≤ n, r k ≤ max (r 0) (max ((O 0 * K) ^ α) R) := by
  have hOupper : ∀ k ≤ n, O k ≤ O 0 := by
    intro k hk
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hmono k (by omega)).trans (ih (by omega))
  intro k hk
  cases k with
  | zero => exact le_max_left _ _
  | succ k =>
    have hp : (O k * K) ^ α ≤ (O 0 * K) ^ α :=
      Real.rpow_le_rpow (mul_nonneg (hO k (by omega)) hK)
        (mul_le_mul_of_nonneg_right (hOupper k (by omega)) hK) hα
    exact (hr k (by omega)).trans ((max_le_max hp le_rfl).trans (le_max_right _ _))

end MatedCRT.Sec7
