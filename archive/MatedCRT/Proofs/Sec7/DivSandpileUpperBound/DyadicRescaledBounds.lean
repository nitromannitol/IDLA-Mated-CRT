import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicPolynomialHorizon

/-! Polynomial bounds for the rescaled initial odometer. -/

namespace MatedCRT.Sec7

/-- A positive fixed coefficient is absorbed into one extra mesh power on
each side of the rescaled initial-odometer bounds. -/
theorem rescaled_initial_maximum_mesh_bounds
    (ε S K p b : ℝ) (hε : 0 < ε) (hS : 0 ≤ S)
    (hεK : ε ≤ K) (hKsmall : ε * K ≤ 1)
    (hSlo : ε ^ b ≤ S) (hShi : S ≤ ε ^ (-p)) :
    ε ^ (b + 2) ≤ S * (ε * K) ∧ S * (ε * K) ≤ ε ^ (-p) := by
  have hscale : ε * ε ≤ ε * K := mul_le_mul_of_nonneg_left hεK hε.le
  have hlow := mul_le_mul hSlo hscale (mul_nonneg hε.le hε.le) hS
  have heq : ε ^ (b + 2 : ℝ) = ε ^ b * (ε * ε) := by
    rw [Real.rpow_add hε, Real.rpow_two]
    ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hlow
  · have hh := mul_le_mul_of_nonneg_left hKsmall hS
    linarith

end MatedCRT.Sec7
