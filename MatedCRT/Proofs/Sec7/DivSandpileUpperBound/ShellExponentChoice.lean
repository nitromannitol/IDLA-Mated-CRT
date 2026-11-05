import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicEventCertificate

/-! Compatible mesh, survival, and mass exponents for the shell iteration.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

/-- Positive mass and survival exponents permit a common smaller target
exponent and a still smaller radius floor, below the cell-diameter exponent. -/
theorem exists_compatible_shell_exponents
    {γ βₘ ω : ℝ} (hγ : 0 < γ) (hβₘ : 0 < βₘ) (hω : 0 < ω) :
    ∃ ζ ω₀ q : ℝ, 0 < ζ ∧ ζ < 1 ∧ 0 < ω₀ ∧
      ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧ ω₀ < 1 ∧ ω₀ ≤ βₘ ∧ ω₀ ≤ ω ∧
      0 < q ∧ q < ω₀ ∧ q < 2 / (2 + γ) ^ 2 - ζ := by
  let a : ℝ := 2 / (2 + γ) ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by
    dsimp [a]
    rw [div_lt_one (by positivity)]
    nlinarith
  let b := min a (min βₘ (min ω 1))
  have hb : 0 < b := lt_min ha (lt_min hβₘ (lt_min hω zero_lt_one))
  have hba : b ≤ a := min_le_left _ _
  have hbβ : b ≤ βₘ := (min_le_right _ _).trans (min_le_left _ _)
  have hbω : b ≤ ω := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb1 : b ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨a / 2, b / 4, b / 8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [a] at * <;> linarith

/-- Restricting the admissible test radii to a smaller exponent preserves
the lower-radius bound from the logarithmic survival estimate. -/
theorem shell_survival_lower_radius_of_exponent_le
    {ε ω₀ ω r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hω : ω₀ ≤ ω)
    (hr : 10 * ε ^ ω₀ ≤ r) : 10 * ε ^ ω ≤ r := by
  have hpow := Real.rpow_le_rpow_of_exponent_ge hε hε1 hω
  linarith

end MatedCRT.Sec7
