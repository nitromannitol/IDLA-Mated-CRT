import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Integral estimates for the three positive-moment regimes. -/

open MeasureTheory Set
open scoped Interval

namespace MatedCRT

/-- The integral appearing in a power-tail bound, away from the logarithmic regime. -/
theorem integral_power_tail {ℓ R χ ν : ℝ} (hℓ : 0 < ℓ) (hLR : ℓ ≤ R)
    (hne : χ ≠ ν) :
    (∫ s in ℓ..R, s ^ (χ - ν - 1)) =
      (R ^ (χ - ν) - ℓ ^ (χ - ν)) / (χ - ν) := by
  have hzero : (0 : ℝ) ∉ [[ℓ, R]] := by
    rw [uIcc_of_le hLR]
    exact fun h => not_le_of_gt hℓ h.1
  have h := integral_rpow (a := ℓ) (b := R) (r := χ - ν - 1)
    (Or.inr ⟨by intro he; apply hne; linarith, hzero⟩)
  simpa only [sub_add_cancel] using h

/-- At the critical exponent the power-tail integral is logarithmic. -/
theorem integral_power_tail_critical {ℓ R ν : ℝ} (hℓ : 0 < ℓ) (hLR : ℓ ≤ R) :
    (∫ s in ℓ..R, s ^ (ν - ν - 1)) = Real.log (R / ℓ) := by
  simp only [sub_self, zero_sub, Real.rpow_neg_one]
  exact integral_inv_of_pos hℓ (lt_of_lt_of_le hℓ hLR)

/-- When the moment exponent exceeds the tail exponent, the upper endpoint controls the integral. -/
theorem power_tail_integral_le_of_tail_lt_moment {ℓ R χ ν : ℝ}
    (hℓ : 0 < ℓ) (hLR : ℓ ≤ R) (h : ν < χ) :
    ℓ ^ ν * (∫ s in ℓ..R, s ^ (χ - ν - 1)) ≤
      ℓ ^ ν * R ^ (χ - ν) / (χ - ν) := by
  rw [integral_power_tail hℓ hLR (ne_of_gt h)]
  have hn : 0 ≤ ℓ ^ (χ - ν) := Real.rpow_nonneg hℓ.le _
  have hm : 0 ≤ ℓ ^ ν := Real.rpow_nonneg hℓ.le _
  have hd : 0 < χ - ν := sub_pos.mpr h
  have hi : (R ^ (χ - ν) - ℓ ^ (χ - ν)) / (χ - ν) ≤ R ^ (χ - ν) / (χ - ν) :=
    div_le_div_of_nonneg_right (sub_le_self _ hn) hd.le
  calc
    _ ≤ ℓ ^ ν * (R ^ (χ - ν) / (χ - ν)) := mul_le_mul_of_nonneg_left hi hm
    _ = _ := by ring

/-- When the moment exponent is below the tail exponent, the lower endpoint controls the integral. -/
theorem power_tail_integral_le_of_moment_lt_tail {ℓ R χ ν : ℝ}
    (hℓ : 0 < ℓ) (hLR : ℓ ≤ R) (h : χ < ν) :
    ℓ ^ ν * (∫ s in ℓ..R, s ^ (χ - ν - 1)) ≤
      ℓ ^ χ / (ν - χ) := by
  rw [integral_power_tail hℓ hLR (ne_of_lt h)]
  have hn : 0 ≤ R ^ (χ - ν) := Real.rpow_nonneg (le_trans hℓ.le hLR) _
  have hm : 0 ≤ ℓ ^ ν := Real.rpow_nonneg hℓ.le _
  have hd : 0 < ν - χ := sub_pos.mpr h
  have heq : (R ^ (χ - ν) - ℓ ^ (χ - ν)) / (χ - ν) =
      (ℓ ^ (χ - ν) - R ^ (χ - ν)) / (ν - χ) := by
    rw [show χ - ν = -(ν - χ) by ring, div_neg, ← neg_div, neg_sub]
  rw [heq]
  have hi : (ℓ ^ (χ - ν) - R ^ (χ - ν)) / (ν - χ) ≤ ℓ ^ (χ - ν) / (ν - χ) :=
    div_le_div_of_nonneg_right (sub_le_self _ hn) hd.le
  calc
    _ ≤ ℓ ^ ν * (ℓ ^ (χ - ν) / (ν - χ)) := mul_le_mul_of_nonneg_left hi hm
    _ = ℓ ^ χ / (ν - χ) := by
      rw [← mul_div_assoc, ← Real.rpow_add hℓ]
      congr 2; ring

end MatedCRT
