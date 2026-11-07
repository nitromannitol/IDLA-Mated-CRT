import MatedCRT.Steps.Sec3.PowerTailBounds

/-! Splitting an integrated tail at a mesoscopic scale. -/

open MeasureTheory Set
open scoped Interval

namespace MatedCRT

/-- Integrate a trivial small-scale tail bound and a polynomial large-scale tail bound. -/
theorem integral_weighted_tail_le {T : ℝ → ℝ} {ℓ R χ ν C : ℝ}
    (hℓ : 0 < ℓ) (hLR : ℓ ≤ R) (hχ : 0 < χ)
    (hsmall : ∀ s ∈ Ioo 0 ℓ, T s ≤ 1)
    (hlarge : ∀ s ∈ Ioo ℓ R, T s ≤ C * ℓ ^ ν * s ^ (-ν))
    (hi₁ : IntervalIntegrable (fun s => s ^ (χ - 1) * T s) volume 0 ℓ)
    (hi₂ : IntervalIntegrable (fun s => s ^ (χ - 1) * T s) volume ℓ R) :
    χ * (∫ s in 0..R, s ^ (χ - 1) * T s) ≤
      ℓ ^ χ + χ * C * (ℓ ^ ν * ∫ s in ℓ..R, s ^ (χ - ν - 1)) := by
  have hp : IntervalIntegrable (fun s : ℝ => s ^ (χ - 1)) volume 0 ℓ :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hz : (0 : ℝ) ∉ [[ℓ, R]] := by
    rw [uIcc_of_le hLR]
    exact fun h => not_le_of_gt hℓ h.1
  have hq : IntervalIntegrable (fun s : ℝ => s ^ (χ - ν - 1)) volume ℓ R :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hz)
  have hc : IntervalIntegrable (fun s : ℝ => (C * ℓ ^ ν) * s ^ (χ - ν - 1)) volume ℓ R :=
    hq.const_mul _
  have hs : (∫ s in 0..ℓ, s ^ (χ - 1) * T s) ≤ ∫ s in 0..ℓ, s ^ (χ - 1) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hℓ.le hi₁ hp
    intro s hs
    simpa using mul_le_mul_of_nonneg_left (hsmall s hs) (Real.rpow_nonneg hs.1.le _)
  have hl : (∫ s in ℓ..R, s ^ (χ - 1) * T s) ≤
      ∫ s in ℓ..R, (C * ℓ ^ ν) * s ^ (χ - ν - 1) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hLR hi₂ hc
    intro s hs
    have hspos : 0 < s := lt_trans hℓ hs.1
    calc
      _ ≤ s ^ (χ - 1) * (C * ℓ ^ ν * s ^ (-ν)) :=
        mul_le_mul_of_nonneg_left (hlarge s hs) (Real.rpow_nonneg hspos.le _)
      _ = (C * ℓ ^ ν) * (s ^ (χ - 1) * s ^ (-ν)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hspos]
        congr 2; ring
  have he : (∫ s in 0..ℓ, s ^ (χ - 1)) = ℓ ^ χ / χ := by
    rw [integral_rpow (Or.inl (by linarith : -1 < χ - 1))]
    simp [Real.zero_rpow (ne_of_gt hχ)]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂]
  rw [intervalIntegral.integral_const_mul] at hl
  rw [he] at hs
  have hk := mul_le_mul_of_nonneg_left (add_le_add hs hl) hχ.le
  have hn : χ ≠ 0 := ne_of_gt hχ
  calc
    _ ≤ χ * (ℓ ^ χ / χ + (C * ℓ ^ ν) * ∫ s in ℓ..R, s ^ (χ - ν - 1)) := hk
    _ = _ := by field_simp

end MatedCRT
