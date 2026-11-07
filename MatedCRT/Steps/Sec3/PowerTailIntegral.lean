import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The tail-integral identity for positive moments, used in the mean-error estimate. -/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT

/-- Cavalieri's principle for an arbitrary positive real moment. -/
theorem lintegral_rpow_eq_lintegral_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (χ : ℝ) (hχ : 0 < χ)
    (hf : 0 ≤ᵐ[μ] f) (hfm : AEMeasurable f μ) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ χ) ∂μ =
      ∫⁻ t in Ioi 0, μ {ω | t < f ω} * ENNReal.ofReal (χ * t ^ (χ - 1)) := by
  have hi : ∀ t > 0, IntervalIntegrable (fun x : ℝ => χ * x ^ (χ - 1)) volume 0 t := by
    intro t ht
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < χ - 1)).const_mul χ
  have hp : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ χ * t ^ (χ - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hχ.le (Real.rpow_nonneg ht.le _)
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (∫ t in 0..f ω, χ * t ^ (χ - 1)) ∂μ := by
      apply lintegral_congr
      intro ω
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < χ - 1))]
      have hz : (0 : ℝ) ^ ((χ - 1) + 1) = 0 := by
        rw [sub_add_cancel, Real.zero_rpow (ne_of_gt hχ)]
      rw [hz]
      simp only [sub_zero, sub_add_cancel]
      congr 1
      field_simp
    _ = _ := lintegral_comp_eq_lintegral_meas_lt_mul μ hf hfm hi hp

end MatedCRT
