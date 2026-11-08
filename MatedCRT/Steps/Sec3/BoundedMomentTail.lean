import MatedCRT.Steps.Sec3.PowerTailIntegral
import MatedCRT.Steps.Sec3.ProbabilityTailIntegrable

/-! Layer-cake formula on a bounded interval. -/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT

/-- A bounded nonnegative random variable has its positive moment equal to the
integral of its weighted upper tail up to the bound. -/
theorem integral_rpow_eq_integral_probability_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) {χ R : ℝ}
    (hχ : 0 < χ) (hR : 0 ≤ R) (hf : 0 ≤ᵐ[μ] f)
    (hbound : ∀ᵐ ω ∂μ, f ω ≤ R) (hfm : AEMeasurable f μ) :
    (∫ ω, f ω ^ χ ∂μ) =
      χ * ∫ t in 0..R, t ^ (χ - 1) * μ.real {ω | t < f ω} := by
  have hint : Integrable (fun ω => f ω ^ χ) μ := by
    apply (integrable_const (R ^ χ)).mono'
      ((Real.continuous_rpow_const hχ.le).measurable.comp_aemeasurable hfm).aestronglyMeasurable
    filter_upwards [hf, hbound] with ω hω hωR
    change ‖f ω ^ χ‖ ≤ R ^ χ
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hω χ)]
    exact Real.rpow_le_rpow hω hωR hχ.le
  have hzero : ∀ t : ℝ, R ≤ t → μ {ω | t < f ω} = 0 := by
    intro t ht
    apply measure_mono_null (t := {ω | ¬ f ω ≤ R})
    · intro ω hω
      exact not_le_of_gt (lt_of_le_of_lt ht hω)
    · rw [measure_eq_zero_iff_ae_notMem]
      simpa using hbound
  let g : ℝ → ℝ≥0∞ := fun t => μ {ω | t < f ω} * ENNReal.ofReal (χ * t ^ (χ - 1))
  have hcut : (∫⁻ t in Ioi (0 : ℝ), g t) = ∫⁻ t in Ioc 0 R, g t := by
    have h := lintegral_inter_add_sdiff (μ := volume) g (Ioi (0 : ℝ)) (show MeasurableSet (Ioc (0 : ℝ) R) from measurableSet_Ioc)
    have hinter : Ioi (0 : ℝ) ∩ Ioc 0 R = Ioc 0 R := inter_eq_right.mpr Ioc_subset_Ioi_self
    rw [hinter] at h
    have hz : (∫⁻ t in Ioi (0 : ℝ) \ Ioc 0 R, g t) = 0 := by
      apply setLIntegral_eq_zero (measurableSet_Ioi.diff measurableSet_Ioc)
      intro t ht
      have htR : R ≤ t := by simp only [mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at ht; exact le_of_lt (ht.2 ht.1)
      simp only [g, hzero t htR, zero_mul, Pi.zero_apply]
    simpa only [hz, add_zero] using h.symm
  have hnonneg : 0 ≤ᵐ[μ] (fun ω => f ω ^ χ) := by
    filter_upwards [hf] with ω hω
    exact Real.rpow_nonneg hω χ
  have hi := (intervalIntegrable_probability_tail μ f le_rfl hR hχ).const_mul χ
  have hp : 0 ≤ᵐ[volume.restrict (Ioc 0 R)]
      (fun t : ℝ => χ * (t ^ (χ - 1) * μ.real {ω | t < f ω})) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg hχ.le (mul_nonneg (Real.rpow_nonneg ht.1.le _) measureReal_nonneg)
  have heq : (∫⁻ t in Ioc (0 : ℝ) R, g t) =
      ENNReal.ofReal (χ * ∫ t in 0..R, t ^ (χ - 1) * μ.real {ω | t < f ω}) := by
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hR,
      ofReal_integral_eq_lintegral_ofReal hi.1 hp]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change g t = ENNReal.ofReal (χ * (t ^ (χ - 1) * μ.real {ω | t < f ω}))
    rw [← mul_assoc, ENNReal.ofReal_mul (mul_nonneg hχ.le (Real.rpow_nonneg ht.1.le _)),
      measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
    simp only [g]
    ac_rfl
  have hright : 0 ≤ χ * ∫ t in 0..R, t ^ (χ - 1) * μ.real {ω | t < f ω} := by
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hR]
    exact integral_nonneg_of_ae hp
  apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hnonneg) hright).mp
  rw [ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    lintegral_rpow_eq_lintegral_tail μ f χ hχ hf hfm]
  change (∫⁻ t in Ioi (0 : ℝ), g t) = _
  rw [hcut]
  exact heq

end MatedCRT

#print axioms MatedCRT.integral_rpow_eq_integral_probability_tail
