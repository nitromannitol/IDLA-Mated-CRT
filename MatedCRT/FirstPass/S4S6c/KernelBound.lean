import MatedCRT.FirstPass.S4S6c.CircleIntegrability

/-!
# Uniform bound on the corrected kernel over the good annulus (q2, task fp-S4S6c; LEMMA68 Lemma 1)

For `u` with `‖u - z‖ ≤ 2R` and `v = circleMap z (3R/2) θ`, the corrected kernel `K(u,v) = log(R/|u-v|) + 1` satisfies
`K ≥ -a₀` with `a₀ = log 4 - 1` (since `|u - v| ≤ 4R`), and its circle average is at most `log R + 1 - log(3R/2)`
(the closed form `circleAverage_kernel_eq` drops the nonnegative `log⁺` term). Consequently
`∫_{(0,2π]} |K(u, circleMap θ)| dθ ≤ 2π (log R + 1 - log(3R/2) + 2a₀)` uniformly in `u`: the integrable majorant used for
the joint integrability (`CircleIntegrability.lean`). Open: the product integrability itself and the Fubini assembly.
-/

open MeasureTheory Real Set Metric

namespace MatedCRT

/-- The distance of a point of the circle `∂B_t(z)` from its centre is `|t|`. -/
theorem norm_circleMap_sub_center' (z : ℂ) (t θ : ℝ) : ‖z - circleMap z t θ‖ = |t| := by
  simp [circleMap, Complex.norm_exp_ofReal_mul_I]

/-- `log 4 ≥ 1`, so that `a₀ = log 4 - 1 ≥ 0`. -/
theorem one_le_log_four : 1 ≤ Real.log 4 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have := Real.log_two_gt_d9
  linarith

/-- The kernel is bounded below on the annulus: `log(R/|u-v|) + 1 ≥ 1 - log 4` when `|u-v| ≤ 4R`. -/
theorem kernel_ge_neg {R : ℝ} {u v : ℂ} (huv : ‖u - v‖ ≤ 4 * R) :
    -(Real.log 4 - 1) ≤ Real.log (R / ‖u - v‖) + 1 := by
  rcases eq_or_ne ‖u - v‖ 0 with h0 | h0
  · rw [h0, div_zero, Real.log_zero]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith
  · have hpos : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have h4 : (1 / 4 : ℝ) ≤ R / ‖u - v‖ := by
      rw [le_div_iff₀ hpos]
      linarith
    have hl := Real.log_le_log (by norm_num) h4
    have hl4 : Real.log (1 / 4) = -Real.log 4 := by
      rw [one_div, Real.log_inv]
    linarith

/-- **Closed form of the circle average of the kernel** (the equality behind `circleAverage_kernel_ge_one_sub_log_two`). -/
theorem circleAverage_kernel_eq {z u : ℂ} {R : ℝ} (hR : 0 < R) :
    circleAverage (fun v : ℂ => Real.log (R / ‖u - v‖) + 1) z (3 * R / 2) =
      (Real.log R + 1) - (Real.log (3 * R / 2) + Real.posLog ((3 * R / 2)⁻¹ * ‖z - u‖)) := by
  have ht : (0 : ℝ) < 3 * R / 2 := by positivity
  have hEq : ∀ v : ℂ, v ≠ u →
      Real.log (R / ‖u - v‖) + 1 = (Real.log R + 1) - Real.log ‖v - u‖ := by
    intro v hv
    have huv : ‖u - v‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      exact hv.symm
    rw [Real.log_div hR.ne' huv, norm_sub_rev]
    ring
  rw [circleAverage_congr_of_ne (f := fun v : ℂ => Real.log (R / ‖u - v‖) + 1)
    (g := fun v : ℂ => (Real.log R + 1) - Real.log ‖v - u‖) ht.ne' hEq]
  have hsub : (fun v : ℂ => (Real.log R + 1) - Real.log ‖v - u‖) =
      (fun _ : ℂ => Real.log R + 1) - (fun v : ℂ => Real.log ‖v - u‖) := rfl
  rw [hsub, circleAverage_sub (circleIntegrable_const _ _ _) (circleIntegrable_log_norm_sub_const _),
    circleAverage_const, circleAverage_log_norm_sub_const_eq_log_radius_add_posLog ht.ne']

/-- The circle average of the kernel is at most `log R + 1 - log(3R/2)`. -/
theorem circleAverage_kernel_le {z u : ℂ} {R : ℝ} (hR : 0 < R) :
    circleAverage (fun v : ℂ => Real.log (R / ‖u - v‖) + 1) z (3 * R / 2) ≤
      (Real.log R + 1) - Real.log (3 * R / 2) := by
  rw [circleAverage_kernel_eq hR]
  have h0 : 0 ≤ Real.posLog ((3 * R / 2)⁻¹ * ‖z - u‖) := by
    unfold Real.posLog
    exact le_max_left _ _
  linarith

/-- The integral of the kernel over `(0, 2π]` is at most `2π (log R + 1 - log(3R/2))`. -/
theorem integral_kernel_Ioc_le {z u : ℂ} {R : ℝ} (hR : 0 < R) :
    ∫ θ in Ioc 0 (2 * π), (Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1) ≤
      2 * π * ((Real.log R + 1) - Real.log (3 * R / 2)) := by
  have hav := circleAverage_kernel_le (z := z) (u := u) hR
  simp only [circleAverage_def, smul_eq_mul] at hav
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)] at hav
  have hpi : (0 : ℝ) < 2 * π := by positivity
  calc ∫ θ in Ioc 0 (2 * π), (Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1)
      = 2 * π * ((2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), (Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul]
    _ ≤ 2 * π * ((Real.log R + 1) - Real.log (3 * R / 2)) := mul_le_mul_of_nonneg_left hav hpi.le

/-- **Uniform bound on the absolute kernel over the annulus.** For `‖u - z‖ ≤ 2R`,
`∫_{(0,2π]} |K(u, circleMap θ)| dθ ≤ 2π (log R + 1 - log(3R/2) + 2(log 4 - 1))`. -/
theorem integral_norm_kernel_le {z u : ℂ} {R : ℝ} (hR : 0 < R) (hu : ‖u - z‖ ≤ 2 * R) :
    ∫ θ in Ioc 0 (2 * π), ‖Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1‖ ≤
      2 * π * ((Real.log R + 1) - Real.log (3 * R / 2) + 2 * (Real.log 4 - 1)) := by
  have ht : (0 : ℝ) < 3 * R / 2 := by positivity
  have hint : IntegrableOn (fun θ : ℝ => Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1)
      (Ioc 0 (2 * π)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)).1
      (intervalIntegrable_kernel_slice (u := u) (z := z) (R := R) hR ht.ne')
  have hpt : ∀ θ ∈ Ioc (0 : ℝ) (2 * π),
      ‖Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1‖ ≤
        (Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1) + 2 * (Real.log 4 - 1) := by
    intro θ _
    have hz : ‖z - circleMap z (3 * R / 2) θ‖ = 3 * R / 2 := by
      rw [norm_circleMap_sub_center', abs_of_pos ht]
    have hdist : ‖u - circleMap z (3 * R / 2) θ‖ ≤ 4 * R := by
      have h1 : u - circleMap z (3 * R / 2) θ = (u - z) + (z - circleMap z (3 * R / 2) θ) := by ring
      have h2 := norm_add_le (u - z) (z - circleMap z (3 * R / 2) θ)
      rw [h1]
      linarith [h2, hu, hz]
    have hk := kernel_ge_neg hdist
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [one_le_log_four]
  have hconst : IntegrableOn (fun _ : ℝ => 2 * (Real.log 4 - 1)) (Ioc 0 (2 * π)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  calc ∫ θ in Ioc 0 (2 * π), ‖Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1‖
      ≤ ∫ θ in Ioc 0 (2 * π),
          ((Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1) + 2 * (Real.log 4 - 1)) :=
        setIntegral_mono_on hint.norm (hint.add hconst) measurableSet_Ioc hpt
    _ = (∫ θ in Ioc 0 (2 * π), (Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1))
          + 2 * (Real.log 4 - 1) * (2 * π) := by
        rw [integral_add hint hconst, setIntegral_const,
          Real.volume_real_Ioc_of_le (show (0 : ℝ) ≤ 2 * π by positivity), smul_eq_mul]
        ring
    _ ≤ 2 * π * ((Real.log R + 1) - Real.log (3 * R / 2)) + 2 * (Real.log 4 - 1) * (2 * π) := by
        linarith [integral_kernel_Ioc_le (z := z) (u := u) hR]
    _ = 2 * π * ((Real.log R + 1) - Real.log (3 * R / 2) + 2 * (Real.log 4 - 1)) := by ring

end MatedCRT
