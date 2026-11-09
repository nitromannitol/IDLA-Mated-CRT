import Mathlib

/-!
# Lemma 1 of the Lemma 6.8 argument: pointwise circle average of the corrected kernel (q2, task fp-S4S6c)

Source: `notes/fp-gaps/LEMMA68.md`, "Lemma 1 (what the corrected good event controls)", lines 91-143, the first display of
the proof: averaging `v ↦ log(R/|u-v|) + 1` over the circle `v = z + (3R/2) e^{iθ}` gives at least `κ₀ = 1 - log 2 > 0`
for every `u` with `|u - z| ≤ 2R`, including `u` on that circle. The single point `v = u` of the circle, where the kernel
is singular, is a null set of the parameter `θ` (the parametrization is injective on a period), so it does not affect the
circle average (`circleAverage_congr_of_ne`).

Mathlib inputs: `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`
(Mathlib/Analysis/SpecialFunctions/Integrals/PosLogEqCircleAverage.lean:205), `injOn_circleMap_of_abs_sub_le`
(Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean:168).
-/

open MeasureTheory Real

namespace MatedCRT

/-- A circle average does not see the value of the integrand at one point `u` of the circle. -/
theorem circleAverage_congr_of_ne {f g : ℂ → ℝ} {z u : ℂ} {t : ℝ} (ht : t ≠ 0)
    (h : ∀ v : ℂ, v ≠ u → f v = g v) :
    circleAverage f z t = circleAverage g z t := by
  simp only [circleAverage_def]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have hnull : volume {θ : ℝ | θ ∈ Set.uIoc 0 (2 * π) ∧ circleMap z t θ = u} = 0 := by
    apply Set.Subsingleton.measure_zero _ volume
    intro a ha b hb
    exact injOn_circleMap_of_abs_sub_le ht (by rw [zero_sub, abs_neg, abs_of_pos (by positivity)])
      ha.1 hb.1 (ha.2.trans hb.2.symm)
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro θ hθ
  simp only [Set.mem_ofPred_eq, not_imp] at hθ
  exact ⟨hθ.1, by by_contra hc; exact hθ.2 (h _ hc)⟩

/-- **Pointwise circle average of the corrected kernel.** For `u` in the closed annulus `|u - z| ≤ 2R`, the circle average
of `v ↦ log(R/|u-v|) + 1` over `∂B_{3R/2}(z)` is at least `1 - log 2`. -/
theorem circleAverage_kernel_ge_one_sub_log_two {z u : ℂ} {R : ℝ} (hR : 0 < R) (hu : ‖u - z‖ ≤ 2 * R) :
    1 - Real.log 2 ≤ circleAverage (fun v : ℂ => Real.log (R / ‖u - v‖) + 1) z (3 * R / 2) := by
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
  -- the ratio `s = (3R/2)⁻¹ ‖z - u‖` is at most `4/3`
  have hzu : ‖z - u‖ ≤ 2 * R := by rw [norm_sub_rev]; exact hu
  have hs : (3 * R / 2)⁻¹ * ‖z - u‖ ≤ 4 / 3 := by
    calc (3 * R / 2)⁻¹ * ‖z - u‖ ≤ (3 * R / 2)⁻¹ * (2 * R) :=
          mul_le_mul_of_nonneg_left hzu (by positivity)
      _ = 4 / 3 := by field_simp; ring
  have hs0 : 0 ≤ (3 * R / 2)⁻¹ * ‖z - u‖ := by positivity
  have h43 : Real.posLog (4 / 3) = Real.log (4 / 3) := by
    unfold Real.posLog
    exact max_eq_right (Real.log_nonneg (by norm_num))
  have hpl : Real.posLog ((3 * R / 2)⁻¹ * ‖z - u‖) ≤ Real.log (4 / 3) := by
    calc Real.posLog ((3 * R / 2)⁻¹ * ‖z - u‖) ≤ Real.posLog (4 / 3) :=
          Real.posLog_le_posLog (by linarith) hs
      _ = Real.log (4 / 3) := h43
  have hlog2 : Real.log (3 / 2) + Real.log (4 / 3) = Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hlogt : Real.log (3 * R / 2) = Real.log R + Real.log (3 / 2) := by
    have h32 : 3 * R / 2 = R * (3 / 2) := by ring
    rw [h32, Real.log_mul hR.ne' (by norm_num)]
  linarith [hpl, hlog2, hlogt]

end MatedCRT
