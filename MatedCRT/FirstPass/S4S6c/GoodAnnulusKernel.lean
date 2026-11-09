import Mathlib

/-!
# Lemma 1 of the Lemma 6.8 argument: pointwise circle average of the corrected kernel (q2, task fp-S4S6c)

Source: `notes/fp-gaps/LEMMA68.md`, "Lemma 1 (what the corrected good event controls)", lines 91-143, the first display of
the proof: averaging `v ↦ log(R/|u-v|) + 1` over the circle `v = z + (3R/2) e^{iθ}` gives at least
`κ₀ = 1 - log 2 > 0` for every `u` with `|u - z| ≤ 2R`. Here `u` off the circle `|u - z| = 3R/2` is treated; the
single exceptional case `|u - z| = 3R/2` (where the kernel has its integrable singularity at one point of the circle) is
NOT yet covered, and is recorded in the round report.

Mathlib input: `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`
(Mathlib/Analysis/SpecialFunctions/Integrals/PosLogEqCircleAverage.lean:205).
-/

open MeasureTheory Real

namespace MatedCRT

/-- **Pointwise circle average of the corrected kernel.** For `u` in the closed annulus `|u - z| ≤ 2R`, off the circle
`|u - z| = 3R/2`, the circle average of `v ↦ log(R/|u-v|) + 1` over `∂B_{3R/2}(z)` is at least `1 - log 2`. -/
theorem circleAverage_kernel_ge_one_sub_log_two {z u : ℂ} {R : ℝ} (hR : 0 < R) (hu : ‖u - z‖ ≤ 2 * R)
    (hne : ‖u - z‖ ≠ 3 * R / 2) :
    1 - Real.log 2 ≤ circleAverage (fun v : ℂ => Real.log (R / ‖u - v‖) + 1) z (3 * R / 2) := by
  have ht : (0 : ℝ) < 3 * R / 2 := by positivity
  have hEq : Set.EqOn (fun v : ℂ => Real.log (R / ‖u - v‖) + 1)
      (fun v : ℂ => (Real.log R + 1) - Real.log ‖v - u‖) (Metric.sphere z |3 * R / 2|) := by
    intro v hv
    rw [Metric.mem_sphere, dist_eq_norm, abs_of_pos ht] at hv
    have hvu : ‖v - u‖ ≠ 0 := by
      intro h0
      apply hne
      have hv' : v = u := sub_eq_zero.mp (norm_eq_zero.mp h0)
      rw [← hv']
      exact hv
    have huv : ‖u - v‖ ≠ 0 := by rwa [norm_sub_rev]
    show Real.log (R / ‖u - v‖) + 1 = (Real.log R + 1) - Real.log ‖v - u‖
    rw [Real.log_div hR.ne' huv, norm_sub_rev]
    ring
  rw [circleAverage_congr_sphere hEq]
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
