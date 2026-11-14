import HarmonicBalls.Proofs.Sec6.BrownianScaling
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockFinite

/-!
# Small-ball bounds for Brownian increments

For `u ≠ v`, the increment `B_v - B_u` of real Brownian motion is a centred Gaussian of variance `|v - u|`, whose
density is at most `(2 π |v - u|)^{-1/2}`; hence `P_x(|B_v - B_u| < a) ≤ 2 a / √(2 π |v - u|)`. For planar Brownian
motion the real and imaginary parts are independent, and `‖w‖ < a` forces `|Re w| < a` and `|Im w| < a`, so
`P_y(‖B_v - B_u‖ < a) ≤ (2 a / √(2 π |v - u|))² ≤ a² / |v - u|`.
-/

open MeasureTheory Set MarkovProcess ProbabilityTheory HarmonicBalls HarmonicBalls.Section6
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

theorem measurable_path_increment (u v : ℝ≥0) :
    Measurable (fun p : ContinuousPath ℝ => p v - p u) :=
  (ContinuousPath.measurable_coordinateProcess _).sub (ContinuousPath.measurable_coordinateProcess _)

/-- **Small-ball bound for a real Brownian increment.** For `u ≠ v`,
`P_x(-a < B_v - B_u < a) ≤ (2 π |v - u|)^{-1/2} · 2a`. -/
theorem brownianMotion_increment_mem_Ioo_le (x : ℝ) {u v : ℝ≥0} (huv : u ≠ v) (a : ℝ) :
    brownianMotion x ((fun p : ContinuousPath ℝ => p v - p u) ⁻¹' Ioo (-a) a) ≤
      ENNReal.ofReal ((√(2 * Real.pi * |(v : ℝ) - u|))⁻¹ * (2 * a)) := by
  have h := (isPreBrownianReal_brownianMotion x).hasLaw_sub v u
  change HasLaw (fun p : ContinuousPath ℝ => (p v - x) - (p u - x)) _ _ at h
  simp only [sub_sub_sub_cancel_right] at h
  have hvu : (v : ℝ) ≠ u := fun e => huv (NNReal.coe_injective e).symm
  have hT : nndist (v : ℝ) (u : ℝ) ≠ 0 := fun e => hvu (nndist_eq_zero.mp e)
  rw [← Measure.map_apply (measurable_path_increment u v) measurableSet_Ioo, h.map_eq]
  refine (gaussianReal_Ioo_le_inv_sqrt 0 hT (-a) a).trans_eq ?_
  rw [coe_nndist, Real.dist_eq]
  ring_nf

/-- **Small-ball bound for a planar Brownian increment** (product form). For `u ≠ v`,
`P_y(‖B_v - B_u‖ < a) ≤ ((2 π |v - u|)^{-1/2} · 2a)²`. -/
theorem planarBrownianMotion_norm_increment_lt_le_sq (y : ℂ) {u v : ℝ≥0} (huv : u ≠ v) (a : ℝ) :
    planarBrownianMotion y {b : ContinuousPath ℂ | ‖b v - b u‖ < a} ≤
      ENNReal.ofReal ((√(2 * Real.pi * |(v : ℝ) - u|))⁻¹ * (2 * a)) ^ 2 := by
  set A : Set (ContinuousPath ℝ) := (fun p : ContinuousPath ℝ => p v - p u) ⁻¹' Ioo (-a) a with hA
  have hAm : MeasurableSet A := measurable_path_increment u v measurableSet_Ioo
  have hsub : {b : ContinuousPath ℂ | ‖b v - b u‖ < a} ⊆ reImPath ⁻¹' (A ×ˢ A) := by
    intro b hb
    have hb' : ‖b v - b u‖ < a := hb
    have hre := (Complex.abs_re_le_norm (b v - b u)).trans_lt hb'
    have him := (Complex.abs_im_le_norm (b v - b u)).trans_lt hb'
    rw [Complex.sub_re] at hre
    rw [Complex.sub_im] at him
    simp only [hA, mem_preimage, mem_prod, reImPath_fst_apply, reImPath_snd_apply, mem_Ioo]
    exact ⟨abs_lt.mp hre, abs_lt.mp him⟩
  calc planarBrownianMotion y {b : ContinuousPath ℂ | ‖b v - b u‖ < a}
      ≤ planarBrownianMotion y (reImPath ⁻¹' (A ×ˢ A)) := measure_mono hsub
    _ = brownianMotion y.re A * brownianMotion y.im A := by
        rw [← Measure.map_apply measurable_reImPath (hAm.prod hAm), planarBrownianMotion_map_reImPath,
          Measure.prod_prod]
    _ ≤ _ := by
        rw [sq]
        exact mul_le_mul' (brownianMotion_increment_mem_Ioo_le _ huv a)
          (brownianMotion_increment_mem_Ioo_le _ huv a)

/-- **Small-ball bound for a planar Brownian increment.** For `u ≠ v` and `0 ≤ a`,
`P_y(‖B_v - B_u‖ < a) ≤ a² / |v - u|`. -/
theorem planarBrownianMotion_norm_increment_lt_le (y : ℂ) {u v : ℝ≥0} (huv : u ≠ v) {a : ℝ}
    (ha : 0 ≤ a) :
    planarBrownianMotion y {b : ContinuousPath ℂ | ‖b v - b u‖ < a} ≤
      ENNReal.ofReal (a ^ 2 / |(v : ℝ) - u|) := by
  refine (planarBrownianMotion_norm_increment_lt_le_sq y huv a).trans ?_
  have hvu : (v : ℝ) ≠ u := fun e => huv (NNReal.coe_injective e).symm
  have hT : 0 < |(v : ℝ) - u| := abs_pos.mpr (sub_ne_zero.mpr hvu)
  rw [← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpi : 2 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  have heq : ((√(2 * Real.pi * |(v : ℝ) - u|))⁻¹ * (2 * a)) ^ 2 =
      2 / Real.pi * (a ^ 2 / |(v : ℝ) - u|) := by
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [heq]
  calc 2 / Real.pi * (a ^ 2 / |(v : ℝ) - u|) ≤ 1 * (a ^ 2 / |(v : ℝ) - u|) :=
        mul_le_mul_of_nonneg_right hpi (by positivity)
    _ = a ^ 2 / |(v : ℝ) - u| := one_mul _

end MatedCRT.KilledOccupation
