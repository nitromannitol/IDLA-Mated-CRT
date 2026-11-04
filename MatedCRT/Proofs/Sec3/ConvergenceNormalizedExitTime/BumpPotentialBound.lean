import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GreenDomainMonotone
import MatedCRT.Defs.Setting

/-! A local Green potential is bounded by the largest-exit-time random variable. -/

open Set Metric MeasureTheory

namespace MatedCRT

/-- A bounded nonnegative source supported near the pole has Green potential
bounded by the logarithmic largest-exit-time kernel. -/
theorem lintegral_green_mul_bump_le_largestExitTimeRV
    (μ : Measure ℂ) {O : Set ℂ} {x : ℂ} {δ : ℝ} (φ : ℂ → ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hO : O ⊆ closedBall x 2) (hx : x ∈ O)
    (hφ1 : ∀ w, φ w ≤ 1) :
    (∫⁻ w in ball x δ, ENNReal.ofReal (HarmonicBalls.greenFunction O x w * φ w) ∂μ) ≤
      largestExitTimeRV μ (ball x δ) := by
  have hObdd : Bornology.IsBounded O := (isBounded_closedBall :
    Bornology.IsBounded (closedBall x (2 : ℝ))).subset hO
  calc
    (∫⁻ w in ball x δ, ENNReal.ofReal (HarmonicBalls.greenFunction O x w * φ w) ∂μ) ≤
        ∫⁻ w in ball x δ, ENNReal.ofReal (Real.log (1 / ‖x - w‖) + 1) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
      by_cases hxw : x = w
      · subst w
        simp [HarmonicBalls.greenFunction_self]
      by_cases hwO : w ∈ O
      · apply ENNReal.ofReal_le_ofReal
        have hd : ‖x - w‖ ≤ 1 := by
          have hw' : ‖w - x‖ < δ := by simpa [mem_ball, dist_eq_norm] using hw
          rw [norm_sub_rev]
          exact (le_of_lt hw').trans hδ1
        exact (mul_le_of_le_one_right (HarmonicBalls.greenFunction_nonneg hObdd x w)
          (hφ1 w)).trans (HarmonicBalls.greenFunction_le_exitTimeKernel hO hx hwO hxw hd)
      · simp [HarmonicBalls.greenFunction_of_notMem_right hwO]
    _ ≤ largestExitTimeRV μ (ball x δ) := by
      unfold largestExitTimeRV
      exact le_iSup_of_le x (le_iSup_of_le (mem_ball_self hδ) le_rfl)

/-- The same estimate for a source vanishing outside the small ball. -/
theorem lintegral_green_mul_bump_le_largestExitTimeRV_of_support
    (μ : Measure ℂ) {O : Set ℂ} {x : ℂ} {δ : ℝ} (φ : ℂ → ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hO : O ⊆ closedBall x 2) (hx : x ∈ O)
    (hφ1 : ∀ w, φ w ≤ 1) (hsupp : ∀ w ∉ ball x δ, φ w = 0) :
    (∫⁻ w, ENNReal.ofReal (HarmonicBalls.greenFunction O x w * φ w) ∂μ) ≤
      largestExitTimeRV μ (ball x δ) := by
  have heq : (fun w => ENNReal.ofReal (HarmonicBalls.greenFunction O x w * φ w)) =
      (ball x δ).indicator (fun w => ENNReal.ofReal (HarmonicBalls.greenFunction O x w * φ w)) := by
    funext w
    by_cases hw : w ∈ ball x δ
    · simp [hw]
    · simp [hw, hsupp w hw]
  rw [heq, lintegral_indicator measurableSet_ball]
  exact lintegral_green_mul_bump_le_largestExitTimeRV μ φ hδ hδ1 hO hx hφ1

/-- The real Green potential of a nonnegative small-ball source obeys the
same estimate, expressed in extended nonnegative reals. -/
theorem ofReal_integral_green_mul_bump_le_largestExitTimeRV
    (μ : Measure ℂ) {O : Set ℂ} {x : ℂ} {δ : ℝ} (φ : ℂ → ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hO : O ⊆ closedBall x 2) (hx : x ∈ O)
    (hφ0 : ∀ w, 0 ≤ φ w) (hφ1 : ∀ w, φ w ≤ 1)
    (hsupp : ∀ w ∉ ball x δ, φ w = 0) :
    ENNReal.ofReal (∫ w, HarmonicBalls.greenFunction O x w * φ w ∂μ) ≤
      largestExitTimeRV μ (ball x δ) := by
  by_cases hint : Integrable (fun w => HarmonicBalls.greenFunction O x w * φ w) μ
  · rw [ofReal_integral_eq_lintegral_ofReal hint]
    · exact lintegral_green_mul_bump_le_largestExitTimeRV_of_support μ φ hδ hδ1 hO hx hφ1 hsupp
    · exact ae_of_all _ fun w => mul_nonneg
        (HarmonicBalls.greenFunction_nonneg (isBounded_closedBall.subset hO) x w) (hφ0 w)
  · simp [integral_undef hint]

/-- Finiteness of the largest-exit-time quantity supplies the local
integrability of a measurable Green kernel at its pole. -/
theorem green_integrableOn_small_ball_of_largestExitTimeRV
    (μ : Measure ℂ) {O : Set ℂ} {x : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hO : O ⊆ closedBall x 2) (hx : x ∈ O)
    (hsm : AEStronglyMeasurable (HarmonicBalls.greenFunction O x) (μ.restrict (ball x δ)))
    (hM : largestExitTimeRV μ (ball x δ) < ⊤) :
    IntegrableOn (HarmonicBalls.greenFunction O x) (ball x δ) μ := by
  have hnonneg : 0 ≤ᵐ[μ.restrict (ball x δ)] HarmonicBalls.greenFunction O x :=
    ae_of_all _ (HarmonicBalls.greenFunction_nonneg (isBounded_closedBall.subset hO) x)
  have hbound := lintegral_green_mul_bump_le_largestExitTimeRV μ (fun _ => 1)
    hδ hδ1 hO hx (fun _ => le_rfl)
  have hfinite : (∫⁻ w in ball x δ, ENNReal.ofReal (HarmonicBalls.greenFunction O x w) ∂μ) < ⊤ := by
    simpa only [mul_one] using hbound.trans_lt hM
  exact ⟨hsm, (hasFiniteIntegral_iff_ofReal hnonneg).2 hfinite⟩

end MatedCRT
