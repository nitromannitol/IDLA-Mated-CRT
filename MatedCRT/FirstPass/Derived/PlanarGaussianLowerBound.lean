import HarmonicBalls.Proofs.Brownian.PlanarHeatSemigroup
import MatedCRT.FirstPass.Derived.PlanarBrownianPointPolar

/-!
# A lower bound for the planar Gaussian law on a disc

The planar Gaussian law `planarGaussian z t` (mean `z`, covariance `t · I₂`, `t > 0`) has the density
`p_t(z, y) = (2πt)⁻¹ exp(-‖y − z‖² / (2t))`, which on the closed disc `closedBall 0 R` is bounded
below by `(2πt)⁻¹ exp(-(R + ‖z‖)² / t)`, since there each coordinate of `y − z` has absolute value at
most `R + ‖z‖`.  Hence `planarGaussian z t` dominates that multiple of Lebesgue measure restricted
to the disc (`smul_volume_restrict_closedBall_le_planarGaussian`), and the corresponding bound for
integrals of nonnegative functions holds (`lintegral_closedBall_le_lintegral_planarGaussian`).
With the simple Markov property at a fixed time `t`, the expectation `E_x[F ∘ θ_t]` of a path
functional `F ≥ 0` is at least the same multiple of `∫_{closedBall 0 R} E_y[F] dy`
(`ofReal_mul_setLIntegral_le_lintegral_shift`).
-/

open MeasureTheory ProbabilityTheory Set Metric Real MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open _root_.HarmonicBalls

/-- The one-dimensional Gaussian density `gaussianPDF m v` at a point `x` with `|x| ≤ R` is at least
`(2πv)^{-1/2} exp(-(R + M)² / (2v))` whenever `|m| ≤ M`. -/
theorem ofReal_le_gaussianPDF_of_abs_le {m : ℝ} {v : ℝ≥0} {x R M : ℝ} (hx : |x| ≤ R)
    (hm : |m| ≤ M) :
    ENNReal.ofReal ((√(2 * π * v))⁻¹ * Real.exp (-(R + M) ^ 2 / (2 * v))) ≤ gaussianPDF m v x := by
  rw [gaussianPDF, gaussianPDFReal]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity))
  have h2 : (x - m) ^ 2 ≤ (R + M) ^ 2 :=
    sq_le_sq' (by linarith [(abs_le.1 hx).1, (abs_le.1 hm).2])
      (by linarith [(abs_le.1 hx).2, (abs_le.1 hm).1])
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right h2 (by positivity)

/-- **Gaussian lower bound on a disc.** For `t ≠ 0` and a Borel set `G` inside `closedBall 0 R`,
`planarGaussian z t G ≥ (2πt)⁻¹ exp(-(R + ‖z‖)² / t) · Leb(G)`. -/
theorem ofReal_mul_volume_le_planarGaussian {z : ℂ} {t : ℝ≥0} (ht : t ≠ 0) {R : ℝ} {G : Set ℂ}
    (hG : MeasurableSet G) (hGR : G ⊆ closedBall 0 R) :
    ENNReal.ofReal ((2 * π * t)⁻¹ * Real.exp (-(R + ‖z‖) ^ 2 / t)) * volume G ≤
      planarGaussian z t G := by
  set a : ℝ≥0∞ := ENNReal.ofReal ((√(2 * π * t))⁻¹ * Real.exp (-(R + ‖z‖) ^ 2 / (2 * t)))
    with ha
  have hc : ENNReal.ofReal ((2 * π * t)⁻¹ * Real.exp (-(R + ‖z‖) ^ 2 / t)) = a * a := by
    rw [ha, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hpos : (0 : ℝ) ≤ 2 * π * t := by positivity
    calc (2 * π * t)⁻¹ * Real.exp (-(R + ‖z‖) ^ 2 / t)
        = ((√(2 * π * t))⁻¹ * (√(2 * π * t))⁻¹) *
            (Real.exp (-(R + ‖z‖) ^ 2 / (2 * t)) * Real.exp (-(R + ‖z‖) ^ 2 / (2 * t))) := by
          rw [← mul_inv, Real.mul_self_sqrt hpos, ← Real.exp_add]
          congr 2
          ring
      _ = _ := by ring
  have hP : MeasurableSet (Complex.measurableEquivRealProd.symm ⁻¹' G) :=
    Complex.measurableEquivRealProd.symm.measurable hG
  have hbound : ∀ p ∈ Complex.measurableEquivRealProd.symm ⁻¹' G,
      a * a ≤ gaussianPDF z.re t p.1 * gaussianPDF z.im t p.2 := by
    intro p hp
    have hn : ‖Complex.measurableEquivRealProd.symm p‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hGR hp
    have hre : |p.1| ≤ R := (Complex.abs_re_le_norm _).trans hn
    have him : |p.2| ≤ R := (Complex.abs_im_le_norm _).trans hn
    exact mul_le_mul' (ofReal_le_gaussianPDF_of_abs_le hre (Complex.abs_re_le_norm z))
      (ofReal_le_gaussianPDF_of_abs_le him (Complex.abs_im_le_norm z))
  rw [hc, planarGaussian, Measure.map_apply Complex.measurableEquivRealProd.symm.measurable hG,
    gaussianReal_of_var_ne_zero _ ht, gaussianReal_of_var_ne_zero _ ht,
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    withDensity_apply _ hP,
    ← (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage hG.nullMeasurableSet,
    ← setLIntegral_const]
  exact setLIntegral_mono' hP hbound

/-- **Gaussian lower bound, measure form.** For `t ≠ 0`, the planar Gaussian law `planarGaussian z t`
dominates `(2πt)⁻¹ exp(-(R + ‖z‖)² / t)` times Lebesgue measure restricted to `closedBall 0 R`. -/
theorem smul_volume_restrict_closedBall_le_planarGaussian {z : ℂ} {t : ℝ≥0} (ht : t ≠ 0) (R : ℝ) :
    ENNReal.ofReal ((2 * π * t)⁻¹ * Real.exp (-(R + ‖z‖) ^ 2 / t)) •
        (volume : Measure ℂ).restrict (closedBall 0 R) ≤ planarGaussian z t := by
  refine Measure.le_iff.2 fun G hG => ?_
  rw [Measure.smul_apply, Measure.restrict_apply hG, smul_eq_mul]
  exact (ofReal_mul_volume_le_planarGaussian ht (hG.inter measurableSet_closedBall)
    inter_subset_right).trans (measure_mono inter_subset_left)

/-- **Gaussian lower bound, integral form.** For `t ≠ 0` and every `φ ≥ 0`,
`(2πt)⁻¹ exp(-(R + ‖z‖)² / t) ∫_{closedBall 0 R} φ ≤ ∫ φ d(planarGaussian z t)`. -/
theorem lintegral_closedBall_le_lintegral_planarGaussian {z : ℂ} {t : ℝ≥0} (ht : t ≠ 0) (R : ℝ)
    (φ : ℂ → ℝ≥0∞) :
    ENNReal.ofReal ((2 * π * t)⁻¹ * Real.exp (-(R + ‖z‖) ^ 2 / t)) *
        ∫⁻ y in closedBall 0 R, φ y ≤ ∫⁻ y, φ y ∂planarGaussian z t := by
  have h := lintegral_mono' (smul_volume_restrict_closedBall_le_planarGaussian (z := z) ht R)
    (le_refl φ)
  rwa [lintegral_smul_measure, smul_eq_mul] at h

/-- **Markov property at a fixed time against a disc.** For `t ≠ 0`, every start `x`, radius `R` and
measurable path functional `F ≥ 0`,
`(2πt)⁻¹ exp(-(R + ‖x‖)² / t) ∫_{closedBall 0 R} E_y[F] dy ≤ E_x[F ∘ θ_t]`. -/
theorem ofReal_mul_setLIntegral_le_lintegral_shift (x : ℂ) {t : ℝ≥0} (ht : t ≠ 0) (R : ℝ)
    {F : ContinuousPath ℂ → ℝ≥0∞} (hF : Measurable F) :
    ENNReal.ofReal ((2 * π * t)⁻¹ * Real.exp (-(R + ‖x‖) ^ 2 / t)) *
        ∫⁻ y in closedBall 0 R, ∫⁻ ω, F ω ∂planarBrownianMotion y ≤
      ∫⁻ ω, F (ContinuousPath.shift t ω) ∂planarBrownianMotion x := by
  rw [← lintegral_map hF (ContinuousPath.continuous_shift_fixed t).measurable,
    KilledOccupation.planarBrownianMotion_map_shift x t,
    Measure.lintegral_bind planarBrownianMotion.measurable.aemeasurable hF.aemeasurable]
  exact lintegral_closedBall_le_lintegral_planarGaussian ht R _

end MatedCRT
