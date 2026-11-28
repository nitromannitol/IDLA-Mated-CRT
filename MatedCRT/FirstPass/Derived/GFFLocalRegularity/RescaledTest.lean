import Mathlib

/-!
# Rescaled test functions and the pairing of a Hölder field with their gradient

For a smooth `η : ℂ → ℝ` supported in the unit disc with `‖Dη‖ ≤ 1`, the rescaled test function
`v = t⁻² η((· − x)/t)` (`rescaledTest η x t`) is smooth, supported in `B(x, t)`, and its derivative is at most
`t⁻³` in norm. The integral of each directional derivative of a smooth compactly supported function vanishes
(integration by parts against the constant `1`), so for a field `Y` that is `β`-Hölder with constant `M` on a set
containing `B(x, t)`,
`|Σᵢ ∫ Yᵢ ∂_{eᵢ} v| = |Σᵢ ∫ (Yᵢ(y) − Yᵢ(x)) ∂_{eᵢ} v(y) dy| ≤ 2 M t^β · π t² · sup ‖Dv‖`
for two unit vectors `e₀, e₁`. These are the deterministic estimates of the last step of the proof of
`MatedCRT.ZeroBoundaryGFFLocalRegularity`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace MatedCRT.GFFLocalRegularity

/-- The rescaled test function `t⁻² η((· − x)/t)`. -/
def rescaledTest (η : ℂ → ℝ) (x : ℂ) (t : ℝ) : ℂ → ℝ :=
  fun y => (t ^ 2)⁻¹ * η ((y - x) / (t : ℂ))

/-- The affine change of variables of `rescaledTest`, written with a real scalar. -/
lemma sub_div_ofReal_eq_smul (x y : ℂ) (t : ℝ) : (y - x) / (t : ℂ) = t⁻¹ • (y - x) := by
  rw [Complex.real_smul, div_eq_inv_mul, Complex.ofReal_inv]

/-- A rescaled smooth function is smooth. -/
theorem contDiff_rescaledTest {η : ℂ → ℝ} {n : WithTop ℕ∞} (hη : ContDiff ℝ n η) (x : ℂ) (t : ℝ) :
    ContDiff ℝ n (rescaledTest η x t) :=
  contDiff_const.mul (hη.comp ((contDiff_id.sub contDiff_const).div_const (t : ℂ)))

/-- A function supported in the unit disc, rescaled at `(x, t)`, is supported in `B(x, t)`. -/
theorem tsupport_rescaledTest_subset {η : ℂ → ℝ} (hsupp : tsupport η ⊆ ball 0 1)
    (x : ℂ) {t : ℝ} (ht : 0 < t) : tsupport (rescaledTest η x t) ⊆ ball x t := by
  have hA : Continuous fun y : ℂ => (y - x) / (t : ℂ) := (continuous_id.sub continuous_const).div_const _
  have h1 : tsupport (rescaledTest η x t) ⊆ tsupport (η ∘ fun y : ℂ => (y - x) / (t : ℂ)) :=
    tsupport_mul_subset_right
  refine h1.trans ((tsupport_comp_subset_preimage η hA).trans ?_)
  intro y hy
  have hy' := hsupp hy
  rw [mem_ball, dist_zero_right, norm_div, Complex.norm_real, Real.norm_of_nonneg ht.le,
    div_lt_one ht] at hy'
  rwa [mem_ball, dist_eq_norm]

/-- A rescaled test function has compact support. -/
theorem hasCompactSupport_rescaledTest {η : ℂ → ℝ} (hsupp : tsupport η ⊆ ball 0 1)
    (x : ℂ) {t : ℝ} (ht : 0 < t) : HasCompactSupport (rescaledTest η x t) :=
  (isCompact_closedBall x t).of_isClosed_subset (isClosed_tsupport _)
    ((tsupport_rescaledTest_subset hsupp x ht).trans ball_subset_closedBall)

/-- The derivative of a rescaled test function at scale `t` is at most `t⁻³` in norm. -/
theorem norm_fderiv_rescaledTest_le {η : ℂ → ℝ} (hη : Differentiable ℝ η)
    (hgrad : ∀ z, ‖fderiv ℝ η z‖ ≤ 1) (x : ℂ) {t : ℝ} (ht : 0 < t) (y : ℂ) :
    ‖fderiv ℝ (rescaledTest η x t) y‖ ≤ (t ^ 3)⁻¹ := by
  have hA : HasFDerivAt (fun y : ℂ => t⁻¹ • (y - x)) (t⁻¹ • ContinuousLinearMap.id ℝ ℂ) y :=
    ((hasFDerivAt_id y).sub_const x).const_smul t⁻¹
  have hfun : rescaledTest η x t = fun y => (t ^ 2)⁻¹ * η (t⁻¹ • (y - x)) := by
    funext y
    rw [rescaledTest, sub_div_ofReal_eq_smul]
  have hD : HasFDerivAt (rescaledTest η x t)
      ((t ^ 2)⁻¹ • ((fderiv ℝ η (t⁻¹ • (y - x))).comp (t⁻¹ • ContinuousLinearMap.id ℝ ℂ))) y := by
    rw [hfun]
    exact (((hη _).hasFDerivAt).comp y hA).const_mul _
  rw [hD.fderiv]
  calc ‖(t ^ 2)⁻¹ • ((fderiv ℝ η (t⁻¹ • (y - x))).comp (t⁻¹ • ContinuousLinearMap.id ℝ ℂ))‖
      ≤ ‖(t ^ 2)⁻¹‖ * (‖fderiv ℝ η (t⁻¹ • (y - x))‖ * ‖t⁻¹ • ContinuousLinearMap.id ℝ ℂ‖) := by
        refine (norm_smul_le ((t ^ 2)⁻¹)
          ((fderiv ℝ η (t⁻¹ • (y - x))).comp (t⁻¹ • ContinuousLinearMap.id ℝ ℂ))).trans ?_
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (t ^ 2)⁻¹ * (1 * t⁻¹) := by
        have h1 : ‖(t ^ 2)⁻¹‖ = (t ^ 2)⁻¹ := Real.norm_of_nonneg (by positivity)
        have h2 : ‖t⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ ≤ t⁻¹ := by
          refine (norm_smul_le t⁻¹ (ContinuousLinearMap.id ℝ ℂ)).trans ?_
          rw [Real.norm_of_nonneg (inv_nonneg.2 ht.le)]
          exact mul_le_of_le_one_right (inv_nonneg.2 ht.le) ContinuousLinearMap.norm_id_le
        rw [h1]
        gcongr
        · exact hgrad _
    _ = (t ^ 3)⁻¹ := by
        rw [one_mul, ← mul_inv, ← pow_succ]

/-- The integral of a directional derivative of a smooth compactly supported function vanishes. -/
theorem integral_fderiv_apply_eq_zero {v : ℂ → ℝ} (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) (e : ℂ) :
    ∫ y, fderiv ℝ v y e = 0 := by
  have hcont : Continuous fun y => fderiv ℝ v y e :=
    (hv.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsupp : HasCompactSupport fun y => fderiv ℝ v y e := hvc.fderiv_apply (𝕜 := ℝ) e
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := e)
    (f := fun _ : ℂ => (1 : ℝ)) (g := v)
    (by simp) (by simpa using hcont.integrable_of_hasCompactSupport hsupp)
    (by simpa using hv.continuous.integrable_of_hasCompactSupport hvc)
    (fun _ _ => differentiableAt_const _) (fun y _ => (hv.differentiable one_ne_zero) y)
  simpa using h

/-- **The pairing of a Hölder function with a derivative of a test function supported in a small disc.** If `Y` is
continuous and `β`-Hölder with constant `M` on `K ⊇ closedBall x t`, `v` is smooth with support in `B(x, t)` and
`‖Dv‖ ≤ B`, and `‖e‖ ≤ 1`, then `|∫ Y ∂_e v| ≤ M t^β · π t² · B`. -/
theorem abs_integral_mul_fderiv_le {Y : ℂ → ℝ} {K : Set ℂ} {M β : ℝ≥0}
    (hY : HolderOnWith M β Y K) (hYc : Continuous Y) {v : ℂ → ℝ} (hv : ContDiff ℝ 1 v) {x : ℂ} {t : ℝ}
    (ht : 0 < t) (hsupp : tsupport v ⊆ ball x t) (hK : closedBall x t ⊆ K) {B : ℝ}
    (hB : ∀ y, ‖fderiv ℝ v y‖ ≤ B) {e : ℂ} (he : ‖e‖ ≤ 1) :
    |∫ y, Y y * fderiv ℝ v y e| ≤ M * t ^ (β : ℝ) * (Real.pi * t ^ 2) * B := by
  have hvc : HasCompactSupport v :=
    (isCompact_closedBall x t).of_isClosed_subset (isClosed_tsupport _) (hsupp.trans ball_subset_closedBall)
  have hxK : x ∈ K := hK (mem_closedBall_self ht.le)
  set g : ℂ → ℝ := fun y => fderiv ℝ v y e with hg
  have hgc : Continuous g := (hv.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hgs : HasCompactSupport g := hvc.fderiv_apply (𝕜 := ℝ) e
  have hzero : ∀ y, y ∉ ball x t → g y = 0 := by
    intro y hy
    have : y ∉ tsupport v := fun h => hy (hsupp h)
    simp only [hg, fderiv_of_notMem_tsupport (𝕜 := ℝ) this, zero_apply]
  have hshift : ∫ y, Y y * g y = ∫ y, (Y y - Y x) * g y := by
    have h0 : ∫ y, g y = 0 := integral_fderiv_apply_eq_zero hv hvc e
    have hi1 : Integrable fun y => (Y y - Y x) * g y :=
      ((hYc.sub continuous_const).mul hgc).integrable_of_hasCompactSupport hgs.mul_left
    have hi2 : Integrable fun y => Y x * g y := (hgc.integrable_of_hasCompactSupport hgs).const_mul _
    calc ∫ y, Y y * g y = ∫ y, ((Y y - Y x) * g y + Y x * g y) := by
          congr 1
          funext y
          ring
      _ = (∫ y, (Y y - Y x) * g y) + ∫ y, Y x * g y := integral_add hi1 hi2
      _ = ∫ y, (Y y - Y x) * g y := by rw [integral_const_mul, h0, mul_zero, add_zero]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x)
  have hbound : ∀ y, ‖(Y y - Y x) * g y‖ ≤ (ball x t).indicator (fun _ => (M : ℝ) * t ^ (β : ℝ) * B) y := by
    intro y
    by_cases hy : y ∈ ball x t
    · rw [indicator_of_mem hy, norm_mul]
      have hyK : y ∈ K := hK (ball_subset_closedBall hy)
      have h1 : ‖Y y - Y x‖ ≤ M * t ^ (β : ℝ) := by
        rw [← dist_eq_norm]
        refine ((hY.dist_le hyK hxK)).trans (mul_le_mul_of_nonneg_left ?_ M.coe_nonneg)
        exact Real.rpow_le_rpow dist_nonneg (mem_ball.1 hy).le β.coe_nonneg
      have h2 : ‖g y‖ ≤ B :=
        ((fderiv ℝ v y).le_opNorm e).trans ((mul_le_of_le_one_right (norm_nonneg _) he).trans (hB y))
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    · rw [indicator_of_notMem hy, hzero y hy, mul_zero, norm_zero]
  have hint : Integrable ((ball x t).indicator fun _ => (M : ℝ) * t ^ (β : ℝ) * B) :=
    (integrableOn_const measure_ball_lt_top.ne).integrable_indicator measurableSet_ball
  rw [hshift, ← Real.norm_eq_abs]
  calc ‖∫ y, (Y y - Y x) * g y‖
      ≤ ∫ y, (ball x t).indicator (fun _ => (M : ℝ) * t ^ (β : ℝ) * B) y :=
        norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hbound)
    _ = M * t ^ (β : ℝ) * (Real.pi * t ^ 2) * B := by
        rw [integral_indicator_const _ measurableSet_ball, Measure.real, Complex.volume_ball,
          ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal ht.le, ENNReal.coe_toReal,
          NNReal.coe_real_pi, smul_eq_mul]
        ring

/-- **The pairing of a Hölder field with the gradient of a test function supported in a small disc**: the sum over
two directions `e₀, e₁` with `‖eᵢ‖ ≤ 1` of the bound of `abs_integral_mul_fderiv_le`. -/
theorem abs_sum_integral_mul_fderiv_le {Y : Fin 2 → ℂ → ℝ} {K : Set ℂ} {M β : ℝ≥0}
    (hY : ∀ i, HolderOnWith M β (Y i) K) (hYc : ∀ i, Continuous (Y i)) {v : ℂ → ℝ} (hv : ContDiff ℝ 1 v)
    {x : ℂ} {t : ℝ} (ht : 0 < t) (hsupp : tsupport v ⊆ ball x t) (hK : closedBall x t ⊆ K) {B : ℝ}
    (hB : ∀ y, ‖fderiv ℝ v y‖ ≤ B) {e : Fin 2 → ℂ} (he : ∀ i, ‖e i‖ ≤ 1) :
    |∑ i, ∫ y, Y i y * fderiv ℝ v y (e i)| ≤ 2 * (M * t ^ (β : ℝ) * (Real.pi * t ^ 2) * B) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Fin.sum_univ_two, two_mul]
  exact add_le_add (abs_integral_mul_fderiv_le (hY 0) (hYc 0) hv ht hsupp hK hB (he 0))
    (abs_integral_mul_fderiv_le (hY 1) (hYc 1) hv ht hsupp hK hB (he 1))

end MatedCRT.GFFLocalRegularity
