import MatedCRT.FirstPass.S4S6c.KernelProduct
import MatedCRT.FirstPass.S4S6c.CircleSwap

/-!
# Lemma 1 of the Lemma 6.8 argument: the mass bound (6) (q2, task fp-S4S6c; LEMMA68 eq (6))

For a measurable annulus `A ⊆ closedBall z (2R)` of finite `μ`-mass, with `F(v) = ∫_A (log(R/|u-v|)+1) dμ(u)`
bounded by `C * m` on the circle `∂B_{3R/2}(z)`, the mass satisfies `(1 - log 2) μ(A) ≤ C m`, i.e.
`M ≤ κ₀⁻¹ C m` with `κ₀ = 1 - log 2`. Proof: the pointwise circle-average bound (`GoodAnnulusKernel`), the Fubini
interchange of `CircleSwap` with the joint integrability of `KernelProduct`, and the bound of the circle average of `F`.
The hypothesis on `F` is only needed on the circle, which is weaker than the good-annulus event (4) of LEMMA68.
-/

open MeasureTheory Real Set Metric

namespace MatedCRT

/-- **Mass bound of Lemma 1** (LEMMA68 eq (6)): `(1 - log 2) μ(A) ≤ C m`. -/
theorem lemma1_mass_le {A : Set ℂ} (μ : Measure ℂ) [SFinite μ] {z : ℂ} {R C m : ℝ} (hR : 0 < R)
    (hA : MeasurableSet A) (hAb : A ⊆ closedBall z (2 * R)) (hμA : μ A ≠ ⊤)
    (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hF : ∀ v ∈ sphere z (3 * R / 2), ∫ u in A, (Real.log (R / ‖u - v‖) + 1) ∂μ ≤ C * m) :
    (1 - Real.log 2) * (μ A).toReal ≤ C * m := by
  have ht : (0 : ℝ) < 3 * R / 2 := by positivity
  -- the circle average of the kernel, as a function of the centre-distance of `u`
  have hclosed : (fun u : ℂ => circleAverage (fun v : ℂ => Real.log (R / ‖u - v‖) + 1) z (3 * R / 2)) =
      fun u : ℂ => (Real.log R + 1) - (Real.log (3 * R / 2) + Real.posLog ((3 * R / 2)⁻¹ * ‖z - u‖)) :=
    funext fun u => circleAverage_kernel_eq hR
  have hpt : ∀ u ∈ A, 1 - Real.log 2 ≤
      circleAverage (fun v : ℂ => Real.log (R / ‖u - v‖) + 1) z (3 * R / 2) ∧
      circleAverage (fun v : ℂ => Real.log (R / ‖u - v‖) + 1) z (3 * R / 2) ≤
        (Real.log R + 1) - Real.log (3 * R / 2) := by
    intro u hu
    have hu' : ‖u - z‖ ≤ 2 * R := by
      have := hAb hu
      rwa [mem_closedBall, dist_eq_norm] at this
    exact ⟨circleAverage_kernel_ge_one_sub_log_two hR hu', circleAverage_kernel_le (z := z) (u := u) hR⟩
  -- integrability of the circle average on the annulus
  have hmeas : Measurable (fun u : ℂ =>
      (Real.log R + 1) - (Real.log (3 * R / 2) + Real.posLog ((3 * R / 2)⁻¹ * ‖z - u‖))) := by
    unfold Real.posLog
    fun_prop
  have : IsFiniteMeasure (μ.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hμA⟩
  have hintavg : Integrable (fun u : ℂ =>
      circleAverage (fun v : ℂ => Real.log (R / ‖u - v‖) + 1) z (3 * R / 2)) (μ.restrict A) := by
    rw [hclosed]
    refine Integrable.mono' (integrable_const (μ := μ.restrict A)
      (|1 - Real.log 2| + |(Real.log R + 1) - Real.log (3 * R / 2)|)) hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hA] with u hu
    obtain ⟨h1, h2⟩ := hpt u hu
    have hav : circleAverage (fun v : ℂ => Real.log (R / ‖u - v‖) + 1) z (3 * R / 2) =
        (Real.log R + 1) - (Real.log (3 * R / 2) + Real.posLog ((3 * R / 2)⁻¹ * ‖z - u‖)) :=
      circleAverage_kernel_eq hR
    rw [Real.norm_eq_abs, abs_le]
    rw [hav] at h1 h2
    constructor
    · linarith [le_abs_self (1 - Real.log 2), neg_abs_le (1 - Real.log 2), abs_nonneg ((Real.log R + 1) - Real.log (3 * R / 2)),
        le_abs_self ((Real.log R + 1) - Real.log (3 * R / 2)), neg_abs_le ((Real.log R + 1) - Real.log (3 * R / 2)),
        abs_nonneg (1 - Real.log 2)]
    · linarith [le_abs_self (1 - Real.log 2), le_abs_self ((Real.log R + 1) - Real.log (3 * R / 2)),
        abs_nonneg (1 - Real.log 2), abs_nonneg ((Real.log R + 1) - Real.log (3 * R / 2))]
  -- Fubini: the average over the circle of the integral over the annulus
  have hswap := integral_circleAverage_swap (A := A) μ (z := z) (t := 3 * R / 2)
    (K := fun u v : ℂ => Real.log (R / ‖u - v‖) + 1) (integrable_kernel_prod μ hR hA hAb hμA)
  -- the circle average of `F` is at most `C m`
  have hbound : circleAverage (fun v : ℂ => ∫ u in A, (Real.log (R / ‖u - v‖) + 1) ∂μ) z (3 * R / 2) ≤
      C * m := by
    rw [circleAverage_def, smul_eq_mul]
    by_cases hI : IntervalIntegrable
        (fun θ : ℝ => ∫ u in A, (Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1) ∂μ) volume 0 (2 * π)
    · have hle : ∫ θ in (0 : ℝ)..(2 * π),
          ∫ u in A, (Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1) ∂μ ≤
            ∫ θ in (0 : ℝ)..(2 * π), C * m := by
        apply intervalIntegral.integral_mono_on (by positivity) hI intervalIntegrable_const
        intro θ _
        apply hF
        refine Metric.mem_sphere.2 ?_
        rw [dist_eq_norm, norm_sub_rev, norm_circleMap_sub_center', abs_of_pos ht]
      rw [intervalIntegral.integral_const, smul_eq_mul] at hle
      have hpi : (0 : ℝ) < 2 * π := by positivity
      calc (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
            ∫ u in A, (Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1) ∂μ
          ≤ (2 * π)⁻¹ * ((2 * π - 0) * (C * m)) := mul_le_mul_of_nonneg_left hle (by positivity)
        _ = C * m := by rw [sub_zero, ← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]
    · rw [intervalIntegral.integral_undef hI, mul_zero]
      positivity
  -- lower bound: the constant `1 - log 2` on the annulus
  have hlow : ∫ u in A, (1 - Real.log 2) ∂μ ≤ ∫ u in A,
      circleAverage (fun v : ℂ => Real.log (R / ‖u - v‖) + 1) z (3 * R / 2) ∂μ := by
    apply setIntegral_mono_on (integrableOn_const hμA) hintavg hA
    intro u hu
    exact (hpt u hu).1
  have hconst : ∫ u in A, (1 - Real.log 2) ∂μ = (μ A).toReal * (1 - Real.log 2) := by
    simp only [setIntegral_const, smul_eq_mul, Measure.real]
  -- combine
  have hfin : (μ A).toReal * (1 - Real.log 2) ≤ C * m := by
    rw [← hconst]
    exact hlow.trans (le_of_eq hswap |>.trans hbound)
  linarith [hfin, mul_comm (μ A).toReal (1 - Real.log 2)]

end MatedCRT
