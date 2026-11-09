import MatedCRT.FirstPass.S4S6c.KernelBound

/-!
# Joint integrability of the corrected kernel on the annulus times the circle (q2, task fp-S4S6c; LEMMA68 Lemma 1)

`integrable_kernel_prod` is the hypothesis `hjoint` of `CircleSwap.lean`, for the kernel
`K(u,v) = log(R/|u-v|) + 1` and the circle `∂B_{3R/2}(z)`, under the measure `μ.restrict A ⊗ (0, 2π]`.
Proof: `integrable_prod_iff`; each slice is interval integrable (`intervalIntegrable_kernel_slice`); the function
`u ↦ ∫ |K(u, circleMap θ)| dθ` is strongly measurable (Fubini for strongly measurable functions) and bounded on the
annulus by `integral_norm_kernel_le`, so it is integrable on the finite measure `μ.restrict A`.
Hypotheses: `A ⊆ closedBall z (2R)` measurable with `μ A ≠ ⊤` (finite on the annulus).
-/

open MeasureTheory Real Set Metric

namespace MatedCRT

/-- Joint integrability of `(u, θ) ↦ log(R/|u - circleMap z (3R/2) θ|) + 1` on `(μ|A) ⊗ (vol|(0,2π])`. -/
theorem integrable_kernel_prod {A : Set ℂ} (μ : Measure ℂ) [SFinite μ] {z : ℂ} {R : ℝ} (hR : 0 < R)
    (hA : MeasurableSet A) (hAb : A ⊆ closedBall z (2 * R)) (hμA : μ A ≠ ⊤) :
    Integrable (fun p : ℂ × ℝ => Real.log (R / ‖p.1 - circleMap z (3 * R / 2) p.2‖) + 1)
      ((μ.restrict A).prod (volume.restrict (Ioc 0 (2 * π)))) := by
  have ht : (0 : ℝ) < 3 * R / 2 := by positivity
  have hmeas : Measurable (fun p : ℂ × ℝ => Real.log (R / ‖p.1 - circleMap z (3 * R / 2) p.2‖) + 1) :=
    measurable_kernel_circle z R (3 * R / 2)
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun u => ?_, ?_⟩
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)).1
      (intervalIntegrable_kernel_slice (u := u) (z := z) (R := R) hR ht.ne')
  · have : IsFiniteMeasure (μ.restrict A) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hμA⟩
    refine Integrable.mono' (integrable_const (μ := μ.restrict A)
      (2 * π * ((Real.log R + 1) - Real.log (3 * R / 2) + 2 * (Real.log 4 - 1)))) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_right
        (ν := volume.restrict (Ioc 0 (2 * π)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hA] with u hu
      have hu' : ‖u - z‖ ≤ 2 * R := by
        have := hAb hu
        rwa [mem_closedBall, dist_eq_norm] at this
      have hnn : 0 ≤ ∫ θ in Ioc 0 (2 * π), ‖Real.log (R / ‖u - circleMap z (3 * R / 2) θ‖) + 1‖ :=
        integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg hnn]
      exact integral_norm_kernel_le hR hu'

end MatedCRT
