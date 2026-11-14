import Mathlib

/-!
# Integral of a bounded measurable function against a mixture of probability measures

For a probability measure `m` on `α`, an almost everywhere measurable family `κ : α → Measure β` of probability
measures, and a bounded measurable `f : β → ℝ`,
`∫ f d(m.bind κ) = ∫ x, ∫ f dκ x dm`.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The integral of a nonnegative bounded measurable function against a measurable family of probability measures
is almost everywhere measurable. -/
theorem aemeasurable_integral_of_nonneg {m : Measure α} {κ : α → Measure β} (hκ : AEMeasurable κ m)
    {g : β → ℝ} (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y) :
    AEMeasurable (fun x => ∫ y, g y ∂(κ x)) m := by
  have hgl : Measurable fun y => ENNReal.ofReal (g y) := hg.ennreal_ofReal
  have : (fun x => ∫ y, g y ∂(κ x)) = fun x => (∫⁻ y, ENNReal.ofReal (g y) ∂(κ x)).toReal := by
    funext x
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hg.aestronglyMeasurable
  rw [this]
  exact ((Measure.measurable_lintegral hgl).comp_aemeasurable hκ).ennreal_toReal

/-- A bounded measurable function integrates against a mixture as the mixture of the integrals (nonnegative
case). -/
theorem integral_bind_of_nonneg_bounded {m : Measure α} [IsProbabilityMeasure m] {κ : α → Measure β}
    (hκ : AEMeasurable κ m) (hprob : ∀ᵐ x ∂m, IsProbabilityMeasure (κ x)) {g : β → ℝ} (hg : Measurable g)
    (hg0 : ∀ y, 0 ≤ g y) {C : ℝ} (hC : ∀ y, g y ≤ C) :
    ∫ y, g y ∂(m.bind κ) = ∫ x, ∫ y, g y ∂(κ x) ∂m := by
  have : IsProbabilityMeasure (m.bind κ) := isProbabilityMeasure_bind hκ hprob
  have hgl : Measurable fun y => ENNReal.ofReal (g y) := hg.ennreal_ofReal
  have hmeas := aemeasurable_integral_of_nonneg hκ hg hg0
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hg.aestronglyMeasurable,
    Measure.lintegral_bind hκ hgl.aemeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => integral_nonneg hg0)
      hmeas.aestronglyMeasurable]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hprob] with x hx
  have hint : Integrable g (κ x) :=
    Integrable.of_bound hg.aestronglyMeasurable C
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 y)]; exact hC y)
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hg0)]

/-- **A bounded measurable function integrates against a mixture of probability measures as the mixture of the
integrals.** -/
theorem integral_bind_of_bounded {m : Measure α} [IsProbabilityMeasure m] {κ : α → Measure β}
    (hκ : AEMeasurable κ m) (hprob : ∀ᵐ x ∂m, IsProbabilityMeasure (κ x)) {f : β → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    ∫ y, f y ∂(m.bind κ) = ∫ x, ∫ y, f y ∂(κ x) ∂m := by
  have : IsProbabilityMeasure (m.bind κ) := isProbabilityMeasure_bind hκ hprob
  have hg0 : ∀ y, 0 ≤ f y + C := fun y => by linarith [neg_abs_le (f y), hC y]
  have hgC : ∀ y, f y + C ≤ 2 * C := fun y => by linarith [le_abs_self (f y), hC y]
  have h := integral_bind_of_nonneg_bounded hκ hprob (hf.add_const C) hg0 hgC
  have hmeas := aemeasurable_integral_of_nonneg hκ (hf.add_const C) hg0
  have hint : ∀ (μ : Measure β) [IsProbabilityMeasure μ], Integrable f μ := fun μ _ =>
    Integrable.of_bound hf.aestronglyMeasurable C
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC y)
  have h1 : ∫ y, (f y + C) ∂(m.bind κ) = ∫ y, f y ∂(m.bind κ) + C := by
    rw [integral_add (hint _) (integrable_const C)]
    simp
  have h2 : ∀ᵐ x ∂m, ∫ y, (f y + C) ∂(κ x) = ∫ y, f y ∂(κ x) + C := by
    filter_upwards [hprob] with x hx
    rw [integral_add (hint _) (integrable_const C)]
    simp
  have hGm : AEMeasurable (fun x => ∫ y, f y ∂(κ x)) m := by
    have : (fun x => ∫ y, f y ∂(κ x)) =ᵐ[m] fun x => ∫ y, (f y + C) ∂(κ x) - C := by
      filter_upwards [h2] with x hx
      rw [hx]; ring
    exact (hmeas.sub_const C).congr this.symm
  have hGint : Integrable (fun x => ∫ y, f y ∂(κ x)) m := by
    refine Integrable.of_bound hGm.aestronglyMeasurable C ?_
    filter_upwards [hprob] with x hx
    rw [Real.norm_eq_abs]
    exact (abs_integral_le_integral_abs).trans
      ((integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _) (integrable_const C)
        (ae_of_all _ hC)).trans (by simp))
  have h3 : ∫ x, ∫ y, (f y + C) ∂(κ x) ∂m = ∫ x, ∫ y, f y ∂(κ x) ∂m + C := by
    rw [integral_congr_ae h2, integral_add hGint (integrable_const C)]
    simp
  linarith

end MatedCRT.FirstPass.Derived
