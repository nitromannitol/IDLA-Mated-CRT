import Mathlib

/-!
# FIRST PASS, Lemma 5.3 (B1b): AE-form test-integral measurability from a measurable version of the LQG measure

The AE form of the test-integral measurability of B1b is obtained from `FrozenLQGMeasureFieldMeasurable` (FirstPass/Frozen/S4S6c.lean:44): a version `g` of the measure `μ` that is measurable for the
field σ-algebra, equal to `μ` almost surely. Here: for a continuous `φ` supported in `B_R`, `ω ↦ ∫ φ dμ_ω` is AE-measurable,
using `Measure.measurable_lintegral` and the positive/negative part decomposition of the integral (needs `μ_ω(B_R) < ∞` a.s.).
The σ-algebra `m` is the field σ-algebra `S.fieldSigma`; the hypothesis `m ≤ mΩ` is the one ingredient not stated in the repository.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric

/-- **AE-form test-integral measurability** (B1b, item (e)): see the module docstring. -/
theorem aemeasurable_integral_of_measurable_version {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    (hm : m ≤ mΩ)
    {P : Measure Ω} {μ g : Ω → Measure ℂ} (hg : Measurable[m] g) (hμg : ∀ᵐ ω ∂P, μ ω = g ω)
    {R : ℝ} (hloc : ∀ᵐ ω ∂P, μ ω (closedBall (0 : ℂ) R) < ⊤)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hsupp : tsupport φ ⊆ closedBall (0 : ℂ) R) :
    AEMeasurable (fun ω => ∫ x, φ x ∂(μ ω)) P := by
  have hF : Measurable[m] (fun ω => ∫⁻ x, ENNReal.ofReal (φ x) ∂(g ω)) :=
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hφ.measurable)).comp hg
  have hG : Measurable[m] (fun ω => ∫⁻ x, ENNReal.ofReal (-φ x) ∂(g ω)) :=
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hφ.measurable.neg)).comp hg
  have hH : Measurable[m] (fun ω => (∫⁻ x, ENNReal.ofReal (φ x) ∂(g ω)).toReal -
      (∫⁻ x, ENNReal.ofReal (-φ x) ∂(g ω)).toReal) :=
    (ENNReal.measurable_toReal.comp hF).sub (ENNReal.measurable_toReal.comp hG)
  refine ⟨_, hH.mono hm le_rfl, ?_⟩
  filter_upwards [hμg, hloc] with ω hωμ hωloc
  have hsub : Function.support φ ⊆ closedBall (0 : ℂ) R := (subset_tsupport φ).trans hsupp
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hφ.continuousOn
  have hbound : ∀ᵐ x ∂((μ ω).restrict (closedBall (0 : ℂ) R)), ‖φ x‖ ≤ C :=
    (ae_restrict_mem measurableSet_closedBall).mono fun x hx => hC x hx
  have hint : Integrable φ (μ ω) :=
    (integrableOn_iff_integrable_of_support_subset hsub).1
      (Measure.integrableOn_of_bounded hωloc.ne hφ.aestronglyMeasurable hbound)
  have hint' : Integrable φ (g ω) := hωμ ▸ hint
  rw [hωμ, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint']

end MatedCRT.S5c
