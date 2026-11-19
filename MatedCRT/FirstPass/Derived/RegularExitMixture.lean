import MatedCRT.FirstPass.Derived.RegularRadiusAe

/-!
# Almost every radius is a regular exit radius for almost every law of a random family of path laws

For a random law `κ a` of continuous planar paths, with `a` distributed according to a probability measure `ν`
and `a ↦ κ a` measurable, the mixture `ν.bind κ` is a probability law of paths, so by
`MatedCRT.RegularRadius.ae_ae_regularExit_ball` Lebesgue-almost every radius `r` is a regular exit radius for
`ν.bind κ`; a measurable null superset of the paths that exit `B_r(0)` irregularly has `κ a`-measure zero for
`ν`-almost every `a`.

* `ae_ae_ae_regularExit_ball`: for almost every `r`, for `ν`-almost every `a`, `κ a`-almost every path exits
  `B_r(0)` regularly.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open MarkovProcess (ContinuousPath)
open MatedCRT.TruncatedLaws MatedCRT.RegularRadius

namespace MatedCRT.RegularRadius

/-- **Almost every radius is regular for almost every law of a random family.** If `a ↦ κ a` is a measurable
family of probability laws of continuous planar paths and `ν` is a probability measure, then for Lebesgue-almost
every `r`, for `ν`-almost every `a`, `κ a`-almost every path exits `ball 0 r` regularly. -/
theorem ae_ae_ae_regularExit_ball {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (κ : α → Measure (ContinuousPath ℂ)) (hκ : Measurable κ) (hκp : ∀ a, IsProbabilityMeasure (κ a)) :
    ∀ᵐ r ∂(volume : Measure ℝ), ∀ᵐ a ∂ν, ∀ᵐ X : ContinuousPath ℂ ∂(κ a), RegularExit (ball (0 : ℂ) r) ⇑X := by
  have : IsProbabilityMeasure (ν.bind κ) :=
    isProbabilityMeasure_bind hκ.aemeasurable (Filter.Eventually.of_forall hκp)
  filter_upwards [ae_ae_regularExit_ball (ν.bind κ)] with r hr
  set N : Set (ContinuousPath ℂ) := {X | ¬ RegularExit (ball (0 : ℂ) r) ⇑X} with hN
  have hN0 : (ν.bind κ) N = 0 := hr
  have hT : (ν.bind κ) (toMeasurable (ν.bind κ) N) = 0 := by rw [measure_toMeasurable]; exact hN0
  have hm : Measurable fun a => κ a (toMeasurable (ν.bind κ) N) :=
    (Measure.measurable_coe (measurableSet_toMeasurable _ _)).comp hκ
  rw [Measure.bind_apply (measurableSet_toMeasurable _ _) hκ.aemeasurable, lintegral_eq_zero_iff hm] at hT
  filter_upwards [hT] with a ha
  have h0 : κ a N = 0 := by
    refine measure_mono_null (subset_toMeasurable (ν.bind κ) N) ?_
    exact ha
  exact h0

end MatedCRT.RegularRadius
