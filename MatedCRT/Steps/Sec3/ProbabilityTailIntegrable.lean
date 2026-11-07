import MatedCRT.Steps.Sec3.PowerTailSplit
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! Integrability of positive-moment probability tails. -/

open MeasureTheory Set

namespace MatedCRT

/-- The real-valued upper tail of a random variable is measurable. -/
theorem measurable_probability_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) :
    Measurable (fun t : ℝ => μ.real {ω | t < f ω}) := by
  exact Measurable.ennreal_toReal <| Antitone.measurable
    (fun _ _ hst => measure_mono (fun _ h => lt_of_le_of_lt hst h))

/-- A positive-moment weight times a probability tail is interval integrable on a
bounded interval with nonnegative endpoints. -/
theorem intervalIntegrable_probability_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    {a b χ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hχ : 0 < χ) :
    IntervalIntegrable (fun s : ℝ => s ^ (χ - 1) * μ.real {ω | s < f ω}) volume a b := by
  have hp : IntervalIntegrable (fun s : ℝ => s ^ (χ - 1)) volume a b :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hp ⊢
  apply hp.mono_nonneg (hp.aestronglyMeasurable.mul (measurable_probability_tail μ f).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact mul_nonneg (Real.rpow_nonneg (le_trans ha hs.1.le) _) measureReal_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simpa using mul_le_mul_of_nonneg_left (measureReal_le_one (μ := μ) (s := {ω | s < f ω}))
      (Real.rpow_nonneg (le_trans ha hs.1.le) _)

/-- The integrated positive-moment tail bound for a probability measure. -/
theorem integral_probability_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    {ℓ R χ ν C : ℝ} (hℓ : 0 < ℓ) (hLR : ℓ ≤ R) (hχ : 0 < χ)
    (htail : ∀ s ∈ Ioo ℓ R, μ.real {ω | s < f ω} ≤ C * ℓ ^ ν * s ^ (-ν)) :
    χ * (∫ s in 0..R, s ^ (χ - 1) * μ.real {ω | s < f ω}) ≤
      ℓ ^ χ + χ * C * (ℓ ^ ν * ∫ s in ℓ..R, s ^ (χ - ν - 1)) := by
  apply integral_weighted_tail_le hℓ hLR hχ
  · intro s hs
    exact measureReal_le_one
  · exact htail
  · exact intervalIntegrable_probability_tail μ f le_rfl hℓ.le hχ
  · exact intervalIntegrable_probability_tail μ f hℓ.le hLR hχ

end MatedCRT
