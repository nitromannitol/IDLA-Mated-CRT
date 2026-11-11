import MatedCRT.Defs.Setting
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! Annealed bounds from uniform quenched estimates. -/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

/-- A uniform bound on quenched probabilities outside a bad environment set
bounds the annealed outer probability by the sum of the bad-set outer measure
and the quenched bound. No measurability of the sections is assumed. -/
theorem sectionwiseOuterProb_le_measure_add_of_quenched_le
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Ω → Measure X)
    (hκ : ∀ ω, κ ω univ ≤ 1) (E : Set (Ω × X)) (B : Set Ω) (c : ℝ≥0∞)
    (hgood : ∀ ω, ω ∉ B → κ ω (Prod.mk ω ⁻¹' E) ≤ c) :
    sectionwiseOuterProb P κ E ≤ P B + c := by
  let T : Set Ω := toMeasurable P B
  have hTm : MeasurableSet T := measurableSet_toMeasurable P B
  have hpoint : ∀ ω, κ ω (Prod.mk ω ⁻¹' E) ≤ T.indicator 1 ω + c := by
    intro ω
    by_cases hω : ω ∈ T
    · rw [indicator_of_mem hω, Pi.one_apply]
      exact (measure_mono (subset_univ _) |>.trans (hκ ω)).trans le_self_add
    · have hωB : ω ∉ B := fun h => hω (subset_toMeasurable P B h)
      rw [indicator_of_notMem hω, zero_add]
      exact hgood ω hωB
  have hm : Measurable (fun ω => T.indicator 1 ω + c) :=
    (measurable_one.indicator hTm).add measurable_const
  unfold sectionwiseOuterProb outerLIntegral
  calc
    (⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g)
      (_ : (fun ω => κ ω (Prod.mk ω ⁻¹' E)) ≤ g), ∫⁻ ω, g ω ∂P) ≤
      ∫⁻ ω, (T.indicator 1 ω + c) ∂P :=
      iInf_le_of_le (fun ω => T.indicator 1 ω + c)
        (iInf_le_of_le hm (iInf_le_of_le hpoint le_rfl))
    _ = P B + c := by
      rw [lintegral_add_right _ measurable_const, lintegral_indicator_one hTm,
        lintegral_const, measure_univ, mul_one, show P T = P B from measure_toMeasurable B]

end MatedCRT

#print axioms MatedCRT.sectionwiseOuterProb_le_measure_add_of_quenched_le
