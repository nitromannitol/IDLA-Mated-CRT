import MatedCRT.FirstPass.Derived.NormalizedFieldCoordinateExistence
import MatedCRT.FirstPass.Derived.NormalizedFieldReferenceMeasure

/-! # A reference measure for selected normalized-field coordinates -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess LQGMetric

namespace MatedCRT.FirstPass.Derived

/-- A normalized field admits continuous selected coordinates together with
singular and reference measures constructed from the same circle process. -/
theorem exists_normalized_field_coordinates_and_reference_measure
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : Ω → ContinuousPath ℝ) :
    ∃ (hC : DistC → (ℂ → ℝ) → ℝ) (c : DistC → ℝ → ℂ → ℝ)
      (μ : DistC → Measure ℂ),
      IsNormalizedWPGFF id (P.map Y) ∧
      IsWholePlaneGFF (P.map Y) hC c ∧
      (∀ x (φ : TestC), hC x φ = x φ) ∧
      (∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z) ∧
      (∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ)) ∧
      Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2) ∧
      IsLQGMeasureOfField (P.map Y) γ γ c μ ∧
      IsLQGMeasureOfField P γ γ (fun ω => c (Y ω)) (fun ω => μ (Y ω)) ∧
      IsLQGMeasure P γ (fun ω => coneRefCircle γ (c (Y ω)) (w ω))
        (fun ω => coneRefMeasure γ (c (Y ω)) (w ω) (μ (Y ω))) := by
  obtain ⟨hC, c, hnorm, hG, hp, hc, hcont, hmeas⟩ :=
    exists_normalized_field_selected_coordinates hY
  obtain ⟨μ, hμ, hμmap, hμref⟩ :=
    exists_reference_measure_of_normalized_field hY hp hc hcont hmeas hγ hγ2 w
  exact ⟨hC, c, μ, hnorm, hG, hp, hc, hcont, hmeas, hμ, hμmap, hμref⟩

end MatedCRT.FirstPass.Derived
