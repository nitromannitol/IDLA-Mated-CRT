import MatedCRT.FirstPass.Derived.NormalizedFieldSelectedCoordinates
import MatedCRT.FirstPass.Derived.ConeReferenceSingularPullback

/-! # Reference-cone measure for selected field coordinates -/

set_option autoImplicit false

open MeasureTheory Set HarmonicBalls MarkovProcess LQGMetric

namespace MatedCRT.FirstPass.Derived

/-- Selected coordinates of a normalized field give a singular-field measure
and a reference-cone measure on the same sample space. -/
theorem exists_reference_measure_of_normalized_field
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {hC : DistC → (ℂ → ℝ) → ℝ} {c : DistC → ℝ → ℂ → ℝ}
    (hp : ∀ x (φ : TestC), hC x φ = x φ)
    (hc : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2))
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : Ω → ContinuousPath ℝ) :
    ∃ μ : DistC → Measure ℂ,
      IsLQGMeasureOfField (P.map Y) γ γ c μ ∧
      IsLQGMeasureOfField P γ γ (fun ω => c (Y ω)) (fun ω => μ (Y ω)) ∧
      IsLQGMeasure P γ (fun ω => coneRefCircle γ (c (Y ω)) (w ω))
        (fun ω => coneRefMeasure γ (c (Y ω)) (w ω) (μ (Y ω))) := by
  exact exists_singular_measure_and_coneRef_of_map hY.1.measurable
    (isWholePlaneGFF_selected_coordinates hY hp hc hcont hmeas) hcont hγ hγ2 w

end MatedCRT.FirstPass.Derived
