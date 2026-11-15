import MatedCRT.FirstPass.Derived.NormalizedFieldSelectedReferenceMeasure

/-! # Selected field coordinates on the mapped law -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess LQGMetric

namespace MatedCRT.FirstPass.Derived

/-- The same selected field coordinates and reference measures have
fixed-coordinate almost-sure agreement on both the original and mapped laws. -/
theorem exists_normalized_field_coordinates_and_mapped_reference_measure
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (w : Ω → ContinuousPath ℝ) :
    ∃ (hC : DistC → (ℂ → ℝ) → ℝ) (c : DistC → ℝ → ℂ → ℝ)
      (μ : DistC → Measure ℂ),
      IsNormalizedWPGFF id (P.map Y) ∧
      IsWholePlaneGFF (P.map Y) hC c ∧
      (∀ x (φ : TestC), hC x φ = x φ) ∧
      (∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z) ∧
      (∀ r, 0 < r → ∀ z, ∀ᵐ x ∂(P.map Y), c x r z = circleAvg x r z) ∧
      (∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ)) ∧
      Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2) ∧
      IsLQGMeasureOfField (P.map Y) γ γ c μ ∧
      IsLQGMeasureOfField P γ γ (fun ω => c (Y ω)) (fun ω => μ (Y ω)) ∧
      IsLQGMeasure P γ (fun ω => coneRefCircle γ (c (Y ω)) (w ω))
        (fun ω => coneRefMeasure γ (c (Y ω)) (w ω) (μ (Y ω))) := by
  obtain ⟨hC, c, μ, hnorm, hG, hp, hc, hcont, hmeas, hμ, hμmap, hμref⟩ :=
    exists_normalized_field_coordinates_and_reference_measure hY hγ hγ2 w
  refine ⟨hC, c, μ, hnorm, hG, hp, hc, ?_, hcont, hmeas, hμ, hμmap, hμref⟩
  intro r hr z
  exact (ae_map_iff hY.1.measurable.aemeasurable
    (measurableSet_eq_fun (hG.measurable_circle r z hr)
      (measurable_circleAvg_left r z))).2 (hc r hr z)

end MatedCRT.FirstPass.Derived
