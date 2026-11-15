import MatedCRT.FirstPass.Derived.NormalizedFieldSelectedCoordinates

/-! # Continuous coordinates of a normalized whole-plane field -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set HarmonicBalls LQGMetric

namespace MatedCRT.FirstPass.Derived

/-- A normalized field admits continuous selected coordinates on its own law,
with fixed-coordinate almost-sure agreement with its circle averages. -/
theorem exists_normalized_field_selected_coordinates
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P) :
    ∃ (hC : DistC → (ℂ → ℝ) → ℝ) (c : DistC → ℝ → ℂ → ℝ),
      IsNormalizedWPGFF id (P.map Y) ∧
      IsWholePlaneGFF (P.map Y) hC c ∧
      (∀ x (φ : TestC), hC x φ = x φ) ∧
      (∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z) ∧
      (∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ)) ∧
      Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2) := by
  let μ := P.map Y
  let : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hY.1.measurable.aemeasurable).2 inferInstance
  have hnorm : IsNormalizedWPGFF id μ := by
    refine ⟨LQGMetric.GM.isWholePlaneGFF_id_map hY.1, ?_⟩
    exact (ae_map_iff hY.1.measurable.aemeasurable
      (measurableSet_eq_fun (measurable_circleAvg_left 1 0) measurable_const)).2 hY.2
  obtain ⟨hC, c₀, hh, hp, hc⟩ := normalizedGFF_exists_projectGFF hnorm
  obtain ⟨c, hcont, hae, hh', hmeas⟩ := MatedCRT.Field.wholePlaneGFF_exists_continuous_version hh
  refine ⟨hC, c, hnorm, hh', hp, ?_, hcont, hmeas⟩
  intro r hr z
  have hcircle : ∀ᵐ x ∂μ, c x r z = circleAvg x r z := by
    filter_upwards [hae r z, hc r hr z, hnorm.2] with x h₁ h₂ h₃
    change circleAvg x 1 0 = 0 at h₃
    simpa only [LQGMetric.CircleAvg.cInc, id_eq, h₃, sub_zero] using h₁.trans h₂
  exact (ae_map_iff hY.1.measurable.aemeasurable
    (measurableSet_eq_fun (hh'.measurable_circle r z hr)
      (measurable_circleAvg_left r z))).1 hcircle

end MatedCRT.FirstPass.Derived
