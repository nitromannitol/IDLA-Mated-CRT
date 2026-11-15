import MatedCRT.FirstPass.Derived.ConeReferenceIndependentPullback
import MatedCRT.FirstPass.LPBridge.WholePlaneContinuousVersion
import HarmonicBalls.Proofs.GFF.CoordinateModification
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux

/-! # A reference cone from an independent normalized field -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess LQGMetric

namespace MatedCRT.FirstPass.Derived

/-- A normalized whole-plane field independent of a conditioned path supplies
field-measurable continuous coordinates for the reference cone construction.
The circle-average agreement is almost sure at each fixed radius and center. -/
theorem exists_reference_cone_of_normalized_field
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P) (γ : ℝ)
    {F : Ω → ContinuousPath ℝ} (hF : Measurable F) (hind : IndepFun Y F P)
    (hFlaw : IsBMConditionedPositive (lqgQ γ - γ) (P.map F)) :
    ∃ (hC : DistC → (ℂ → ℝ) → ℝ) (c : DistC → ℝ → ℂ → ℝ),
      (∀ x (φ : TestC), hC x φ = x φ) ∧
      (∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z) ∧
      (∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ)) ∧
      Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2) ∧
      IsQuantumCone γ P (fun ω => coneRefPairing γ (hC (Y ω)) (c (Y ω)) (F ω))
        (fun ω => coneRefCircle γ (c (Y ω)) (F ω)) := by
  let μ := P.map Y
  let : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hY.1.measurable.aemeasurable).2 inferInstance
  have hnorm : IsNormalizedWPGFF id μ := by
    refine ⟨LQGMetric.GM.isWholePlaneGFF_id_map hY.1, ?_⟩
    exact (ae_map_iff hY.1.measurable.aemeasurable
      (measurableSet_eq_fun (measurable_circleAvg_left 1 0) measurable_const)).2 hY.2
  obtain ⟨hC, c₀, hh, hp, hc⟩ := normalizedGFF_exists_projectGFF hnorm
  obtain ⟨c, hcont, hae, hh', hmeas⟩ := MatedCRT.Field.wholePlaneGFF_exists_continuous_version hh
  refine ⟨hC, c, hp, ?_, hcont, hmeas, ?_⟩
  · intro r hr z
    have hcircle : ∀ᵐ x ∂μ, c x r z = circleAvg x r z := by
      filter_upwards [hae r z, hc r hr z, hnorm.2] with x h₁ h₂ h₃
      change circleAvg x 1 0 = 0 at h₃
      simpa only [LQGMetric.CircleAvg.cInc, id_eq, h₃, sub_zero] using h₁.trans h₂
    exact (ae_map_iff hY.1.measurable.aemeasurable
      (measurableSet_eq_fun (hh'.measurable_circle r z hr)
        (measurable_circleAvg_left r z))).1 hcircle
  · exact isQuantumCone_coneRef_of_independent hh' γ hcont hmeas hY.1.measurable hF rfl hind hFlaw

end MatedCRT.FirstPass.Derived
