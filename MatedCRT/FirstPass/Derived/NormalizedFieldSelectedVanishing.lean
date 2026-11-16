import MatedCRT.FirstPass.Derived.NormalizedFieldMappedReferenceMeasure
import LatticeProb.LQG.SingularApproximantVanishing
import HarmonicBalls.FirstPass.LPBridge.M1

/-! # Selected field coordinates and vanishing singular approximants -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess LQGMetric
open Filter Topology Metric
open LatticeProb.LQG
open LatticeProb.Gauss (fieldCircleAverage)

namespace MatedCRT.FirstPass.Derived

/-- A single choice of field coordinates and reference measure also has the
common dyadic vanishing property on the original probability space. -/
theorem exists_normalized_field_coordinates_reference_measure_and_vanishing
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
      HarmonicBalls.IsLQGMeasureOfField (P.map Y) γ γ c μ ∧
      HarmonicBalls.IsLQGMeasureOfField P γ γ (fun ω => c (Y ω)) (fun ω => μ (Y ω)) ∧
      HarmonicBalls.IsLQGMeasure P γ (fun ω => coneRefCircle γ (c (Y ω)) (w ω))
        (fun ω => coneRefMeasure γ (c (Y ω)) (w ω) (μ (Y ω))) ∧
      (∀ᵐ ω ∂P, ∀ k : ℕ → ℕ,
        Tendsto (fun J => LatticeProb.LQG.lqgApprox γ (LatticeProb.Gauss.fieldCircleAverage γ (c (Y ω)))
          (LatticeProb.LQG.dyadicScale (k J)) (ball 0 (LatticeProb.LQG.dyadicScale J))) atTop (𝓝 0)) := by
  obtain ⟨hC, c, μ, hnorm, hG, hp, hc, hcm, hcont, hmeas, hμ, hμmap, hμref⟩ :=
    exists_normalized_field_coordinates_and_mapped_reference_measure hY hγ hγ2 w
  refine ⟨hC, c, μ, hnorm, hG, hp, hc, hcm, hcont, hmeas, hμ, hμmap, hμref, ?_⟩
  have hvanish : ∀ᵐ x ∂(P.map Y), ∀ k : ℕ → ℕ,
      Tendsto (fun J => LatticeProb.LQG.lqgApprox γ (LatticeProb.Gauss.fieldCircleAverage γ (c x))
        (LatticeProb.LQG.dyadicScale (k J)) (ball 0 (LatticeProb.LQG.dyadicScale J))) atTop (𝓝 0) :=
    ae_tendsto_singular_approximant_dyadic_ball hnorm
      ((HarmonicBalls.LPBridge.isWholePlaneGFF_iff _ _ _).1 hG)
      hcont hcm hγ hγ2 (MatedCRT.lt_lqgQ_of_mem_Ioo hγ hγ2)
      (δ := 1) (r := 1 / 4) (ρ := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  exact ae_of_ae_map hY.1.measurable.aemeasurable hvanish

end MatedCRT.FirstPass.Derived
