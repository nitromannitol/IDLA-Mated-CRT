import MatedCRT.FirstPass.Derived.NormalizedFieldSelectedVanishing
import LatticeProb.LQG.SingularApproximantVanishing
import HarmonicBalls.FirstPass.LPBridge.M1

/-! # Vanishing singular approximants for given field coordinates -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set HarmonicBalls LQGMetric
open Filter Topology Metric
open LatticeProb.LQG
open LatticeProb.Gauss (fieldCircleAverage)

namespace MatedCRT.FirstPass.Derived

/-- The given continuous coordinates of a normalized field have a common
vanishing event for all sequences of dyadic regularization scales. -/
theorem ae_singular_approximant_vanishing_of_selected_coordinates
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → DistC} (hY : IsNormalizedWPGFF Y P)
    {hC : DistC → (ℂ → ℝ) → ℝ} {c : DistC → ℝ → ℂ → ℝ}
    (hp : ∀ x (φ : TestC), hC x φ = x φ)
    (hc : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c (Y ω) r z = circleAvg (Y ω) r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c q.2 q.1.1 q.1.2))
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ k : ℕ → ℕ,
      Tendsto (fun J => LatticeProb.LQG.lqgApprox γ (LatticeProb.Gauss.fieldCircleAverage γ (c (Y ω)))
        (LatticeProb.LQG.dyadicScale (k J)) (ball 0 (LatticeProb.LQG.dyadicScale J))) atTop (𝓝 0) := by
  let μ := P.map Y
  let : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hY.1.measurable.aemeasurable).2 inferInstance
  have hnorm : IsNormalizedWPGFF id μ := by
    refine ⟨LQGMetric.GM.isWholePlaneGFF_id_map hY.1, ?_⟩
    exact (ae_map_iff hY.1.measurable.aemeasurable
      (measurableSet_eq_fun (measurable_circleAvg_left 1 0) measurable_const)).2 hY.2
  have hG : IsWholePlaneGFF μ hC c :=
    isWholePlaneGFF_selected_coordinates hY hp hc hcont hmeas
  have hcm : ∀ r, 0 < r → ∀ z, ∀ᵐ x ∂μ, c x r z = circleAvg x r z := by
    intro r hr z
    exact (ae_map_iff hY.1.measurable.aemeasurable
      (measurableSet_eq_fun (hG.measurable_circle r z hr)
        (measurable_circleAvg_left r z))).2 (hc r hr z)
  have hvanish : ∀ᵐ x ∂μ, ∀ k : ℕ → ℕ,
      Tendsto (fun J => LatticeProb.LQG.lqgApprox γ (LatticeProb.Gauss.fieldCircleAverage γ (c x))
        (LatticeProb.LQG.dyadicScale (k J)) (ball 0 (LatticeProb.LQG.dyadicScale J))) atTop (𝓝 0) :=
    ae_tendsto_singular_approximant_dyadic_ball hnorm
      ((HarmonicBalls.LPBridge.isWholePlaneGFF_iff _ _ _).1 hG)
      hcont hcm hγ hγ2 (MatedCRT.lt_lqgQ_of_mem_Ioo hγ hγ2)
      (δ := 1) (r := 1 / 4) (ρ := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  exact ae_of_ae_map hY.1.measurable.aemeasurable hvanish

end MatedCRT.FirstPass.Derived
