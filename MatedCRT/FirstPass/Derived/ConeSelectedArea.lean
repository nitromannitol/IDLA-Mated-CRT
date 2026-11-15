import MatedCRT.FirstPass.Derived.ConeSpatialCircleFubini
import HarmonicBalls.FirstPass.LPBridge.M4
import LatticeProb.LQG.ConeAreaSpatialAE

/-! # Identification of the area of a matching cone distribution -/

noncomputable section

open MeasureTheory
open HarmonicBalls

namespace MatedCRT

/-- The selected area of a measurable distribution matching a quantum cone
agrees almost surely with any LQG measure of the cone circle averages. -/
theorem ae_cone_selectedArea_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {H : Ω → LQGMetric.DistC} {μ : Ω → Measure ℂ}
    (hQ : IsQuantumCone γ P hC hcirc)
    (hμ : IsLQGMeasure P γ hcirc μ)
    (hHm : Measurable H)
    (hH : ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC, hC ω φ = H ω φ) :
    ∀ᵐ ω ∂P, MatedCRTHarmonic.CellScaling.lqgArea γ (H ω) = μ ω := by
  apply LatticeProb.LQG.ae_lqgArea_eq_of_isLQGMeasure_ae
    ((HarmonicBalls.LPBridge.isLQGMeasure_iff P γ hcirc μ).1 hμ)
  apply ae_cone_circleAvg_eq_spatial hQ hHm hH LatticeProb.LQG.dyadicScale
  intro n
  unfold LatticeProb.LQG.dyadicScale
  positivity

end MatedCRT
