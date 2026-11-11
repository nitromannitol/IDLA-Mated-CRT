import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BoundaryProbability
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CenteredPotentialContinuous

/-! Boundary control for the Green potential on an origin-centered ball. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter
open scoped ENNReal

/-- Lemmas 3.3 and 2.17 give the continuum boundary estimate on a ball
centered at the origin, without assuming the potential-identification step. -/
theorem normalizedExitGreenPotential_boundary_small_centered
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} (hr : 0 < r) (hball : ball (0 : ℂ) r ⊆ ball 0 ρ)
    {t : ℝ} (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
      S.P {ω | ∃ x ∈ closedBall (0 : ℂ) r \ closedBall 0 r',
        t < |normalizedExitGreenPotential S r 0 ω x|} ≤ e := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply boundary_layer_small_in_probability S.P hr (normalizedExitGreenPotential S r 0) _ _ ht he
  · intro x hx
    by_cases hxi : x ∈ ball (0 : ℂ) r
    · exact normalizedExitGreenPotential_aemeasurable 𝒮 h33 h217 hγ hγ2 hρ hρ1 S hS hr hball hxi
    · have hz : (fun ω => normalizedExitGreenPotential S r 0 ω x) = fun _ => 0 := by
        funext ω
        exact normalizedExitGreenPotential_eq_zero_of_not_mem S hxi ω
      rw [hz]
      exact aemeasurable_const
  · filter_upwards [normalizedExitGreenPotential_ae_continuousOn_centered 𝒮 h217
      hγ hγ2 hρ hρ1 S hS hr hball] with ω hω
    exact ⟨hω, fun x hx => normalizedExitGreenPotential_eq_zero_on_sphere S hx ω⟩

end MatedCRT
