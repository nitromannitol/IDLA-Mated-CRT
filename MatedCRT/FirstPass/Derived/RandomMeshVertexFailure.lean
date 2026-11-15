import MatedCRT.FirstPass.Derived.VertexSourceFailure

/-! # Random-mesh transfer of vertex failures -/

set_option autoImplicit false

open Set Metric MeasureTheory

namespace MatedCRT

/-- A selected-cell failure controls the probability of a vertex failure, for a
positive random mesh and almost surely identified vertex positions. -/
theorem measure_vertexScoreFailure_le_selected_of_valid
    {Ω : Type} {X : Type*} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : Ω → ℝ) (hε : ∀ᵐ ω ∂S.P, 0 < ε ω)
    {ρ ρ' t : ℝ} (hρ : ρ < ρ')
    (score : ℂ × X → ℝ) (hcont : ∀ x, Continuous fun z => score (z, x))
    (q : Ω → ℤ → ℂ × X)
    (hq : ∀ᵐ ω ∂S.P, ∀ k, (q ω k).1 = vertexPoint (ε ω) (S.η ω) k) :
    S.P {ω | ∃ k, (q ω k).1 ∈ closedBall (0 : ℂ) ρ ∧ t < score (q ω k)} ≤
      S.P {ω | ∃ z ∈ closedBall (0 : ℂ) ρ',
        t < score (z, (q ω (vertexOf (ε ω) (S.η ω) z)).2)} := by
  apply measure_mono_ae
  filter_upwards [hS.isAreaParametrized, hε, hq] with ω harea hpos hpoint
  exact vertexScoreFailure_subset_selected harea hpos hρ score hcont (q ω) hpoint

end MatedCRT
