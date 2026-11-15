import MatedCRT.FirstPass.Derived.RandomMeshVertexFailure

/-! # Vertex failures with exceptional random meshes -/

set_option autoImplicit false

open Set Metric MeasureTheory Filter Topology

namespace MatedCRT

/-- Vertex failure is controlled by selected-cell failure and the event that the
random mesh is nonpositive. -/
theorem measure_vertexScoreFailure_le_selected_add_badMesh
    {Ω : Type} {X : Type*} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : Ω → ℝ) {ρ ρ' t : ℝ} (hρ : ρ < ρ')
    (score : ℂ × X → ℝ) (hcont : ∀ x, Continuous fun z => score (z, x))
    (q : Ω → ℤ → ℂ × X)
    (hq : ∀ᵐ ω ∂S.P, ∀ k, (q ω k).1 = vertexPoint (ε ω) (S.η ω) k) :
    S.P {ω | ∃ k, (q ω k).1 ∈ closedBall (0 : ℂ) ρ ∧ t < score (q ω k)} ≤
      S.P {ω | ∃ z ∈ closedBall (0 : ℂ) ρ',
        t < score (z, (q ω (vertexOf (ε ω) (S.η ω) z)).2)} +
      S.P {ω | ε ω ≤ 0} := by
  refine (measure_mono_ae ?_).trans (measure_union_le _ _)
  filter_upwards [hS.isAreaParametrized, hq] with ω harea hpoint
  intro hfail
  by_cases hpos : 0 < ε ω
  · exact Or.inl (vertexScoreFailure_subset_selected harea hpos hρ score hcont (q ω) hpoint hfail)
  · exact Or.inr (le_of_not_gt hpos)

/-- Vanishing selected-cell failure and nonpositive-mesh probabilities imply
vanishing vertex-failure probability, for arbitrary varying scores and meshes. -/
theorem tendsto_measure_vertexScoreFailure_of_selected_of_badMesh
    {Ω ι : Type} {X : Type*} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (l : Filter ι)
    (ε : ι → Ω → ℝ) {ρ ρ' : ℝ} (hρ : ρ < ρ') (t : ι → ℝ)
    (score : ι → ℂ × X → ℝ)
    (hcont : ∀ i x, Continuous fun z => score i (z, x))
    (q : ι → Ω → ℤ → ℂ × X)
    (hq : ∀ i, ∀ᵐ ω ∂S.P, ∀ k, (q i ω k).1 = vertexPoint (ε i ω) (S.η ω) k)
    (hselected : Tendsto (fun i => S.P {ω | ∃ z ∈ closedBall (0 : ℂ) ρ',
      t i < score i (z, (q i ω (vertexOf (ε i ω) (S.η ω) z)).2)}) l (𝓝 0))
    (hmesh : Tendsto (fun i => S.P {ω | ε i ω ≤ 0}) l (𝓝 0)) :
    Tendsto (fun i => S.P {ω | ∃ k, (q i ω k).1 ∈ closedBall (0 : ℂ) ρ ∧
      t i < score i (q i ω k)}) l (𝓝 0) := by
  have hsum := hselected.add hmesh
  simp only [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun i =>
      measure_vertexScoreFailure_le_selected_add_badMesh hS (ε i) hρ (score i) (hcont i)
        (q i) (hq i))

end MatedCRT
