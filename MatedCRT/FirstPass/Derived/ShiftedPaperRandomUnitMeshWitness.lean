import MatedCRT.FirstPass.Derived.ShiftedPaperUnitMeshWitness

/-! # Random scaling of shifted walk witnesses -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LatticeProb
open scoped NNReal ENNReal

namespace MatedCRT

/-- Sample-dependent unit-mesh scaling transports the marked witness event,
up to the measure of the set where the scaling assumptions fail. -/
theorem measure_jointShiftedWalk_witness_unitMesh_rescale
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (b c θ : Ω → ℝ) (w w' : Ω → MatedCRTHarmonic.MatedCRT.Path2)
    (R : Ω → ℂ) (η η' : Ω → C(ℝ, ℂ)) (m r : Ω → ℝ)
    (G : Set Ω)
    (hG : ∀ ω ∈ G, 0 < b ω ∧ 0 < c ω ∧
      (∀ t, w' ω t = (c ω * (w ω (b ω * t)).1, c ω * (w ω (b ω * t)).2)) ∧
      (∀ t, η' ω t = (R ω)⁻¹ * η ω (b ω * t)) ∧
      MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1 (shiftedMeshPath (w ω) (b ω) (θ ω)) ∧
      MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1 (shiftedMeshPath (w' ω) 1 (θ ω)))
    (U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))) (K : Set ℂ) (t : ℝ≥0∞) :
    let E : Set Ω := {ω | ∃ k : ℤ, scaledWalkStart (((η' ω, 1, θ ω), m ω), r ω, k) ∈ K ∧
      jointShiftedVertexWalkKernel (w' ω, (((η' ω, 1, θ ω), m ω), r ω, k))
        {ξ | ((w' ω, (((η' ω, 1, θ ω), m ω), r ω, k)),
          scaledWalkPath (((η' ω, 1, θ ω), m ω), r ω, k) ξ) ∈ U} ≤ t}
    let F : Set Ω := {ω | ∃ k : ℤ, scaledWalkStart (((η ω, b ω, θ ω), m ω), r ω, k) ∈
      (fun z => (R ω)⁻¹ * z) ⁻¹' K ∧
      jointShiftedVertexWalkKernel (w ω, (((η ω, b ω, θ ω), m ω), r ω, k))
        {ξ | ((w' ω, (((η' ω, 1, θ ω), m ω), r ω, k)),
          ContinuousMap.const ℝ≥0 (R ω)⁻¹ *
            scaledWalkPath (((η ω, b ω, θ ω), m ω), r ω, k) ξ) ∈ U} ≤ t}
    P E ≤ P F + P Gᶜ ∧ P F ≤ P E + P Gᶜ := by
  dsimp only
  have heq : ∀ ω ∈ G,
      (∃ k : ℤ, scaledWalkStart (((η' ω, 1, θ ω), m ω), r ω, k) ∈ K ∧
        jointShiftedVertexWalkKernel (w' ω, (((η' ω, 1, θ ω), m ω), r ω, k))
          {ξ | ((w' ω, (((η' ω, 1, θ ω), m ω), r ω, k)),
            scaledWalkPath (((η' ω, 1, θ ω), m ω), r ω, k) ξ) ∈ U} ≤ t) ↔
      (∃ k : ℤ, scaledWalkStart (((η ω, b ω, θ ω), m ω), r ω, k) ∈
        (fun z => (R ω)⁻¹ * z) ⁻¹' K ∧
        jointShiftedVertexWalkKernel (w ω, (((η ω, b ω, θ ω), m ω), r ω, k))
          {ξ | ((w' ω, (((η' ω, 1, θ ω), m ω), r ω, k)),
            ContinuousMap.const ℝ≥0 (R ω)⁻¹ *
              scaledWalkPath (((η ω, b ω, θ ω), m ω), r ω, k) ξ) ∈ U} ≤ t) := by
    intro ω hω
    obtain ⟨hb, hc, hw, hη, h, h'⟩ := hG ω hω
    exact exists_jointShiftedWalk_witness_unitMesh_rescale hb hc (θ ω) (w ω) (w' ω) hw
      (R ω) (η ω) (η' ω) hη (m ω) (r ω) h h' U K t
  constructor
  · refine (measure_mono ?_).trans (measure_union_le _ _)
    intro ω hω
    by_cases hg : ω ∈ G
    · exact Or.inl ((heq ω hg).mp hω)
    · exact Or.inr hg
  · refine (measure_mono ?_).trans (measure_union_le _ _)
    intro ω hω
    by_cases hg : ω ∈ G
    · exact Or.inl ((heq ω hg).mpr hω)
    · exact Or.inr hg

end MatedCRT
