import MatedCRT.FirstPass.Derived.JointShiftedPaperWalkTransfer

/-! # Paper walk witness estimates with exceptional meshes -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open LatticeProb MatedCRTHarmonic
open scoped ENNReal NNReal

namespace MatedCRT

/-- The physical walk witness is controlled by the vertex walk witness and the
probability of a nonpositive mesh. -/
theorem measure_paperWalk_witness_le_vertex_add_badMesh
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → JointShiftedWalkEnvironment) (R : Ω → ℝ)
    (U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))) (K : Set ℂ) (t : ℝ≥0∞) :
    P {ω | ∃ j, scaledWalkStart (jointShiftedWalkWitnessOf (X ω, R ω, j)).2 ∈ K ∧
      totalizedShiftedPhysicalWalkLaw (X ω).2.1.2.1 (X ω).2.1.2.2 (X ω).1 j
        {ξ | (jointShiftedWalkWitnessOf (X ω, R ω, j),
          scaledWalkPath (jointShiftedWalkWitnessOf (X ω, R ω, j)).2 ξ) ∈ U} ≤ t} ≤
    P {ω | ∃ j, scaledWalkStart (jointShiftedWalkWitnessOf (X ω, R ω, j)).2 ∈ K ∧
      jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf (X ω, R ω, j))
        {ξ | (jointShiftedWalkWitnessOf (X ω, R ω, j),
          scaledWalkPath (jointShiftedWalkWitnessOf (X ω, R ω, j)).2 ξ) ∈ U} ≤ t} +
      P {ω | (X ω).2.1.2.1 ≤ 0} := by
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  by_cases hmesh : 0 < (X ω).2.1.2.1
  · left
    obtain ⟨j, hj, hp⟩ := hω
    refine ⟨j, hj, ?_⟩
    rw [jointShiftedVertexWalkKernel_event_eq (jointShiftedWalkWitnessOf (X ω, R ω, j))
      hmesh U]
    exact hp
  · exact Or.inr (le_of_not_gt hmesh)

/-- Vanishing bad-mesh probability transfers a vanishing vertex walk witness
probability to the physical walk. -/
theorem tendsto_measure_paperWalk_witness_of_vertex_of_badMesh
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (l : Filter ι)
    (X : ι → Ω → JointShiftedWalkEnvironment) (R : ι → Ω → ℝ)
    (U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))) (K : Set ℂ) (t : ℝ≥0∞)
    (hvertex : Tendsto (fun i => P {ω | ∃ j,
      scaledWalkStart (jointShiftedWalkWitnessOf (X i ω, R i ω, j)).2 ∈ K ∧
      jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf (X i ω, R i ω, j))
        {ξ | (jointShiftedWalkWitnessOf (X i ω, R i ω, j),
          scaledWalkPath (jointShiftedWalkWitnessOf (X i ω, R i ω, j)).2 ξ) ∈ U} ≤ t}) l (𝓝 0))
    (hmesh : Tendsto (fun i => P {ω | (X i ω).2.1.2.1 ≤ 0}) l (𝓝 0)) :
    Tendsto (fun i => P {ω | ∃ j,
      scaledWalkStart (jointShiftedWalkWitnessOf (X i ω, R i ω, j)).2 ∈ K ∧
      totalizedShiftedPhysicalWalkLaw (X i ω).2.1.2.1 (X i ω).2.1.2.2 (X i ω).1 j
        {ξ | (jointShiftedWalkWitnessOf (X i ω, R i ω, j),
          scaledWalkPath (jointShiftedWalkWitnessOf (X i ω, R i ω, j)).2 ξ) ∈ U} ≤ t})
      l (𝓝 0) := by
  have hsum : Tendsto (fun i =>
      P {ω | ∃ j, scaledWalkStart (jointShiftedWalkWitnessOf (X i ω, R i ω, j)).2 ∈ K ∧
        jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf (X i ω, R i ω, j))
          {ξ | (jointShiftedWalkWitnessOf (X i ω, R i ω, j),
            scaledWalkPath (jointShiftedWalkWitnessOf (X i ω, R i ω, j)).2 ξ) ∈ U} ≤ t} +
        P {ω | (X i ω).2.1.2.1 ≤ 0}) l (𝓝 0) := by
    simpa only [add_zero] using hvertex.add hmesh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun i => measure_paperWalk_witness_le_vertex_add_badMesh P (X i) (R i) U K t)

end MatedCRT
