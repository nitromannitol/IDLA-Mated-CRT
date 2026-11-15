import MatedCRT.FirstPass.Derived.JointShiftedPaperWalkLaw
import LatticeProb.LQG.JointShiftedWalkRandomScale

/-! # Transfer of shifted walk witness estimates to the paper walk law -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open LatticeProb MatedCRTHarmonic
open scoped ENNReal NNReal

namespace MatedCRT

/-- At positive mesh, good-radius conditions agree for the two walk laws. -/
theorem ae_jointShiftedWalk_goodRadius_iff_paper
    (ν : Measure JointShiftedWalkEnvironment)
    (hmesh : ∀ᵐ e ∂ν, 0 < e.2.1.2.1)
    (U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))) (K : Set ℂ) (t : ℝ≥0∞) :
    (∀ᵐ e ∂ν, ∃ δ : ℝ, 0 < δ ∧ ∀ r j, 0 < r → r < δ →
      ¬ (scaledWalkStart (jointShiftedWalkWitnessOf (e, r, j)).2 ∈ K ∧
        jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf (e, r, j))
          {ξ | (jointShiftedWalkWitnessOf (e, r, j),
            scaledWalkPath (jointShiftedWalkWitnessOf (e, r, j)).2 ξ) ∈ U} ≤ t)) ↔
    (∀ᵐ e ∂ν, ∃ δ : ℝ, 0 < δ ∧ ∀ r j, 0 < r → r < δ →
      ¬ (scaledWalkStart (jointShiftedWalkWitnessOf (e, r, j)).2 ∈ K ∧
        totalizedShiftedPhysicalWalkLaw e.2.1.2.1 e.2.1.2.2 e.1 j
          {ξ | (jointShiftedWalkWitnessOf (e, r, j),
            scaledWalkPath (jointShiftedWalkWitnessOf (e, r, j)).2 ξ) ∈ U} ≤ t)) := by
  have heq : ∀ᵐ e ∂ν, ∀ r j,
      jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf (e, r, j))
          {ξ | (jointShiftedWalkWitnessOf (e, r, j),
            scaledWalkPath (jointShiftedWalkWitnessOf (e, r, j)).2 ξ) ∈ U} =
      totalizedShiftedPhysicalWalkLaw e.2.1.2.1 e.2.1.2.2 e.1 j
          {ξ | (jointShiftedWalkWitnessOf (e, r, j),
            scaledWalkPath (jointShiftedWalkWitnessOf (e, r, j)).2 ξ) ∈ U} := by
    filter_upwards [hmesh] with e he r j
    exact jointShiftedVertexWalkKernel_event_eq (jointShiftedWalkWitnessOf (e, r, j)) he U
  constructor <;> intro h
  · filter_upwards [h, heq] with e h he
    simpa only [he] using h
  · filter_upwards [h, heq] with e h he
    simpa only [he] using h

/-- Equal environment laws transfer existential witness-event measures to the paper law. -/
theorem measure_jointShiftedWalk_witness_eq_paper
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ν : Measure JointShiftedWalkEnvironment) (X : Ω → JointShiftedWalkEnvironment)
    (hX : AEMeasurable X P) (hlaw : Measure.map X P = ν)
    (hmesh : ∀ᵐ e ∂ν, 0 < e.2.1.2.1)
    (R : Ω → ℝ) (U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ)))
    (K : Set ℂ) (t : ℝ≥0∞) :
    P {ω | ∃ j, scaledWalkStart (jointShiftedWalkWitnessOf (X ω, R ω, j)).2 ∈ K ∧
      jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf (X ω, R ω, j))
        {ξ | (jointShiftedWalkWitnessOf (X ω, R ω, j),
          scaledWalkPath (jointShiftedWalkWitnessOf (X ω, R ω, j)).2 ξ) ∈ U} ≤ t} =
    P {ω | ∃ j, scaledWalkStart (jointShiftedWalkWitnessOf (X ω, R ω, j)).2 ∈ K ∧
      totalizedShiftedPhysicalWalkLaw (X ω).2.1.2.1 (X ω).2.1.2.2 (X ω).1 j
        {ξ | (jointShiftedWalkWitnessOf (X ω, R ω, j),
          scaledWalkPath (jointShiftedWalkWitnessOf (X ω, R ω, j)).2 ξ) ∈ U} ≤ t} := by
  have hmeshX : ∀ᵐ ω ∂P, 0 < (X ω).2.1.2.1 := by
    apply (ae_map_iff hX (measurableSet_lt measurable_const
      measurable_snd.fst.snd.fst)).mp
    rwa [hlaw]
  apply measure_congr
  filter_upwards [hmeshX] with ω hω
  apply propext
  constructor
  · rintro ⟨j, hj, hp⟩
    rw [jointShiftedVertexWalkKernel_event_eq (jointShiftedWalkWitnessOf (X ω, R ω, j)) hω U] at hp
    exact ⟨j, hj, hp⟩
  · rintro ⟨j, hj, hp⟩
    refine ⟨j, hj, ?_⟩
    rw [jointShiftedVertexWalkKernel_event_eq (jointShiftedWalkWitnessOf (X ω, R ω, j)) hω U]
    exact hp

end MatedCRT
