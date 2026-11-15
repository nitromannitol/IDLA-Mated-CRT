import MatedCRT.FirstPass.Derived.TotalizedShiftedPaperWalkLaw
import LatticeProb.LQG.JointShiftedWalkWitness

/-! # Joint shifted paper walk law -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open LatticeProb MatedCRTHarmonic
open scoped ENNReal NNReal

namespace MatedCRT

/-- At positive mesh the joint vertex kernel is the totalized physical-grid walk law. -/
theorem jointShiftedVertexWalkKernel_eq_totalizedShiftedPhysicalWalkLaw
    (q : JointShiftedWalkWitness) (hε : 0 < q.2.1.1.2.1) :
    jointShiftedVertexWalkKernel q =
      totalizedShiftedPhysicalWalkLaw q.2.1.1.2.1 q.2.1.1.2.2 q.1 q.2.2.2 := by
  by_cases h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1
      (shiftedMeshPath q.1 q.2.1.1.2.1 q.2.1.1.2.2)
  · rw [jointShiftedVertexWalkKernel_apply q h,
      totalizedShiftedPhysicalWalkLaw_eq_map_walkLaw hε q.2.1.1.2.2 q.1 q.2.2.2 h]
  · rw [jointShiftedVertexWalkKernel_apply_of_not_locallyFinite q h,
      totalizedShiftedPhysicalWalkLaw_of_not_locallyFinite _ _ _ _ h]

/-- The paper law gives the same probability to every joint path event. -/
theorem jointShiftedVertexWalkKernel_event_eq
    (q : JointShiftedWalkWitness) (hε : 0 < q.2.1.1.2.1)
    (U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))) :
    jointShiftedVertexWalkKernel q {ξ | (q, scaledWalkPath q.2 ξ) ∈ U} =
      totalizedShiftedPhysicalWalkLaw q.2.1.1.2.1 q.2.1.1.2.2 q.1 q.2.2.2
        {ξ | (q, scaledWalkPath q.2 ξ) ∈ U} := by
  rw [jointShiftedVertexWalkKernel_eq_totalizedShiftedPhysicalWalkLaw q hε]

/-- Positive-mesh paper walk witnesses form a measurable set. -/
theorem measurableSet_positiveMesh_paperWalk_witness
    {U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))} (hU : MeasurableSet U)
    {K : Set ℂ} (hK : MeasurableSet K) (t : ℝ≥0∞) :
    MeasurableSet {q : JointShiftedWalkWitness | 0 < q.2.1.1.2.1 ∧
      scaledWalkStart q.2 ∈ K ∧
      totalizedShiftedPhysicalWalkLaw q.2.1.1.2.1 q.2.1.1.2.2 q.1 q.2.2.2
        {ξ | (q, scaledWalkPath q.2 ξ) ∈ U} ≤ t} := by
  have hp : MeasurableSet {q : JointShiftedWalkWitness | 0 < q.2.1.1.2.1} :=
    measurableSet_lt measurable_const measurable_snd.fst.fst.snd.fst
  have heq : {q : JointShiftedWalkWitness | 0 < q.2.1.1.2.1 ∧
      scaledWalkStart q.2 ∈ K ∧
      totalizedShiftedPhysicalWalkLaw q.2.1.1.2.1 q.2.1.1.2.2 q.1 q.2.2.2
        {ξ | (q, scaledWalkPath q.2 ξ) ∈ U} ≤ t} =
      {q : JointShiftedWalkWitness | 0 < q.2.1.1.2.1} ∩
      {q : JointShiftedWalkWitness | scaledWalkStart q.2 ∈ K ∧
        jointShiftedVertexWalkKernel q {ξ | (q, scaledWalkPath q.2 ξ) ∈ U} ≤ t} := by
    ext q
    simp only [mem_ofPred_eq, mem_inter_iff]
    by_cases hε : 0 < q.2.1.1.2.1
    · rw [jointShiftedVertexWalkKernel_event_eq q hε]
    · simp only [hε, false_and]
  rw [heq]
  exact hp.inter (measurableSet_jointShiftedWalk_witness hU hK t)

end MatedCRT
