import MatedCRT.FirstPass.Derived.ShiftedPaperMarkedWitnessDilation

/-! # Unit-mesh scaling of shifted walk witnesses -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LatticeProb
open scoped NNReal ENNReal

namespace MatedCRT

/-- Scaling physical mesh `b` by time `b` transfers the entire existential
marked-walk witness event to unit mesh. The rescaled witness remains in the
marked event, and the start constraint uses the inverse spatial image of `K`. -/
theorem exists_jointShiftedWalk_witness_unitMesh_rescale
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (θ : ℝ)
    (w w' : MatedCRTHarmonic.MatedCRT.Path2)
    (hw : ∀ t, w' t = (c * (w (b * t)).1, c * (w (b * t)).2))
    (R : ℂ) (η η' : C(ℝ, ℂ)) (hη : ∀ t, η' t = R⁻¹ * η (b * t))
    (m r : ℝ)
    (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1 (shiftedMeshPath w b θ))
    (h' : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1 (shiftedMeshPath w' 1 θ))
    (U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))) (K : Set ℂ) (t : ℝ≥0∞) :
    (∃ k : ℤ, scaledWalkStart (((η', 1, θ), m), r, k) ∈ K ∧
      jointShiftedVertexWalkKernel (w', (((η', 1, θ), m), r, k))
        {ξ | ((w', (((η', 1, θ), m), r, k)),
          scaledWalkPath (((η', 1, θ), m), r, k) ξ) ∈ U} ≤ t) ↔
    (∃ k : ℤ, scaledWalkStart (((η, b, θ), m), r, k) ∈ (fun z => R⁻¹ * z) ⁻¹' K ∧
      jointShiftedVertexWalkKernel (w, (((η, b, θ), m), r, k))
        {ξ | ((w', (((η', 1, θ), m), r, k)),
          ContinuousMap.const ℝ≥0 R⁻¹ * scaledWalkPath (((η, b, θ), m), r, k) ξ) ∈ U} ≤ t) := by
  have hdiv : b / b = 1 := div_self (ne_of_gt hb)
  have h'' : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1
      (shiftedMeshPath w' (b / b) θ) := by simpa only [hdiv] using h'
  apply exists_congr
  intro k
  have hstart := scaledWalkStart_mem_shiftedPhysical_rescale (ε := b) hb θ R η η' hη m r k K
  have hprob := jointShiftedVertexWalkKernel_markedEvent_rescale hb hb hc θ w w' hw
    R η η' hη m r r k h h'' U
  simp only [hdiv] at hstart hprob
  rw [hstart, hprob]

end MatedCRT
