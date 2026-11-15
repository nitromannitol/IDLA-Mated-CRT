import MatedCRT.FirstPass.Derived.ShiftedPaperWitnessDilation

/-! # Dilation of marked shifted-walk events -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LatticeProb
open scoped NNReal ENNReal

namespace MatedCRT

/-- A witness-dependent event transforms with the complete rescaled witness
held fixed and the original walk path multiplied by the spatial scale. -/
theorem jointShiftedVertexWalkKernel_markedEvent_rescale
    {ε b c : ℝ} (hε : 0 < ε) (hb : 0 < b) (hc : 0 < c) (θ : ℝ)
    (w w' : MatedCRTHarmonic.MatedCRT.Path2)
    (hw : ∀ t, w' t = (c * (w (b * t)).1, c * (w (b * t)).2))
    (R : ℂ) (η η' : C(ℝ, ℂ)) (hη : ∀ t, η' t = R⁻¹ * η (b * t))
    (m r r' : ℝ) (k : ℤ)
    (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1 (shiftedMeshPath w ε θ))
    (h' : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1
      (shiftedMeshPath w' (ε / b) θ))
    (U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))) :
    jointShiftedVertexWalkKernel (w', (((η', ε / b, θ), m), r', k))
      {ξ | ((w', (((η', ε / b, θ), m), r', k)),
        scaledWalkPath (((η', ε / b, θ), m), r', k) ξ) ∈ U} =
    jointShiftedVertexWalkKernel (w, (((η, ε, θ), m), r, k))
      {ξ | ((w', (((η', ε / b, θ), m), r', k)),
        ContinuousMap.const ℝ≥0 R⁻¹ * scaledWalkPath (((η, ε, θ), m), r, k) ξ) ∈ U} := by
  rw [jointShiftedVertexWalkKernel_shiftedPhysical_rescale hε hb hc θ w w' hw
    η η' m m r r' k h h']
  congr 1
  ext ξ
  simp only [mem_ofPred_eq]
  have hp : scaledWalkPath (((η', ε / b, θ), m), r', k) ξ =
      ContinuousMap.const ℝ≥0 R⁻¹ * scaledWalkPath (((η, ε, θ), m), r, k) ξ := by
    ext t
    exact scaledWalkPath_shiftedPhysical_rescale hb θ R η η' hη m r r' k ξ t
  rw [hp]

/-- Starting-point constraints transform by the same spatial multiplication. -/
theorem scaledWalkStart_mem_shiftedPhysical_rescale {ε b : ℝ} (hb : 0 < b)
    (θ : ℝ) (R : ℂ) (η η' : C(ℝ, ℂ))
    (hη : ∀ t, η' t = R⁻¹ * η (b * t)) (m r : ℝ) (k : ℤ) (K : Set ℂ) :
    scaledWalkStart (((η', ε / b, θ), m), r, k) ∈ K ↔
      scaledWalkStart (((η, ε, θ), m), r, k) ∈ (fun z => R⁻¹ * z) ⁻¹' K := by
  rw [scaledWalkStart_shiftedPhysical_rescale hb θ R η η' hη m r k]
  rfl

end MatedCRT
