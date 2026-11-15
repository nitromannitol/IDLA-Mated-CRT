import MatedCRT.FirstPass.Derived.ShiftedPaperWalkDilation

/-! # Dilation of shifted walk witnesses -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LatticeProb
open scoped NNReal

namespace MatedCRT

/-- The scaled witness start transforms with the embedding curve. -/
theorem scaledWalkStart_shiftedPhysical_rescale {ε b : ℝ} (hb : 0 < b)
    (θ : ℝ) (R : ℂ) (η η' : C(ℝ, ℂ))
    (hη : ∀ t, η' t = R⁻¹ * η (b * t)) (m r : ℝ) (k : ℤ) :
    scaledWalkStart (((η', ε / b, θ), m), r, k) =
      R⁻¹ * scaledWalkStart (((η, ε, θ), m), r, k) := by
  rw [scaledWalkStart_eq_paper_vertex, scaledWalkStart_eq_paper_vertex,
    vertexPoint_shiftedPhysical_rescale hb θ R η η' hη]
  simp only [Complex.real_smul]
  ring

/-- The witness path transforms pointwise with the embedding curve. -/
theorem scaledWalkPath_shiftedPhysical_rescale {ε b : ℝ} (hb : 0 < b)
    (θ : ℝ) (R : ℂ) (η η' : C(ℝ, ℂ))
    (hη : ∀ t, η' t = R⁻¹ * η (b * t)) (m r r' : ℝ) (k : ℤ)
    (ξ : ℕ → ℤ) (t : ℝ≥0) :
    scaledWalkPath (((η', ε / b, θ), m), r', k) ξ t =
      R⁻¹ * scaledWalkPath (((η, ε, θ), m), r, k) ξ t := by
  rw [scaledWalkPath_eq_paper_interpolatedWalk, scaledWalkPath_eq_paper_interpolatedWalk]
  exact interpolatedWalk_shiftedPhysical_rescale hb θ R η η' hη m ξ t

/-- A shifted witness path event has the same probability after scaling the
boundary paths, mesh and embedding curve. -/
theorem jointShiftedVertexWalkKernel_pathEvent_rescale
    {ε b c : ℝ} (hε : 0 < ε) (hb : 0 < b) (hc : 0 < c) (θ : ℝ)
    (w w' : MatedCRTHarmonic.MatedCRT.Path2)
    (hw : ∀ t, w' t = (c * (w (b * t)).1, c * (w (b * t)).2))
    (R : ℂ) (η η' : C(ℝ, ℂ)) (hη : ∀ t, η' t = R⁻¹ * η (b * t))
    (m r r' : ℝ) (k : ℤ)
    (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1 (shiftedMeshPath w ε θ))
    (h' : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1
      (shiftedMeshPath w' (ε / b) θ)) (B : Set (ℝ≥0 → ℂ)) :
    jointShiftedVertexWalkKernel (w', (((η', ε / b, θ), m), r', k))
      {ξ | (fun t => scaledWalkPath (((η', ε / b, θ), m), r', k) ξ t) ∈ B} =
    jointShiftedVertexWalkKernel (w, (((η, ε, θ), m), r, k))
      {ξ | (fun t => R⁻¹ * scaledWalkPath (((η, ε, θ), m), r, k) ξ t) ∈ B} := by
  rw [jointShiftedVertexWalkKernel_shiftedPhysical_rescale hε hb hc θ w w' hw
    η η' m m r r' k h h']
  congr 1
  ext ξ
  simp only [mem_ofPred_eq]
  have hp : (fun t => scaledWalkPath (((η', ε / b, θ), m), r', k) ξ t) =
      (fun t => R⁻¹ * scaledWalkPath (((η, ε, θ), m), r, k) ξ t) := by
    funext t
    exact scaledWalkPath_shiftedPhysical_rescale hb θ R η η' hη m r r' k ξ t
  rw [hp]

end MatedCRT
