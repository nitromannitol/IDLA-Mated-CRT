import MatedCRT.FirstPass.Derived.ShiftedPaperInterpolation
import MatedCRT.FirstPass.Derived.ConeScaledStoppedLaw

/-! # Dilation of shifted physical-grid walks -/

set_option autoImplicit false

noncomputable section

open MeasureTheory LatticeProb
open scoped NNReal

namespace MatedCRT

/-- Boundary time dilation and positive amplitude scaling preserve the walk law
on corresponding translated physical grids. -/
theorem srwLaw_shiftedPhysical_rescale {ε b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (θ : ℝ) (w w' : MatedCRTHarmonic.MatedCRT.Path2)
    (hw : ∀ t, w' t = (c * (w (b * t)).1, c * (w (b * t)).2)) (k : ℤ) :
    srwLaw (bmEdgeCount (ε / b) (fun t => (w' (t + (ε / b) * θ)).1)
      (fun t => (w' (t + (ε / b) * θ)).2)) k =
    srwLaw (bmEdgeCount ε (fun t => (w (t + ε * θ)).1)
      (fun t => (w (t + ε * θ)).2)) k := by
  apply ConeScaledWalkData.srwLaw_rescale hb hc
  · intro t
    rw [hw]
    field_simp
  · intro t
    rw [hw]
    field_simp

/-- The corresponding translated curve vertices have the stated spatial scaling. -/
theorem vertexPoint_shiftedPhysical_rescale {ε b : ℝ} (hb : 0 < b) (θ : ℝ)
    (R : ℂ) (η η' : ℝ → ℂ) (hη : ∀ t, η' t = R⁻¹ * η (b * t)) (k : ℤ) :
    vertexPoint (ε / b) (fun t => η' (t + (ε / b) * θ)) k =
      R⁻¹ * vertexPoint ε (fun t => η (t + ε * θ)) k := by
  apply ConeScaledWalkData.vertexPoint_rescale hb
  intro t
  rw [hη]
  congr 1
  congr 1
  field_simp

/-- The entire interpolated path has the same spatial scaling at a common speed. -/
theorem interpolatedWalk_shiftedPhysical_rescale {ε b : ℝ} (hb : 0 < b) (θ : ℝ)
    (R : ℂ) (η η' : ℝ → ℂ) (hη : ∀ t, η' t = R⁻¹ * η (b * t))
    (m : ℝ) (ξ : ℕ → ℤ) (t : ℝ≥0) :
    interpolatedWalk (ε / b) (fun s => η' (s + (ε / b) * θ)) m ξ t =
      R⁻¹ * interpolatedWalk ε (fun s => η (s + ε * θ)) m ξ t := by
  unfold interpolatedWalk
  simp only [vertexPoint_shiftedPhysical_rescale hb θ R η η' hη]
  ring

/-- On locally finite shifted grids, the joint witness kernels agree under
simultaneous time and positive boundary-amplitude scaling. -/
theorem jointShiftedVertexWalkKernel_shiftedPhysical_rescale
    {ε b c : ℝ} (hε : 0 < ε) (hb : 0 < b) (hc : 0 < c) (θ : ℝ)
    (w w' : MatedCRTHarmonic.MatedCRT.Path2)
    (hw : ∀ t, w' t = (c * (w (b * t)).1, c * (w (b * t)).2))
    (η η' : C(ℝ, ℂ)) (m m' r r' : ℝ) (k : ℤ)
    (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1 (shiftedMeshPath w ε θ))
    (h' : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1
      (shiftedMeshPath w' (ε / b) θ)) :
    jointShiftedVertexWalkKernel (w', (((η', ε / b, θ), m'), r', k)) =
      jointShiftedVertexWalkKernel (w, (((η, ε, θ), m), r, k)) := by
  rw [jointShiftedVertexWalkKernel_eq_totalizedShiftedPhysicalWalkLaw _ (div_pos hε hb),
    jointShiftedVertexWalkKernel_eq_totalizedShiftedPhysicalWalkLaw _ hε,
    totalizedShiftedPhysicalWalkLaw_of_locallyFinite _ _ _ _ h',
    totalizedShiftedPhysicalWalkLaw_of_locallyFinite _ _ _ _ h]
  exact srwLaw_shiftedPhysical_rescale hb hc θ w w' hw k

end MatedCRT
