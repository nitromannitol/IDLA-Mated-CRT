import MatedCRT.FirstPass.Derived.ConeShiftedSelectedWalkLaw
import MatedCRT.FirstPass.Derived.ShiftedPaperInterpolation

/-! # Selected and vertex walk laws -/

set_option autoImplicit false

open MeasureTheory LatticeProb
open scoped NNReal

namespace MatedCRT

/-- The selected path law is the interpolated vertex-kernel law at the selected
integer, provided that the shifted graph is locally finite. -/
theorem shiftedSelectedWalkLaw_eq_map_vertexKernel
    (w : MatedCRTHarmonic.MatedCRT.Path2) (η : C(ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (m : ℝ≥0) (r : ℝ) (x : ℂ)
    (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1
      (shiftedMeshPath w ε θ)) :
    shiftedSelectedWalkLaw ε m (ε * θ) x η w =
      (jointShiftedVertexWalkKernel
        (w, (((η, ε, θ), (m : ℝ)), r,
          vertexOf ε (fun t => η (t + ε * θ)) x))).map
        (scaledWalkPath (((η, ε, θ), (m : ℝ)), r,
          vertexOf ε (fun t => η (t + ε * θ)) x)) := by
  rw [jointShiftedVertexWalkKernel_eq_totalizedShiftedPhysicalWalkLaw _ hε,
    totalizedShiftedPhysicalWalkLaw_of_locallyFinite _ _ _ _ h]
  unfold shiftedSelectedWalkLaw
  congr 1
  funext ξ
  apply ContinuousMap.ext
  intro t
  rw [scaledWalkPath_eq_paper_interpolatedWalk, interpPathCM_vertexPoint]

end MatedCRT
