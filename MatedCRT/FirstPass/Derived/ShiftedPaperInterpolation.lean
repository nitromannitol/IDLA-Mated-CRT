import MatedCRT.FirstPass.Derived.ShiftedPaperCell
import MatedCRT.FirstPass.Derived.JointShiftedPaperWalkLaw
import MatedCRT.Defs.Setting

/-! # Shifted-grid witnesses and embedded paper walks -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LatticeProb
open scoped NNReal

namespace MatedCRT

/-- The witness start is the scaled paper vertex of the time-translated curve. -/
theorem scaledWalkStart_eq_paper_vertex (η : C(ℝ, ℂ)) (ε θ m r : ℝ) (k : ℤ) :
    scaledWalkStart (((η, ε, θ), m), r, k) =
      r • vertexPoint ε (fun t => η (t + ε * θ)) k := by
  exact congrArg (fun z : ℂ => r • z)
    (shiftedGridAnchor_eq_vertexPoint_timeShift η ε θ k)

/-- The witness interpolation equals the paper interpolation for the same
integer walk and time-translated curve. -/
theorem scaledWalkPath_eq_paper_interpolatedWalk (η : C(ℝ, ℂ))
    (ε θ m r : ℝ) (k : ℤ) (ξ : ℕ → ℤ) (t : ℝ≥0) :
    scaledWalkPath (((η, ε, θ), m), r, k) ξ t =
      interpolatedWalk ε (fun s => η (s + ε * θ)) m ξ t := by
  simp only [scaledWalkPath, scaledWalkParameters, shiftedWalkPath,
    ConstantStepInterpolation.continuousPath_apply, ConstantStepInterpolation.path,
    shiftedGridAnchor_eq_vertexPoint_timeShift, interpolatedWalk,
    AffineMap.lineMap_apply_module, Complex.real_smul]

/-- Under local finiteness and positive mesh, the witness kernel gives the same
probability as the physical-grid walk law to every paper interpolation event. -/
theorem jointShiftedVertexWalkKernel_paper_interpolation_event
    (w : MatedCRTHarmonic.MatedCRT.Path2) (η : C(ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) (θ m r : ℝ) (k : ℤ)
    (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1
      (shiftedMeshPath w ε θ)) (B : Set (ℝ≥0 → ℂ)) :
    jointShiftedVertexWalkKernel (w, (((η, ε, θ), m), r, k))
        {ξ | (fun t => scaledWalkPath (((η, ε, θ), m), r, k) ξ t) ∈ B} =
      srwLaw (bmEdgeCount ε (fun t => (w (t + ε * θ)).1)
        (fun t => (w (t + ε * θ)).2)) k
        {ξ | interpolatedWalk ε (fun t => η (t + ε * θ)) m ξ ∈ B} := by
  rw [jointShiftedVertexWalkKernel_eq_totalizedShiftedPhysicalWalkLaw _ hε,
    totalizedShiftedPhysicalWalkLaw_of_locallyFinite _ _ _ _ h]
  congr 1
  ext ξ
  simp only [mem_ofPred_eq]
  have heq : (fun t => scaledWalkPath (((η, ε, θ), m), r, k) ξ t) =
      interpolatedWalk ε (fun t => η (t + ε * θ)) m ξ := by
    funext t
    exact scaledWalkPath_eq_paper_interpolatedWalk η ε θ m r k ξ t
  rw [heq]

end MatedCRT
