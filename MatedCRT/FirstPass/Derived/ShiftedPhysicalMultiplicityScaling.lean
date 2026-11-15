import MatedCRT.FirstPass.Derived.ShiftedMeshMultiplicity

/-! # Scaling of shifted physical-grid edge multiplicities -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

/-- Simultaneous positive time and amplitude scaling preserves the entire
edge-multiplicity function on corresponding shifted physical grids. -/
theorem bmEdgeCount_shiftedPhysical_rescale {ε b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (θ : ℝ) (w w' : MatedCRTHarmonic.MatedCRT.Path2)
    (hw : ∀ t, w' t = (c * (w (b * t)).1, c * (w (b * t)).2)) :
    bmEdgeCount (ε / b) (fun t => (w' (t + (ε / b) * θ)).1)
      (fun t => (w' (t + (ε / b) * θ)).2) =
    bmEdgeCount ε (fun t => (w (t + ε * θ)).1)
      (fun t => (w (t + ε * θ)).2) := by
  funext j k
  apply Sec1.bmEdgeCount_rescale hb hc
  · intro t
    rw [hw]
    field_simp
  · intro t
    rw [hw]
    field_simp

/-- The corresponding shifted unit-mesh graphs have the same multiplicities. -/
theorem bmEdgeCount_shiftedMeshPath_rescale {ε b c : ℝ} (hε : 0 < ε)
    (hb : 0 < b) (hc : 0 < c) (θ : ℝ)
    (w w' : MatedCRTHarmonic.MatedCRT.Path2)
    (hw : ∀ t, w' t = (c * (w (b * t)).1, c * (w (b * t)).2)) :
    bmEdgeCount 1 (fun t => (LatticeProb.shiftedMeshPath w' (ε / b) θ t).1)
      (fun t => (LatticeProb.shiftedMeshPath w' (ε / b) θ t).2) =
    bmEdgeCount 1 (fun t => (LatticeProb.shiftedMeshPath w ε θ t).1)
      (fun t => (LatticeProb.shiftedMeshPath w ε θ t).2) := by
  rw [bmEdgeCount_shiftedMeshPath (div_pos hε hb), bmEdgeCount_shiftedMeshPath hε]
  exact bmEdgeCount_shiftedPhysical_rescale hb hc θ w w' hw

end MatedCRT
