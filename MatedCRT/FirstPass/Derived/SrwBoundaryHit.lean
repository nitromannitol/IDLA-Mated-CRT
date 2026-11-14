import MatedCRT.FirstPass.Derived.SrwWalkLawBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15CBoundary

/-!
# Boundary hitting by the embedded simple random walk

The simple random walk reaches the cells meeting the frontier of a bounded open
set, provided its starting cell meets the set and the embedded graph is connected.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain

/-- The vertex walk hits the frontier cells of a bounded open set almost surely. -/
theorem srwLaw_hitTime_frontier_ne_top
    {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω) (hε : 0 ≤ ε)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    {x : ℤ} (hx : (H.cell x ∩ D).Nonempty) :
    srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x
      {ξ | hitTime (verticesMeeting H.cell (frontier D)) ξ ≠ ⊤} = 1 := by
  apply le_antisymm prob_le_one
  calc
    1 = (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).walkLaw x
        ((MatedCRTHarmonic.MatedCRT.graph ε ω hlf).vertexPath ⁻¹'
          {ξ | hitTime (verticesMeeting H.cell (frontier D)) ξ ≠ ⊤}) :=
      (t15c_walkLaw_hitTime_ne_top (H := H) hconn hDo hDb hx).symm
    _ ≤ _ := walkLaw_vertexPath_preimage_le_srwLaw hlf hε x _

end MatedCRT
