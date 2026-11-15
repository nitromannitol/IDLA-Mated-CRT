import MatedCRT.FirstPass.Derived.SrwWalkLawBridge
import MatedCRT.Proofs.Sec1.Scaling
import LatticeProb.LQG.ShiftedMeshEdgeCode

/-! # Multiplicities on a shifted time grid -/

noncomputable section

namespace MatedCRT

open MatedCRTHarmonic

/-- The unit-mesh graph of the shifted boundary path has the physical-mesh
multiplicities of the boundary path translated by the shift. In particular,
this equality retains the multiplicities of parallel edges. -/
theorem bmEdgeCount_shiftedMeshPath {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (w : MatedCRTHarmonic.MatedCRT.Path2) :
    bmEdgeCount 1
        (fun t => (LatticeProb.shiftedMeshPath w ε θ t).1)
        (fun t => (LatticeProb.shiftedMeshPath w ε θ t).2) =
      bmEdgeCount ε (fun t => (w (t + ε * θ)).1)
        (fun t => (w (t + ε * θ)).2) := by
  funext j k
  have h := Sec1.bmEdgeCount_rescale (ε := ε) (b := ε) (c := 1) hε zero_lt_one
    (fun t => (w (t + ε * θ)).1) (fun t => (w (t + ε * θ)).2)
    (fun t => (LatticeProb.shiftedMeshPath w ε θ t).1)
    (fun t => (LatticeProb.shiftedMeshPath w ε θ t).2)
    (fun t => by simp only [LatticeProb.shiftedMeshPath_apply, one_mul]; congr 1; ring)
    (fun t => by simp only [LatticeProb.shiftedMeshPath_apply, one_mul]; congr 1; ring) j k
  simpa only [div_self hε.ne'] using h

/-- The simple random walk laws agree under the shifted-grid multiplicity
identification, for every starting vertex. -/
theorem srwLaw_shiftedMeshPath {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (w : MatedCRTHarmonic.MatedCRT.Path2) (x : ℤ) :
    srwLaw (bmEdgeCount 1
        (fun t => (LatticeProb.shiftedMeshPath w ε θ t).1)
        (fun t => (LatticeProb.shiftedMeshPath w ε θ t).2)) x =
      srwLaw (bmEdgeCount ε (fun t => (w (t + ε * θ)).1)
        (fun t => (w (t + ε * θ)).2)) x := by
  rw [bmEdgeCount_shiftedMeshPath hε θ w]

end MatedCRT
