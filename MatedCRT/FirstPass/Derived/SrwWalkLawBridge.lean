import MatedCRT.FirstPass.Derived.SrwChainBridge
import MatedCRT.FirstPass.Derived.SrwStepBridge
import LatticeProb.LQG.ChainLumping

/-!
# Simple random walk on the mated-CRT map as the vertex path of the edge-end walk

For `ε ≥ 0` and the locally finite mated-CRT multigraph `G = MatedCRT.graph ε ω h`, the law `srwLaw m x` of simple
random walk on the edge count `m = bmEdgeCount ε L R` (Definition 1.1) is the image, under the vertex path
`G.vertexPath`, of Bonanno's edge-end walk law `G.walkLaw x`. Consequently every measurable event of vertex paths has
the same probability under the two walks. Proof: the one-step identity `srwKernel_bmEdgeCount_eq`, the Dynkin lumping
of the chain on `V ⊕ Dart` onto its vertices (`LatticeProb.LQG.walkLaw_map_vertexPath`), and
`chainLaw_srwKernel` (`srwLaw m x` is the chain law of `srwKernel m`).
-/

namespace MatedCRT

open MeasureTheory

variable {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2} (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
include h

/-- `srwLaw` of the edge count is the vertex-path image of the edge-end walk law. -/
theorem srwLaw_bmEdgeCount_eq_map_walkLaw (hε : 0 ≤ ε) (x : ℤ) :
    srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x =
      ((MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw x).map
        (MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath := by
  rw [← chainLaw_srwKernel]
  exact (LatticeProb.LQG.walkLaw_map_vertexPath (MatedCRTHarmonic.MatedCRT.graph ε ω h) _
    (fun y => srwKernel_bmEdgeCount_eq h hε y) x).symm

/-- Events of vertex paths have the same probability under `srwLaw` and under the edge-end walk. -/
theorem srwLaw_bmEdgeCount_apply_eq_walkLaw (hε : 0 ≤ ε) (x : ℤ) {B : Set (ℕ → ℤ)} (hB : MeasurableSet B) :
    srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x B =
      (MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw x
        ((MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath ⁻¹' B) := by
  rw [← chainLaw_srwKernel]
  exact (LatticeProb.LQG.walkLaw_vertexPath_preimage (MatedCRTHarmonic.MatedCRT.graph ε ω h) _
    (fun y => srwKernel_bmEdgeCount_eq h hε y) x hB).symm

/-- Lower bounds transfer from the edge-end walk to `srwLaw` for every set of vertex paths, measurable or not. -/
theorem walkLaw_vertexPath_preimage_le_srwLaw (hε : 0 ≤ ε) (x : ℤ) (B : Set (ℕ → ℤ)) :
    (MatedCRTHarmonic.MatedCRT.graph ε ω h).walkLaw x ((MatedCRTHarmonic.MatedCRT.graph ε ω h).vertexPath ⁻¹' B) ≤
      srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x B := by
  rw [srwLaw_bmEdgeCount_eq_map_walkLaw h hε]
  exact Measure.le_map_apply (LatticeProb.LQG.measurable_vertexPath' _).aemeasurable B

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.srwLaw_bmEdgeCount_eq_map_walkLaw
#print axioms MatedCRT.srwLaw_bmEdgeCount_apply_eq_walkLaw
#print axioms MatedCRT.walkLaw_vertexPath_preimage_le_srwLaw
