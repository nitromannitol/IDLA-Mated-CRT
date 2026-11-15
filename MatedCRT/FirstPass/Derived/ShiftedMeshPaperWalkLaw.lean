import MatedCRT.FirstPass.Derived.ShiftedMeshMultiplicity

/-! # Random walk law on a shifted time grid -/

noncomputable section

namespace MatedCRT

open MeasureTheory

/-- The walk on the translated physical grid has the vertex-path law of the
unit-mesh graph of the shifted boundary path, with all edge multiplicities. -/
theorem srwLaw_shiftedPhysical_eq_map_walkLaw {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (w : MatedCRTHarmonic.MatedCRT.Path2) (x : ℤ)
    (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1
      (LatticeProb.shiftedMeshPath w ε θ)) :
    srwLaw (bmEdgeCount ε (fun t => (w (t + ε * θ)).1)
      (fun t => (w (t + ε * θ)).2)) x =
      ((MatedCRTHarmonic.MatedCRT.graph 1 (LatticeProb.shiftedMeshPath w ε θ) h).walkLaw x).map
        (MatedCRTHarmonic.MatedCRT.graph 1 (LatticeProb.shiftedMeshPath w ε θ) h).vertexPath := by
  rw [← srwLaw_shiftedMeshPath hε θ w x]
  exact srwLaw_bmEdgeCount_eq_map_walkLaw h (by norm_num) x

/-- Measurable vertex-path events have the same probability under the two
walk constructions on the shifted grid. -/
theorem srwLaw_shiftedPhysical_apply_eq_walkLaw {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (w : MatedCRTHarmonic.MatedCRT.Path2) (x : ℤ)
    (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1
      (LatticeProb.shiftedMeshPath w ε θ))
    {B : Set (ℕ → ℤ)} (hB : MeasurableSet B) :
    srwLaw (bmEdgeCount ε (fun t => (w (t + ε * θ)).1)
      (fun t => (w (t + ε * θ)).2)) x B =
      (MatedCRTHarmonic.MatedCRT.graph 1 (LatticeProb.shiftedMeshPath w ε θ) h).walkLaw x
        ((MatedCRTHarmonic.MatedCRT.graph 1 (LatticeProb.shiftedMeshPath w ε θ) h).vertexPath ⁻¹' B) := by
  rw [← srwLaw_shiftedMeshPath hε θ w x]
  exact srwLaw_bmEdgeCount_apply_eq_walkLaw h (by norm_num) x hB

end MatedCRT
