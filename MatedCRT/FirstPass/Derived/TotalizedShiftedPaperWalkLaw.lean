import MatedCRT.FirstPass.Derived.ShiftedMeshPaperWalkLaw

/-! # Totalized random walk law on a shifted time grid -/

noncomputable section

namespace MatedCRT

open MeasureTheory

/-- The translated physical-grid walk law, extended by zero when the shifted
unit graph is not locally finite. -/
def totalizedShiftedPhysicalWalkLaw (ε θ : ℝ)
    (w : MatedCRTHarmonic.MatedCRT.Path2) (x : ℤ) : Measure (ℕ → ℤ) := by
  classical
  exact if MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1
      (LatticeProb.shiftedMeshPath w ε θ) then
    srwLaw (bmEdgeCount ε (fun t => (w (t + ε * θ)).1)
      (fun t => (w (t + ε * θ)).2)) x
  else 0

/-- On locally finite shifted graphs the totalized law is the paper walk law. -/
theorem totalizedShiftedPhysicalWalkLaw_of_locallyFinite (ε θ : ℝ)
    (w : MatedCRTHarmonic.MatedCRT.Path2) (x : ℤ)
    (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1
      (LatticeProb.shiftedMeshPath w ε θ)) :
    totalizedShiftedPhysicalWalkLaw ε θ w x =
      srwLaw (bmEdgeCount ε (fun t => (w (t + ε * θ)).1)
        (fun t => (w (t + ε * θ)).2)) x := by
  classical
  simp only [totalizedShiftedPhysicalWalkLaw, ite_eq_left h]

/-- Outside local finiteness the totalized law has zero mass. -/
theorem totalizedShiftedPhysicalWalkLaw_of_not_locallyFinite (ε θ : ℝ)
    (w : MatedCRTHarmonic.MatedCRT.Path2) (x : ℤ)
    (h : ¬ MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1
      (LatticeProb.shiftedMeshPath w ε θ)) :
    totalizedShiftedPhysicalWalkLaw ε θ w x = 0 := by
  classical
  simp only [totalizedShiftedPhysicalWalkLaw, ite_eq_right h]

/-- For positive mesh the totalized law agrees with the graph vertex-walk law
on the locally finite domain. -/
theorem totalizedShiftedPhysicalWalkLaw_eq_map_walkLaw {ε : ℝ} (hε : 0 < ε)
    (θ : ℝ) (w : MatedCRTHarmonic.MatedCRT.Path2) (x : ℤ)
    (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite 1
      (LatticeProb.shiftedMeshPath w ε θ)) :
    totalizedShiftedPhysicalWalkLaw ε θ w x =
      ((MatedCRTHarmonic.MatedCRT.graph 1 (LatticeProb.shiftedMeshPath w ε θ) h).walkLaw x).map
        (MatedCRTHarmonic.MatedCRT.graph 1 (LatticeProb.shiftedMeshPath w ε θ) h).vertexPath := by
  rw [totalizedShiftedPhysicalWalkLaw_of_locallyFinite ε θ w x h]
  exact srwLaw_shiftedPhysical_eq_map_walkLaw hε θ w x h

end MatedCRT
