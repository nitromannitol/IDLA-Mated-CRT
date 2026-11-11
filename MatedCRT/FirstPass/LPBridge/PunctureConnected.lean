import MatedCRT.FirstPass.Frozen.S4d
import LatticeProb.Analysis.PuncturedPlaneConnected

/-!
# Bridge: the frozen punctured-plane input `FrozenPunctureConnected`

Discharges the first-pass frozen input `FrozenPunctureConnected` (FirstPass/Frozen/S4d.lean) from the plane-topology
lemma `LatticeProb.IsOpen.isConnected_diff_singleton` (removing one point from a connected open planar set).
-/

namespace MatedCRT

/-- The frozen input `FrozenPunctureConnected` holds: for an open connected `U ⊆ ℂ` and `z ∈ U`, `U \ {z}` is connected.
Proved in `LatticeProb.IsOpen.isConnected_diff_singleton`; the hypothesis `z ∈ U` is not needed. -/
theorem frozenPunctureConnected_holds : FrozenPunctureConnected := by
  intro U hU hc z _
  exact LatticeProb.IsOpen.isConnected_diff_singleton hU hc z

end MatedCRT
