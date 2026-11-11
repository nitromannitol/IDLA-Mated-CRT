import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestriction
import MatedCRT.Proofs.Measurability.ConePairing

/-!
# The lateral process of a cone sample and of a whole-plane GFF is a.e. measurable

This discharges the pending measurability input `LateralProcessAEMeasurable` (Gaussian lateral
process of Definition 2.1, paper l.437-442). Both conjuncts are instances of
`MatedCRT.CirclePairing.aemeasurable_lateralProcess`: its jointly measurable version
`lateralVersionEval` is built from the a.s. continuous circle-average process, so only the pairing
measurability, the circle measurability and the a.s. continuity on `(0, ∞) × ℂ` are needed. Each of
these is a field of `IsQuantumCone` (resp. `IsWholePlaneGFF`), so no structure field is added.
-/

namespace MatedCRT.ConeMeanZeroRestriction

/-- **The lateral process is a.e. measurable for quantum cones and for whole-plane GFFs.** -/
theorem lateralProcessAEMeasurable_holds : LateralProcessAEMeasurable := by
  refine ⟨fun γ Ω _ P hC hcirc _ hQ => ?_, fun Ω _ P hC hcirc _ hG => ?_⟩
  · exact MatedCRT.CirclePairing.aemeasurable_lateralProcess hQ.measurable_pairing
      hQ.measurable_circle hQ.ae_continuousOn_circle
  · exact MatedCRT.CirclePairing.aemeasurable_lateralProcess hG.measurable_pairing
      hG.measurable_circle hG.ae_continuousOn_circle

end MatedCRT.ConeMeanZeroRestriction
