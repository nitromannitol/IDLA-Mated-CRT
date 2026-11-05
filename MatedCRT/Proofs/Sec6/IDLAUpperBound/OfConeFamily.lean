import MatedCRT.Proofs.Sec6.IDLAUpperBound.OfSteps
import MatedCRT.Proofs.Measurability.BoundaryLayer

/-!
# Proposition 6.1 without `BoundaryLayerMeasurableStep`

The measurability step of the carving of Proposition 6.1 (`BoundaryLayerMeasurableStep`) follows from the measurability
of the harmonic balls of the cone (`ConeFamilyAEMeasurableStep`, the step of Theorem 2.3) and Lemma 2.4
(`boundaryLayerMeasurableStep_of_coneFamilyAEMeasurable`, MatedCRT/Proofs/Measurability/BoundaryLayer.lean).
-/

namespace MatedCRT

/-- **Proposition 6.1** (prop:IDLA-upper-bound, line 2252) from Lemma 6.10, Proposition 5.1, Lemma 2.4 and the
measurability of the harmonic balls of the cone (`ConeFamilyAEMeasurableStep`). -/
theorem iDLAUpperBound_of_coneFamilyAEMeasurable (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮) (hfam : ConeFamilyAEMeasurableStep) (h24 : ConeHarmonicBallsUpToFixedTimeStmt) :
    IDLAUpperBoundStmt 𝒮 :=
  IDLAUpperBound.iDLAUpperBound_of_steps 𝒮 h610 h51
    (boundaryLayerMeasurableStep_of_coneFamilyAEMeasurable 𝒮 hfam h24) hfam h24

end MatedCRT
