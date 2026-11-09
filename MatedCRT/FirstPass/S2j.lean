import MatedCRT.FirstPass.S2g.Section6
import MatedCRT.FirstPass.S2i.CanonicalFactor

/-!
# FirstPass S2j: `ConeFamilyAEMeasurableStep` (measurability of the cone harmonic balls)

Task fp-S2j-cone-family-aemeasurable (worker q4). The step `ConeFamilyAEMeasurableStep`
(`Steps/Sec2/ConeHarmonicBalls.lean`, Theorem 2.3 measurability) is proved from the canonical factorization of
the cone harmonic balls:

* `coneCanonicalFactor_proved` (FirstPass/S2i/CanonicalFactor.lean, z2) gives `ConeCanonicalFactorStep` from the
  canonical half-ball existence `ConeCanonicalHalfBallStep` (the good-event construction of
  `notes/fp-gaps/G-S2-measurable.md`, Section 3), the closure containment `ConeHalfBallClosureInsideStep`, the
  volume growth `VolumeGrowthStmt`, and the frozen cone externals `ConeCircleLawUniqueStep`, `ConeReferenceExistsStep`;
* `coneFamilyAEMeasurableStep_of_factor` (FirstPass/S2g/Section6.lean, q1) gives `ConeFamilyAEMeasurableStep` from
  `ConeCanonicalFactorStep`, the quantum cone scaling law `QuantumConeScalingInput` (the rescaled conjunct,
  Section 5 of the notes) and the LQG measure property `LQGMeasurePropertiesStmt`.

The open steps are explicit hypotheses; no new mathematics is introduced here.
-/

namespace MatedCRT

/-- **`ConeFamilyAEMeasurableStep` (FirstPass S2j, q4).** Under the explicit hypotheses `ConeCanonicalHalfBallStep`,
`ConeHalfBallClosureInsideStep`, `VolumeGrowthStmt`, `ConeCircleLawUniqueStep`, `ConeReferenceExistsStep`,
`QuantumConeScalingInput` and `LQGMeasurePropertiesStmt`, the harmonic balls of the cone are a.e. measurable: the
pair (circle average process, family process) is a.e. measurable for the unscaled family and for every rescaled family. -/
theorem coneFamilyAEMeasurable_proved
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep) (h27 : VolumeGrowthStmt)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    ConeFamilyAEMeasurableStep :=
  coneFamilyAEMeasurableStep_of_factor (coneCanonicalFactor_proved hcan hcl h27 hE1 hE2) hscale h22

end MatedCRT
