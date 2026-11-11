import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.MeasureLaw
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.LQGScaling

/-! # Cone-family measurability from the numbered estimates -/

namespace MatedCRT

/-- The measurability step follows from the cone volume-growth estimate,
strict growth, quantum-cone scaling and the LQG measure properties. -/
theorem coneFamilyAEMeasurableStep_of_volumeGrowth_and_lqgProperties
    (h27 : VolumeGrowthStmt) (hgrow : ConeHarmonicBallStrictGrowthStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    ConeFamilyAEMeasurableStep :=
  coneFamilyAEMeasurableStep_of_scaling h27 hgrow hscale
    (coneLQGScalingStep_of_steps h22 (coneScaleRadiusPosStep_of_input hscale))

end MatedCRT
