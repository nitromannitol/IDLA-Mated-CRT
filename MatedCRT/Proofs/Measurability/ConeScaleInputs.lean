import MatedCRT.Proofs.Sec2.ConeScaleInvariance.Main
import MatedCRT.Proofs.Measurability.ConeRescaledCircle

/-!
# Section 2 reductions without `ConeRescaledCircleAEMeasurableStep`

`ConeRescaledCircleAEMeasurableStep` follows from `ConeScaleRadiusPosStep`
(`coneRescaledCircleAEMeasurableStep_of_pos`, MatedCRT/Proofs/Measurability/ConeRescaledCircle.lean), which the
reductions of Lemmas 2.5, 2.6, Theorem 2.3 and of `ConeFamilyAEMeasurableStep` already assume.
-/

namespace MatedCRT

/-- **`ConeFamilyAEMeasurableStep`** (the step of Theorem 2.3) from Fact 2.2, the quantum cone scaling input, strict
growth, positivity of the cone scale radius and the functional step of the half-ball family. -/
theorem coneFamilyAEMeasurableStep_of_inputs (hscale : QuantumConeScalingInput)
    (hgrow : ConeHarmonicBallStrictGrowthStep) (h22 : LQGMeasurePropertiesStmt) (hpos : ConeScaleRadiusPosStep)
    (hfun : ConeHalfBallFamilyFunctionalStep) : ConeFamilyAEMeasurableStep :=
  coneFamilyAEMeasurableStep_of_steps hscale hgrow (coneLQGScalingStep_of_steps h22 hpos)
    (coneRescaledCircleAEMeasurableStep_of_pos hpos) hfun

/-- **Lemma 2.5** from its inputs, without `ConeRescaledCircleAEMeasurableStep`. -/
theorem coneScaleInvarianceUpToFixedTime_of_scaleRadiusPos (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) (hpos : ConeScaleRadiusPosStep) (hgrow : ConeHarmonicBallStrictGrowthStep)
    (hfun : ConeHalfBallFamilyFunctionalStep) : ConeScaleInvarianceUpToFixedTimeStmt :=
  coneScaleInvarianceUpToFixedTime_of_inputs hscale h22 hpos hgrow (coneRescaledCircleAEMeasurableStep_of_pos hpos)
    hfun

/-- **Lemma 2.6** from its inputs, without `ConeRescaledCircleAEMeasurableStep`. -/
theorem coneScaleInvariance_of_scaleRadiusPos (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (hpos : ConeScaleRadiusPosStep) (hfun : ConeHarmonicBallFunctionalStep) : ConeScaleInvarianceStmt :=
  coneScaleInvariance_of_inputs hscale h22 hpos (coneRescaledCircleAEMeasurableStep_of_pos hpos) hfun

/-- **Theorem 2.3** from its inputs, without `ConeRescaledCircleAEMeasurableStep`. -/
theorem coneHarmonicBalls_of_scaleRadiusPos (h0 : WholePlaneLogLQGExistenceStep)
    (h1 : WholePlaneConeHarmonicBallsStep) (h2 : WholePlaneHarmonicBallsSmallTimeStep) (h3 : ConeRestrictionStep)
    (h4 : ConeHarmonicBallLocalityStep) (hgrow : ConeHarmonicBallStrictGrowthStep) (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) (hpos : ConeScaleRadiusPosStep) (hfun : ConeHalfBallFamilyFunctionalStep) :
    ConeHarmonicBallsStmt :=
  coneHarmonicBalls_of_inputs h0 h1 h2 h3 h4 hgrow hscale h22 hpos (coneRescaledCircleAEMeasurableStep_of_pos hpos)
    hfun

end MatedCRT
