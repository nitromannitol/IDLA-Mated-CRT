import MatedCRT.FirstPass.S7x
import MatedCRT.FirstPass.S7y.Final

/-!
# Proposition 7.1 with the Borel form of the Lemma 2.9 hypothesis

The `h29` hypothesis of Lemma 2.9 is restated for Borel `D`:
`CountingMeasureConvergenceStmt 𝒮` (MatedCRT/Draft/Section2.lean:143, BG20 Lemma A.4) quantifies over arbitrary
`D ⊆ B_ρ`, while BG20 states the result for Borel `D`. The Borel form `CountingMeasureConvergenceMeasurableStmt` is
defined in `MatedCRT/FirstPass/S7y/Stmt.lean`, with `countingMeasureConvergenceMeasurable_of_stmt` (the Draft statement
implies it).

`firstPass_7_1_support_measurable` below is `firstPass_7_1_support` (MatedCRT/FirstPass/S7x.lean:105) with `h29` in the
Borel form. Its only use of `h29` is the Lemma 6.8 chain through `constantOrderLowerBoundDivLog_final_meas`
(`MatedCRT/FirstPass/S7y/Final.lean`), a measurable-binder copy of
`constantOrderLowerBoundDivLog_final` (Proofs/Sec6/ConstantOrderLowerBoundDiv/Final.lean:68). The copies are wrappers:
every instantiation of Lemma 2.9 in that chain is at an open ball, which is measurable.

No Draft statement is edited, and no Prop is frozen.
-/

namespace MatedCRT

/-- **Proposition 7.1** (`firstPass_7_1`) with Lemma 7.4 in the positive-support form `CrudeUpperBoundSupportStmt` and
Lemma 2.9 in the Borel form `CountingMeasureConvergenceMeasurableStmt`, in place of `CountingMeasureConvergenceStmt`
(`firstPass_7_1_support`, S7x.lean:105). Same other hypotheses and conclusion. -/
theorem firstPass_7_1_support_measurable (𝒮 : SpaceFillingSLEModel) (hscale : MepsScalingInput 𝒮)
    (hcone : ConeHarmonicBallsStmt) (hdeg : DegreeBoundInput 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceMeasurableStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hconv : ConvergenceDivisibleStmt 𝒮) (hgreen : UniformConvergenceGreenKernelStmt 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) : DivSandpileUpperBoundStmt 𝒮 :=
  divSandpileUpperBound_of_meshScaling 𝒮 hscale hcone
    (constantOrderLowerBoundDivLog_final_meas 𝒮 h216 h27 h28 h29 h218 h0 AnnulusHitField.coneWholePlaneWeylComparison h2
      hV hR Field.ConeCircle.circleAverageModConstStep (LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮))
    h27 (firstPass_7_2_corrected 𝒮 h216 h28) hconv hgreen h28 (firstPass_7_3 𝒮)
    (crudeUpperBound_of_support 𝒮 (crudeUpperBoundSupport_of_corrected 𝒮 (discreteLaplacianBoundCorrected 𝒮) hdeg))

end MatedCRT
