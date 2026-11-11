import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Final
import MatedCRT.FirstPass.S7y.OfSteps

/-!
# Measurable-binder copies of `constantOrderLowerBoundDiv_of_inputs` and `constantOrderLowerBoundDivLog_final`
(fp-S7y-h29-measurable)

Copies of MatedCRT/Proofs/Sec6/ConstantOrderLowerBoundDiv/Final.lean:43 and :68 with the Lemma 2.9 hypothesis
`CountingMeasureConvergenceMeasurableStmt` (S7y/Stmt.lean) and the `_meas` almost-sure assembly (S7y/OfSteps.lean). Proofs
are the originals', with the calls renamed. Original file unchanged.
-/

namespace MatedCRT

/-- **Lemma 6.8, route (b) of E-A10** (lemma:constant-order-lower-bound-div, line 2455), from the cited Lemmas 2.7,
2.8, 2.9, 2.16, 2.18, Lemma 6.4 and the `σ(h)`-measurability of the LQG measure (eq:measure-lim, line 470). -/
theorem constantOrderLowerBoundDiv_of_inputs_meas (𝒮 : SpaceFillingSLEModel)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceMeasurableStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h64 : GoodAnnulusPrevalenceStmt) (hμ : LQGMeasureFieldMeasurableStep 𝒮) :
    ConstantOrderLowerBoundDivLogStmt 𝒮 :=
  constantOrderLowerBoundDiv_of_aeSteps_meas 𝒮 h216 h27 h28 h29 h64 h218
    (expectedExitTimeExplicitBound_of_steps (boundedExitTimeRV_of_steps h27) h218)
    (goodScaleEventMeasurableAEStep_of_lqgMeasure 𝒮 hμ) (adjacentCellsMeetAeStep 𝒮)

/-- **Lemma 6.8, route (b) of E-A10, final form** (lemma:constant-order-lower-bound-div, line 2455). Hypotheses: the
cited Lemmas 2.16, 2.7, 2.8, 2.9, 2.18; the six open field steps of Lemmas 6.4 and 6.5 (`goodAnnulusPrevalence_final`);
the open step `LQGMeasureFieldMeasurableStep` (eq:measure-lim, line 470). -/
theorem constantOrderLowerBoundDivLog_final_meas (𝒮 : SpaceFillingSLEModel)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceMeasurableStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h0 : WholePlaneLQGExistenceStep) (h1 : ConeWholePlaneWeylComparisonStep)
    (h2 : WholePlaneLQGCoordinateChangeStep) (hV : WholePlaneUpperVolumeTailStep)
    (hR : ConeMeanZeroRestrictionStep) (hD : CircleAverageModConstStep) (hμ : LQGMeasureFieldMeasurableStep 𝒮) :
    ConstantOrderLowerBoundDivLogStmt 𝒮 :=
  constantOrderLowerBoundDiv_of_inputs_meas 𝒮 h216 h27 h28 h29 h218 (goodAnnulusPrevalence_final h0 h1 h2 hV hR hD) hμ


end MatedCRT
