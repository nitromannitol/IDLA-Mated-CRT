import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.OfSteps
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Steps.Sec2.ExpectedExitTimeExplicitBound
import MatedCRT.Steps.Sec2.BoundedExitTimeRV
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.Main

/-!
# Lemma 6.8, route (b) of E-A10: final reductions

`constantOrderLowerBoundDiv_of_aeSteps` (`OfSteps.lean`) with its proved inputs discharged:
* Lemma 2.19 (`ExpectedExitTimeExplicitBoundStmt`) from Lemma 2.17 (`boundedExitTimeRV_of_steps`, from Lemma 2.7) and
  Lemma 2.18 (`expectedExitTimeExplicitBound_of_steps`);
* the intersection of adjacent cells (`adjacentCellsMeetAeStep`);
* the almost-sure `σ(h)`-measurability of the good-scale events of line 2505 from the `σ(h)`-measurability of the LQG
  measure `μ_h` (eq:measure-lim, line 470; `goodScaleEventMeasurableAEStep_of_lqgMeasure`).

`constantOrderLowerBoundDiv_of_inputs`: from the cited Lemmas 2.7, 2.8, 2.9, 2.16, 2.18, Lemma 6.4 and
`LQGMeasureFieldMeasurableStep`. `constantOrderLowerBoundDiv_of_fieldInputs`: Lemma 6.4 replaced by its field inputs
(`goodAnnulusPrevalence_of_fieldInputs`).
-/

namespace MatedCRT

/-- **Lemma 6.8, route (b) of E-A10** (lemma:constant-order-lower-bound-div, line 2455), from the cited Lemmas 2.7,
2.8, 2.9, 2.16, 2.18, Lemma 6.4 and the `σ(h)`-measurability of the LQG measure (eq:measure-lim, line 470). -/
theorem constantOrderLowerBoundDiv_of_inputs (𝒮 : SpaceFillingSLEModel)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h64 : GoodAnnulusPrevalenceStmt) (hμ : LQGMeasureFieldMeasurableStep 𝒮) :
    ConstantOrderLowerBoundDivLogStmt 𝒮 :=
  constantOrderLowerBoundDiv_of_aeSteps 𝒮 h216 h27 h28 h29 h64 h218
    (expectedExitTimeExplicitBound_of_steps (boundedExitTimeRV_of_steps h27) h218)
    (goodScaleEventMeasurableAEStep_of_lqgMeasure 𝒮 hμ) (adjacentCellsMeetAeStep 𝒮)

/-- **Lemma 6.8, route (b) of E-A10** (lemma:constant-order-lower-bound-div, line 2455), from the cited Lemmas 2.7,
2.8, 2.9, 2.16, 2.18, the `σ(h)`-measurability of the LQG measure and the field inputs of Lemmas 6.4 and 6.5
(`goodAnnulusPrevalence_of_fieldInputs`). -/
theorem constantOrderLowerBoundDiv_of_fieldInputs (𝒮 : SpaceFillingSLEModel)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hμ : LQGMeasureFieldMeasurableStep 𝒮) (h0 : WholePlaneLQGExistenceStep)
    (h1 : ConeWholePlaneWeylComparisonStep) (h2 : WholePlaneLQGCoordinateChangeStep)
    (hV : WholePlaneUpperVolumeTailStep) (hR : ConeMeanZeroRestrictionStep) (hD : CircleAverageModConstStep) :
    ConstantOrderLowerBoundDivLogStmt 𝒮 :=
  constantOrderLowerBoundDiv_of_inputs 𝒮 h216 h27 h28 h29 h218
    (goodAnnulusPrevalence_of_fieldInputs h0 h1 h2 hV hR hD) hμ

end MatedCRT
