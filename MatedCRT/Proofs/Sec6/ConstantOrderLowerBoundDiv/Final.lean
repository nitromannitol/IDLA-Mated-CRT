import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.OfSteps
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Steps.Sec2.ExpectedExitTimeExplicitBound
import MatedCRT.Steps.Sec2.BoundedExitTimeRV
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.Main
import MatedCRT.Proofs.Sec6.IterativeBound.Statement

/-!
# Lemma 6.8, route (b) of E-A10, and the chain 6.7 (b), 6.9 (b), 6.10: final reductions

`constantOrderLowerBoundDiv_of_aeSteps` (`OfSteps.lean`) with its proved inputs discharged:
* Lemma 2.19 (`ExpectedExitTimeExplicitBoundStmt`) from Lemma 2.17 (`boundedExitTimeRV_of_steps`, from Lemma 2.7) and
  Lemma 2.18 (`expectedExitTimeExplicitBound_of_steps`);
* the intersection of adjacent cells (`adjacentCellsMeetAeStep`);
* the almost-sure `σ(h)`-measurability of the good-scale events of line 2505 from the `σ(h)`-measurability of the LQG
  measure `μ_h` (eq:measure-lim, line 470; `goodScaleEventMeasurableAEStep_of_lqgMeasure`).

`constantOrderLowerBoundDiv_of_inputs`: from the cited Lemmas 2.7, 2.8, 2.9, 2.16, 2.18, Lemma 6.4 and
`LQGMeasureFieldMeasurableStep`. `constantOrderLowerBoundDiv_of_fieldInputs`: Lemma 6.4 replaced by its field inputs
(`goodAnnulusPrevalence_of_fieldInputs`).

## Final forms

The `_final` theorems take only cited Draft statements and the named steps (see docs/campaign/COUNTED.md); no External input is
used. The hypotheses, in this order:
* cited (Draft statements of results the paper quotes): Lemma 2.16 `GreenKernelLowerBoundStmt`, Lemma 2.7
  `VolumeGrowthStmt`, Lemma 2.8 `CellSizeEstimateStmt`, Lemma 2.9 `CountingMeasureConvergenceStmt`, Lemma 2.18
  `ExitTimeUpperBoundStmt` (all five for each result here);
* steps of Lemmas 6.4 and 6.5 (`goodAnnulusPrevalence_final`): `WholePlaneLQGExistenceStep`,
  `ConeWholePlaneWeylComparisonStep`, `WholePlaneLQGCoordinateChangeStep`, `WholePlaneUpperVolumeTailStep`,
  `ConeMeanZeroRestrictionStep`; `CircleAverageModConstStep` is proved by `circleAverageModConstStep` (`MatedCRT/Proofs/Field/ConeCircleModConst.lean:367`);
* step of Lemma 6.8 (b) (`MatedCRT/Proofs/Measurability/GoodScale.lean`; see docs/campaign/COUNTED.md):
  `LQGMeasureFieldMeasurableStep` (eq:measure-lim, line 470).

Lemmas 6.7 (b), 6.9 (b) and 6.10 add no hypothesis to those of Lemma 6.8 (b): their remaining inputs (Lemma 2.19,
`AdjacentCellsMeetAeStep`, the Chernoff step and the steps of `iterativeBound`) are proved.
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

/-- **Lemma 6.8, route (b) of E-A10, final form** (lemma:constant-order-lower-bound-div, line 2455). Hypotheses: the
cited Lemmas 2.16, 2.7, 2.8, 2.9, 2.18; the six field steps of Lemmas 6.4 and 6.5 (`goodAnnulusPrevalence_final`);
the step `LQGMeasureFieldMeasurableStep` (eq:measure-lim, line 470). -/
theorem constantOrderLowerBoundDivLog_final (𝒮 : SpaceFillingSLEModel)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h0 : WholePlaneLQGExistenceStep) (h1 : ConeWholePlaneWeylComparisonStep)
    (h2 : WholePlaneLQGCoordinateChangeStep) (hV : WholePlaneUpperVolumeTailStep)
    (hR : ConeMeanZeroRestrictionStep) (hD : CircleAverageModConstStep) (hμ : LQGMeasureFieldMeasurableStep 𝒮) :
    ConstantOrderLowerBoundDivLogStmt 𝒮 :=
  constantOrderLowerBoundDiv_of_inputs 𝒮 h216 h27 h28 h29 h218 (goodAnnulusPrevalence_final h0 h1 h2 hV hR hD) hμ

/-- **Lemma 6.7, route (b) of E-A10, final form** (lemma:constant-order-lower-bound, line 2427, absorption probability
`s₂/(1+|log r|)²`), with the hypotheses of `constantOrderLowerBoundDivLog_final`. Lemma 2.19 is discharged by
Lemmas 2.17 and 2.18, the intersection of adjacent cells by `adjacentCellsMeetAeStep`. -/
theorem constantOrderLowerBoundLog_final (𝒮 : SpaceFillingSLEModel)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h0 : WholePlaneLQGExistenceStep) (h1 : ConeWholePlaneWeylComparisonStep)
    (h2 : WholePlaneLQGCoordinateChangeStep) (hV : WholePlaneUpperVolumeTailStep)
    (hR : ConeMeanZeroRestrictionStep) (hD : CircleAverageModConstStep) (hμ : LQGMeasureFieldMeasurableStep 𝒮) :
    ConstantOrderLowerBoundLogStmt 𝒮 :=
  constantOrderLowerBoundLog 𝒮
    (constantOrderLowerBoundDivLog_final 𝒮 h216 h27 h28 h29 h218 h0 h1 h2 hV hR hD hμ) h27 h28
    (expectedExitTimeExplicitBound_of_steps (boundedExitTimeRV_of_steps h27) h218) (adjacentCellsMeetAeStep 𝒮)

/-- **Lemma 6.9, route (b), final form** (lemma:chance-of-being-absorbed, with `s₃` chosen after `s₀`), with the hypotheses of `constantOrderLowerBoundDivLog_final`, through Lemma 6.7 (b). -/
theorem chanceOfBeingAbsorbedLogLoss_final (𝒮 : SpaceFillingSLEModel)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h0 : WholePlaneLQGExistenceStep) (h1 : ConeWholePlaneWeylComparisonStep)
    (h2 : WholePlaneLQGCoordinateChangeStep) (hV : WholePlaneUpperVolumeTailStep)
    (hR : ConeMeanZeroRestrictionStep) (hD : CircleAverageModConstStep) (hμ : LQGMeasureFieldMeasurableStep 𝒮) :
    ChanceOfBeingAbsorbedLogLossStmt 𝒮 :=
  chanceOfBeingAbsorbedLogLoss_of_div 𝒮
    (constantOrderLowerBoundDivLog_final 𝒮 h216 h27 h28 h29 h218 h0 h1 h2 hV hR hD hμ) h27 h28
    (expectedExitTimeExplicitBound_of_steps (boundedExitTimeRV_of_steps h27) h218) (adjacentCellsMeetAeStep 𝒮)

/-- **Lemma 6.10, final form** (lemma:iterative-bound, line 2696), with the hypotheses of `constantOrderLowerBoundDivLog_final`,
through Lemmas 6.7 (b) and 6.9 (b). -/
theorem iterativeBound_final (𝒮 : SpaceFillingSLEModel)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h0 : WholePlaneLQGExistenceStep) (h1 : ConeWholePlaneWeylComparisonStep)
    (h2 : WholePlaneLQGCoordinateChangeStep) (hV : WholePlaneUpperVolumeTailStep)
    (hR : ConeMeanZeroRestrictionStep) (hD : CircleAverageModConstStep) (hμ : LQGMeasureFieldMeasurableStep 𝒮) :
    IterativeBoundStmt 𝒮 :=
  iterativeBound_of_div 𝒮
    (constantOrderLowerBoundDivLog_final 𝒮 h216 h27 h28 h29 h218 h0 h1 h2 hV hR hD hμ) h27 h28
    (expectedExitTimeExplicitBound_of_steps (boundedExitTimeRV_of_steps h27) h218) (adjacentCellsMeetAeStep 𝒮)

end MatedCRT
