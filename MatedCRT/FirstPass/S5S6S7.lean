import MatedCRT.Draft.Section5
import MatedCRT.Draft.Section6
import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Proofs.Sec5.LLowerBound.OfInputs
import MatedCRT.Proofs.Sec6.GoodAnnulusPrevalence.Main
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Final
import MatedCRT.Proofs.Field.ConeCircleModConst
import MatedCRT.Proofs.Measurability.LQGMeasureField
import MatedCRT.FirstPass.Frozen.S5S6S7

/-!
# FIRST PASS: Section 5 (Proposition 5.1, Lemmas 5.2-5.4), Section 6 and Section 7 of arXiv:2211.04891 (corrected draft)

Each theorem `firstPass_<sec>_<num>` has as conclusion the Draft statement of the numbered result (or its corrected
form) and, as hypotheses, only Draft statements of other numbered results used by the printed proof and EXTERNAL
inputs (`FP...` frozen Props in `MatedCRT/FirstPass/Frozen/S5S6S7.lean`, and Draft statements of cited results).
-/

namespace MatedCRT

/-- **Lemma 5.2** (`firstPass_5_2`). Uses the cited Lemmas 2.7 (`VolumeGrowthStmt`) and 2.8
(`CellSizeEstimateStmt`). -/
theorem firstPass_5_2 (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) :
    GeneralIDLALowerBoundStmt 𝒮 :=
  generalIDLALowerBound_of_volumeGrowth_cellSize 𝒮 h27 h28

/-- **Lemma 5.4** (`firstPass_5_4`). Uses the cited Lemmas 2.15, 2.16 and 2.9; the adjacency of cells is
proved (`adjacentCellsMeetAeStep`). -/
theorem firstPass_5_4 (𝒮 : SpaceFillingSLEModel) (h215 : GreenFunctionCrudeBoundStmt 𝒮)
    (h216 : GreenKernelLowerBoundStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) : LLowerBoundStmt 𝒮 :=
  lLowerBound_of_inputs 𝒮 h215 h216 h29

/-- **Lemma 6.5** (`firstPass_6_5`, lemma:annulus-hit). Uses the four EXTERNAL field inputs `FP...`
(WholePlaneLQGExistence, ConeWholePlaneWeylComparison, WholePlaneLQGCoordinateChange, WholePlaneUpperVolumeTail);
the tightness step is proved inside `annulusHit_final`. -/
theorem firstPass_6_5 (h0 : FPWholePlaneLQGExistence) (h1 : FPConeWholePlaneWeylComparison)
    (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail) : AnnulusHitStmt :=
  annulusHit_final h0 h1 h2 hV

/-- **Lemma 6.4** (`firstPass_6_4`, lemma:good-prevalance). Uses the four inputs of Lemma 6.5, the EXTERNAL
`FPConeMeanZeroRestriction`, and the proved `circleAverageModConstStep`. -/
theorem firstPass_6_4 (h0 : FPWholePlaneLQGExistence) (h1 : FPConeWholePlaneWeylComparison)
    (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) : GoodAnnulusPrevalenceStmt :=
  goodAnnulusPrevalence_final h0 h1 h2 hV hR Field.ConeCircle.circleAverageModConstStep

/-- **Lemma 6.10** (`firstPass_6_10`, lemma:iterative-bound). Uses the cited Lemmas 2.16, 2.7, 2.8, 2.9, 2.18, the
EXTERNAL field inputs of Lemma 6.4, and the proved `circleAverageModConstStep` and `lqgMeasureFieldMeasurableStep`.
The printed proof uses the log form of Lemma 6.8 (route (b), `ConstantOrderLowerBoundDivLogStmt`), which is proved
inside `iterativeBound_final` from the same inputs. -/
theorem firstPass_6_10 (𝒮 : SpaceFillingSLEModel) (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h1 : FPConeWholePlaneWeylComparison)
    (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) : IterativeBoundStmt 𝒮 :=
  iterativeBound_final 𝒮 h216 h27 h28 h29 h218 h0 h1 h2 hV hR Field.ConeCircle.circleAverageModConstStep
    (LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮)

end MatedCRT
