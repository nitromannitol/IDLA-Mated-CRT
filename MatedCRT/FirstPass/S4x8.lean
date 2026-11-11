import MatedCRT.FirstPass.S4x
import MatedCRT.FirstPass.S218
import MatedCRT.FirstPass.S3g
import MatedCRT.FirstPass.Closure.Section3

/-!
# Lemma 4.8, corrected, from the corrected Lemma 3.5 and the BG20 exit-time input

`firstPass_4_8_corrected_of_closedInputs` is the counted form of Lemma 4.8 (`lemma:subsequential-properties`, corrected
form `SubsequentialPropertiesCorrectedStmt`). It has the conclusion of
`firstPass_4_8_corrected_of_inputs` (FirstPass/S4x.lean) and the following binders:

* the exit-time input `ExitTimeUpperBoundStmt 𝒮` is replaced by the exact mass-restricted BG20 statement `h51 : BG20Prop51 𝒮`
  (BG20 Proposition 5.1), through `exitTimeUpperBound_of_bg20Prop51_volumeGrowth h51 h27` (FirstPass/S218.lean:26);
* the discrete Dirichlet input is the corrected Lemma 3.5, `h35c : DiscreteDirichletProblemCorrectedStmt 𝒮` [C13]. The
  printed type `DiscreteDirichletProblemStmt 𝒮` that the chain (corrected 4.6, prepared identification) consumes is
  recovered from `h35c` by the proved bridge `MatedCRT.FirstPass35Bridge.discreteDirichletProblem_of_corrected_of_steps`
  (FirstPass/S3g.lean:164). That bridge takes the cell-size estimate `h28 : CellSizeEstimateStmt 𝒮` as one extra binder; the
  discrete maximum principle is not a binder (it is `maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)`).

`h33` and `h37` remain binders here. `closed_4_8_corrected` discharges all of them from a certified reference model
(the pattern of `closed_3_5`, FirstPass/Closure/Section3.lean).
-/

namespace MatedCRT

open MeasureTheory

/-- **Lemma 4.8, corrected, from the corrected Lemma 3.5 and BG20 Proposition 5.1.** Same conclusion as
`firstPass_4_8_corrected_of_inputs`; the Dirichlet input is the corrected `DiscreteDirichletProblemCorrectedStmt`, bridged to
the printed type by `discreteDirichletProblem_of_corrected_of_steps` (cell-size input `h28`), and the exit-time input is the
mass-restricted `BG20Prop51` through `exitTimeUpperBound_of_bg20Prop51_volumeGrowth`. -/
theorem firstPass_4_8_corrected_of_closedInputs {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮)
    (h27 : VolumeGrowthStmt) (h51 : BG20Prop51 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮) (h37 : ConvergenceNormalizedExitTimeStmt 𝒮) :
    SubsequentialPropertiesCorrectedStmt 𝒮 :=
  firstPass_4_8_corrected_of_inputs hm h27 (exitTimeUpperBound_of_bg20Prop51_volumeGrowth h51 h27) hH h33
    (FirstPass35Bridge.discreteDirichletProblem_of_corrected_of_steps h28 h35c) h37

/-- **Lemma 4.8, corrected, for a certified reference model `hC`.** The inputs are closed by the certified model
(`hC.mepsScaling`, `hC.bg20Prop51`, `hC.frozenDiscreteHolderContinuityCorrected`, `hC.cellSizeEstimate`), by `closed_3_3`
(Lemma 3.3), by `closed_3_5` (corrected Lemma 3.5) and by `closed_3_7` (Lemma 3.7). Remaining inputs: the cited Lemma 2.7
`h27 : VolumeGrowthStmt` and the frozen external `hexc : FrozenBrownianOutwardExcursionAtExit` (as in `closed_3_5`). -/
theorem closed_4_8_corrected {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (h27 : VolumeGrowthStmt) (hexc : FrozenBrownianOutwardExcursionAtExit) :
    SubsequentialPropertiesCorrectedStmt 𝒮 :=
  firstPass_4_8_corrected_of_closedInputs hC.mepsScaling h27 hC.bg20Prop51 hC.frozenDiscreteHolderContinuityCorrected
    hC.cellSizeEstimate (closed_3_3 ν hC h27) (closed_3_5 ν hC h27 hexc) (closed_3_7 ν hC h27 hexc)

end MatedCRT

#print axioms MatedCRT.firstPass_4_8_corrected_of_closedInputs
#print axioms MatedCRT.closed_4_8_corrected
