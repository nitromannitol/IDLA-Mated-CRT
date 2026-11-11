import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.SelectionStep
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Equicontinuity
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Steps.Sec2.BoundedExitTimeRV

/-!
# Lemma 3.1 (corrected) from its inputs

`discretePotentialTightness_of_inputs` proves `DiscretePotentialTightnessCorrectedStmt`. This is Lemma 3.1 with the
changes N1, `D` open and N3 listed in MatedCRT/Steps/Sec3/DiscretePotentialTightness.lean. Its inputs are:

* `MepsScalingInput` (eq:meps-scaling, BG20 (1.8));
* `BoundedExitTimeRVStmt` and `ExitTimeUpperBoundStmt` (Lemmas 2.17 and 2.18);
* `DiscreteHolderContinuityCorrectedStep` (Lemma 3.2 in the corrected form of review-L32);
* `AdjacentCellsMeetAeStep` (the cells of adjacent vertices intersect; DMS14 Lemma 8.8).

`discretePotentialTightnessCorrected_of_boundedExitTime` discharges `AdjacentCellsMeetAeStep` with
`adjacentCellsMeetAeStep` (MatedCRT/Proofs/MatingOfTrees/AdjacentCells.lean). Its remaining hypotheses are:

* the External input `MepsScalingInput`;
* the Draft statements of Lemmas 2.17 and 2.18;
* the corrected Lemma 3.2.

The final form `discretePotentialTightnessCorrected_of_inputs`
(MatedCRT/Proofs/Sec3/DiscretePotentialTightness/Final.lean) replaces Lemma 2.17 by Lemma 2.7
(`boundedExitTimeRV_of_steps`).
-/

namespace MatedCRT

/-- **Lemma 3.1 (corrected)** from its inputs. -/
theorem discretePotentialTightness_of_inputs {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮) :
    DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  discretePotentialTightness_of_equicontinuity hm (tightnessEquicontinuityStep_of_steps h217 h218 hH hadj)

/-- **Lemma 3.1 (corrected)** from Draft and External inputs and the corrected Lemma 3.2 only:
* `MepsScalingInput` (External; eq:meps-scaling, BG20 (1.8));
* `BoundedExitTimeRVStmt` and `ExitTimeUpperBoundStmt` (Draft; Lemmas 2.17 and 2.18);
* `DiscreteHolderContinuityCorrectedStep` (Lemma 3.2, corrected; GMS19 Theorem 3.9).

The local finiteness of the mated-CRT map comes from `adjacentCellsMeetAeStep`. -/
theorem discretePotentialTightnessCorrected_of_boundedExitTime {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h217 : BoundedExitTimeRVStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮) : DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  discretePotentialTightness_of_inputs hm h217 h218 hH (adjacentCellsMeetAeStep 𝒮)

end MatedCRT
