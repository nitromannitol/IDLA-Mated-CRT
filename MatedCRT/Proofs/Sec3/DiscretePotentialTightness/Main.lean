import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.SelectionStep
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Equicontinuity

/-!
# Lemma 3.1 (corrected) from its inputs

`discretePotentialTightness_of_inputs` proves `DiscretePotentialTightnessCorrectedStmt` (Lemma 3.1 with the changes
N1, `D` open and N3 listed in MatedCRT/Steps/Sec3/DiscretePotentialTightness.lean) from:

* `MepsScalingInput` (eq:meps-scaling, BG20 (1.8));
* `BoundedExitTimeRVStmt` and `ExitTimeUpperBoundStmt` (Lemmas 2.17 and 2.18);
* `DiscreteHolderContinuityCorrectedStep` (Lemma 3.2 in the corrected form of review-L32);
* `AdjacentCellsMeetAeStep` (the cells of adjacent vertices intersect; DMS14 Lemma 8.8).
-/

namespace MatedCRT

/-- **Lemma 3.1 (corrected)** from its inputs. -/
theorem discretePotentialTightness_of_inputs {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮) :
    DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  discretePotentialTightness_of_equicontinuity hm (tightnessEquicontinuityStep_of_steps h217 h218 hH hadj)

end MatedCRT
