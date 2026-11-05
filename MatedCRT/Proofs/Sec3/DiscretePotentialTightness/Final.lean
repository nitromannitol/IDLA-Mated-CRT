import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Main

/-!
# Lemma 3.1 (corrected): final form

`discretePotentialTightnessCorrected_of_inputs` proves `DiscretePotentialTightnessCorrectedStmt`
(MatedCRT/Steps/Sec3/DiscretePotentialTightness.lean; Lemma 3.1 with the changes N1, `D` open (E-c1-4) and N3).
Its hypotheses are:

* `MepsScalingInput` (External, MatedCRT/External/SLE.lean; eq:meps-scaling, BG20 (1.8)), cited;
* `VolumeGrowthStmt` (Draft, Lemma 2.7; BG20 Lemma A.1), cited. It gives Lemma 2.17 (`BoundedExitTimeRVStmt`)
  through `boundedExitTimeRV_of_steps`;
* `ExitTimeUpperBoundStmt` (Draft, Lemma 2.18; BG20 Proposition 5.1), cited;
* `DiscreteHolderContinuityCorrectedStep` (Lemma 3.2, corrected [C6]; GMS19 Theorem 3.9),
  implied by `DiscreteHolderContinuityStmt` via `discreteHolderContinuityCorrected_of_draft`.

The cells of adjacent vertices of the mated-CRT map intersect by `adjacentCellsMeetAeStep`
(MatedCRT/Proofs/MatingOfTrees/AdjacentCells.lean), so no step hypothesis remains.
-/

namespace MatedCRT

/-- **Lemma 3.1 (corrected)** (lemma:discrete-potential-tightness, line 976). The hypotheses are the cited eq:meps-scaling
(`MepsScalingInput`), Lemma 2.7 (`VolumeGrowthStmt`) and Lemma 2.18 (`ExitTimeUpperBoundStmt`), and the corrected
Lemma 3.2 (`DiscreteHolderContinuityCorrectedStep`). -/
theorem discretePotentialTightnessCorrected_of_inputs {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮)
    (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮) : DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  discretePotentialTightnessCorrected_of_boundedExitTime hm (boundedExitTimeRV_of_steps h27) h218 hH

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.discretePotentialTightnessCorrected_of_inputs

section Audit

open MatedCRT

variable (𝒮 : SpaceFillingSLEModel)

/-- **Lemma 3.1 (corrected)** from the cited eq:meps-scaling, Lemmas 2.7 and 2.18 and the corrected Lemma 3.2. -/
example (hm : MepsScalingInput 𝒮) (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : DiscreteHolderContinuityCorrectedStep 𝒮) : DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  discretePotentialTightnessCorrected_of_inputs hm h27 h218 hH

end Audit
