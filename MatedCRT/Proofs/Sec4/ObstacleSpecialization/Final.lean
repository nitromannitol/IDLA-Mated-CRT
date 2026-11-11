import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Statements
import MatedCRT.Proofs.Sec4.Equibounded
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Steps.Sec2.BoundedExitTimeRV

/-!
# Section 4: Lemmas 4.3, 4.4 (corrected), 4.5 (corrected) and 4.7, final forms

* `discreteBasicProperties` (**Lemma 4.3**), `discreteLaplacianBoundCorrected` (**Lemma 4.4**, corrected) and
  `discreteConservationOfMassCorrected` (**Lemma 4.5**, corrected) have no hypotheses. The route of
  MatedCRT/Proofs/Sec4/ObstacleSpecialization/Statements.lean applies Appendix A to the connected component of the
  origin in `V^ε(B_ρ) \ V^ε(∂B_ρ)` and needs only `AdjacentCellsMeetAeStep`, which `adjacentCellsMeetAeStep`
  (MatedCRT/Proofs/MatingOfTrees/AdjacentCells.lean) proves. Neither `BallInteriorConnectedStep` nor
  `MatedObstacleSettingStep` is used.
* `equibounded_of_inputs` (**Lemma 4.7**) has only cited hypotheses:
  - `VolumeGrowthStmt` (Draft, Lemma 2.7; BG20 Lemma A.1), which gives Lemma 2.17 (`BoundedExitTimeRVStmt`) through
    `boundedExitTimeRV_of_steps`;
  - `ExitTimeUpperBoundStmt` (Draft, Lemma 2.18; BG20 Proposition 5.1);
  - `MepsScalingInput` (External, MatedCRT/External/SLE.lean; eq:meps-scaling, BG20 (1.8)).

  Lemma 4.3 is discharged by `discreteBasicProperties`. `equibounded_of_boundedExitTime` keeps Lemma 2.17 as a
  hypothesis.
-/

namespace MatedCRT

/-- **Lemma 4.3** (lemma:discrete-basic-properties, line 1690 of paper/idla_mated_crt-corrected.tex). -/
theorem discreteBasicProperties (𝒮 : SpaceFillingSLEModel) : DiscreteBasicPropertiesStmt 𝒮 :=
  discreteBasicProperties_of_escape (adjacentCellsMeetAeStep 𝒮)

/-- **Lemma 4.4** (lemma:discrete-laplacian-bound, line 1708), corrected (the origin claim needs
`0 ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)`). -/
theorem discreteLaplacianBoundCorrected (𝒮 : SpaceFillingSLEModel) : DiscreteLaplacianBoundCorrectedStmt 𝒮 :=
  discreteLaplacianBoundCorrected_of_escape (adjacentCellsMeetAeStep 𝒮)

/-- **Lemma 4.5** (lemma:discrete-conservation-of-mass, line 1716), corrected (the mass identity needs
`0 ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)`). -/
theorem discreteConservationOfMassCorrected (𝒮 : SpaceFillingSLEModel) :
    DiscreteConservationOfMassCorrectedStmt 𝒮 :=
  discreteConservationOfMassCorrected_of_escape (adjacentCellsMeetAeStep 𝒮)

/-- **Lemma 4.7** (lemma:equibounded, line 1740) from Lemma 2.17 (`BoundedExitTimeRVStmt`), Lemma 2.18
(`ExitTimeUpperBoundStmt`) and eq:meps-scaling (`MepsScalingInput`), with Lemma 4.3 discharged. -/
theorem equibounded_of_boundedExitTime {𝒮 : SpaceFillingSLEModel} (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮) : EquiboundedStmt 𝒮 :=
  equibounded_of_steps (discreteBasicProperties 𝒮) h217 h218 hm

/-- **Lemma 4.7** (lemma:equibounded, line 1740) from the cited Lemma 2.7 (`VolumeGrowthStmt`, BG20 Lemma A.1),
Lemma 2.18 (`ExitTimeUpperBoundStmt`, BG20 Proposition 5.1) and eq:meps-scaling (`MepsScalingInput`, BG20 (1.8)). -/
theorem equibounded_of_inputs {𝒮 : SpaceFillingSLEModel} (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮) : EquiboundedStmt 𝒮 :=
  equibounded_of_boundedExitTime (boundedExitTimeRV_of_steps h27) h218 hm

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.discreteBasicProperties
#print axioms MatedCRT.discreteLaplacianBoundCorrected
#print axioms MatedCRT.discreteConservationOfMassCorrected
#print axioms MatedCRT.equibounded_of_inputs

section Audit

open MatedCRT

variable (𝒮 : SpaceFillingSLEModel)

/-- **Lemma 4.3**. -/
example : DiscreteBasicPropertiesStmt 𝒮 := discreteBasicProperties 𝒮

/-- **Lemma 4.4**, corrected. -/
example : DiscreteLaplacianBoundCorrectedStmt 𝒮 := discreteLaplacianBoundCorrected 𝒮

/-- **Lemma 4.5**, corrected. -/
example : DiscreteConservationOfMassCorrectedStmt 𝒮 := discreteConservationOfMassCorrected 𝒮

/-- **Lemma 4.7** from the cited Lemmas 2.7 and 2.18 and eq:meps-scaling. -/
example (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮) (hm : MepsScalingInput 𝒮) :
    EquiboundedStmt 𝒮 :=
  equibounded_of_inputs h27 h218 hm

end Audit
