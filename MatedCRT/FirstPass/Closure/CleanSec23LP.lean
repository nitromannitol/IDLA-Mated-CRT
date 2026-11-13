import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.FirstPass.LPBridge.BrownianOutwardExcursion

/-!
# Lemmas 2.13, 3.1, 3.5, 3.6 and 3.7 with the closure and LP-bridge binders discharged

Each theorem below has the conclusion of the counted form of its row in `docs/campaign/COUNTED.md`, with the
binders listed here discharged. A binder is discharged only by a concluder whose type is the binder's type, or by a
committed bridge:

* `hcell : FrozenAdjacentCellsMeetAe 𝒮` (Lemma 2.13) is `adjacentCellsMeetAeStep 𝒮`
  (`MatedCRT/Proofs/MatingOfTrees/AdjacentCells.lean:17`), whose type `AdjacentCellsMeetAeStep 𝒮` has the same body.
* `hexc : FrozenBrownianOutwardExcursionAtExit` (Lemmas 3.5, 3.6, 3.7) is
  `frozenBrownianOutwardExcursionAtExit_holds` (`MatedCRT/FirstPass/LPBridge/BrownianOutwardExcursion.lean:113`),
  which has no hypotheses.
* `h27 : VolumeGrowthStmt` and `h218 : ExitTimeUpperBoundStmt 𝒮` (Lemma 3.1) are supplied by the committed bridges
  `volumeGrowthStmt_of_berestyckiGwynne` and the field `CertifiedReferenceModel.exitTimeUpperBound`, as in
  `MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:92`.

The binders `hBG : FrozenBerestyckiGwynneConeBallMass` and `h32 : FrozenDiscreteHolderContinuityCorrected 𝒮` have no
concluder and are kept.
-/

namespace MatedCRT
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- Lemma 2.13 (maximum principle), closed with the adjacency of cells supplied by `adjacentCellsMeetAeStep`
(`FrozenAdjacentCellsMeetAe 𝒮` discharged, no binder left). -/
theorem closed_2_13_lp {𝒮 : SpaceFillingSLEModel} : MaximumPrincipleStmt 𝒮 :=
  closed_2_13 (adjacentCellsMeetAeStep 𝒮)

/-- Lemma 3.1 (discrete potential tightness, samplewise form), with `h27` and `h218` discharged as in
`firstPass_3_1_ownBinders`. The conclusion is `DiscretePotentialTightnessPointwiseStmt 𝒮`, the conclusion of
`firstPass_3_1_faithful`. -/
theorem closed_3_1_lp (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass) (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) :
    MatedCRT.S3c.DiscretePotentialTightnessPointwiseStmt 𝒮 :=
  firstPass_3_1_ownBinders 𝒮 hm ν hC hBG h32

/-- Lemma 3.5 (discrete Dirichlet problem, corrected), with `h27` supplied as in `closed_3_5_ownBinders` and
`hexc` discharged by `frozenBrownianOutwardExcursionAtExit_holds`. -/
theorem closed_3_5_lp (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass) :
    DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  closed_3_5_ownBinders 𝒮 ν hC hBG frozenBrownianOutwardExcursionAtExit_holds

open MatedCRT.FirstPass36 in

/-- Lemma 3.7 (convergence of the normalized exit time, corrected), with `hexc` discharged by
`frozenBrownianOutwardExcursionAtExit_holds` and the other binders as in `firstPass_3_7_ownBinders`. -/
theorem closed_3_7_lp (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hm : MepsScalingInput 𝒮) (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 :=
  firstPass_3_7_ownBinders 𝒮 ν hC hBG hm h32 frozenBrownianOutwardExcursionAtExit_holds

end MatedCRT
