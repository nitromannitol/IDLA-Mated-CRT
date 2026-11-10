import MatedCRT.Proofs.IDLA.JointDiscreteLowerBound
import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Draft.Section5
import MatedCRT.Steps.Sec5.IDLALowerBound
import MatedCRT.FirstPass.S5d.StoppedReduction
import MatedCRT.FirstPass.S5d.ClusterInner
import MatedCRT.FirstPass.S5d.ClusterFromOdometer
import MatedCRT.FirstPass.S5d.StoppedPathwise
import MatedCRT.FirstPass.S5d.StoppedExitInput

/-!
# Proposition 5.1 (`firstPass_5_1`, task fp-S5d-5-1-stopped-repair)

`IDLALowerBoundStmt` (Draft/Section5.lean:27) is assembled from:
* the relaxed Lemma 5.2 (no origin or connectivity condition on the target; proved in the repository by
  `generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize` from Lemma 2.7 and Lemma 2.8);
* Lemma 5.3 (`MeanValueInequalityStmt`) and Lemma 5.4 (`LLowerBoundStmt`), Draft statements used as hypotheses;
* NEW steps that are not yet proved (referee notes/fp-gaps/CHATGPT-5-1-gaps-referee.md):
  - `StrictStoppedOdometerPositivityStep` (referee §3.2-3.3, §5.2: the stopped odometer is strictly positive on `B⁻_σ(Λ_t)`
    w.h.p. on `{t < T}`). It gives `StrictClusterCompactContainmentStep` (G1c, referee §3 eq. (3.1); `S5d/ClusterFromOdometer.lean`),
    which gives `DiscreteClusterInnerBoundStep` with Lemma 2.8 (`S5d/ClusterInner.lean`);
  - the stopped clause needs `StoppedSecondGreenStep` (open) and the first Green inequality, which is now reduced to the
    single open input `StoppedFirstGreenInputsStep` (floor, ceiling, exit; `S5d/StoppedFirstGreenInputs.lean`, [C21]). The
    deterministic package of that reduction is discharged in `S5d/StoppedPathwise.lean`
    (`stoppedFirstGreenStep_of_steps`), and `IDLALowerBoundStoppedStep` follows from the two Green steps
    (`MatedCRT/FirstPass/S5d/StoppedReduction.lean`).

Hence `firstPass_5_1_of_steps` is a conditional reduction, not a `PROVED-FP` theorem.
-/

namespace MatedCRT

/-- **Proposition 5.1 from its open steps.** The unstopped conjunct uses only `hP` and `h28` (through the compact containment
`strictClusterCompactContainmentStep_of_odometerPositivity`); the stopped conjunct is
`iDLALowerBoundStopped_of_greenSteps` (killing set `V^ε(Λ_t) ∩ S^ε`, targets `V^ε(B⁻_δ(Λ_t)) ∪ {0}`), from the two
open Green steps: the first one is `stoppedFirstGreenStep_of_steps` from `stoppedFirstGreenInputsStep_of_floorCeiling` (open floor and ceiling input `hfc`, exit input proved in `S5d/StoppedExitInput.lean`) and the standing steps
`hcell`, `hlap` ([C21]); the second is `hG2`; the cone-family inputs are `hfam`, `h24`. -/
theorem firstPass_5_1_of_steps (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h53 : MeanValueInequalityStmt 𝒮) (h54 : LLowerBoundStmt 𝒮)
    (hP : StrictStoppedOdometerPositivityStep 𝒮) (hfam : ConeFamilyAEMeasurableStep)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (hfc : StoppedFloorCeilingStep 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt) (hμ : LQGMeasureFieldMeasurableStep 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮) (hlap : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (hG2 : StoppedSecondGreenStep 𝒮) :
    IDLALowerBoundStmt 𝒮 :=
  iDLALowerBound_of_steps 𝒮 (generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize 𝒮 h27 h28) h53 h54 h28
    (discreteClusterInnerBound_of_compactContainment 𝒮 h28
      (strictClusterCompactContainmentStep_of_odometerPositivity 𝒮 h28 hP))
    (iDLALowerBoundStopped_of_greenSteps 𝒮 (generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize 𝒮 h27 h28)
      hfam h24
      (stoppedFirstGreenStep_of_steps 𝒮 (stoppedFirstGreenInputsStep_of_floorCeiling 𝒮 hfc h218 h217 hμ hcell hlap)
        hcell hlap) hG2)

end MatedCRT
