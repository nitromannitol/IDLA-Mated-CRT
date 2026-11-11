import MatedCRT.FirstPass.S2b
import MatedCRT.Proofs.IDLA.JointDiscreteLowerBound
import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Draft.Section5
import MatedCRT.Steps.Sec5.IDLALowerBound
import MatedCRT.FirstPass.S5d.StoppedReduction
import MatedCRT.FirstPass.S5d.ClusterInner
import MatedCRT.FirstPass.S5d.ClusterFromOdometer
import MatedCRT.FirstPass.S5d.StoppedPathwise
import MatedCRT.FirstPass.S5d.StoppedExitInput
import MatedCRT.FirstPass.S5d.UnstoppedFromStopped
import MatedCRT.FirstPass.S2j
import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.S1S2S8SA
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Measurability.LQGMeasureField
import MatedCRT.FirstPass.S5h
import MatedCRT.FirstPass.S5e.SecondGreenStep
import MatedCRT.FirstPass.S5d.FloorCellStep

/-!
# Proposition 5.1 (`firstPass_5_1`)

`IDLALowerBoundStmt` (Draft/Section5.lean:27) is assembled from:
* the relaxed Lemma 5.2 (no origin or connectivity condition on the target; proved in the repository by
  `generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize` from Lemma 2.7 and Lemma 2.8);
* Lemma 5.3 (`MeanValueInequalityStmt`) and Lemma 5.4 (`LLowerBoundStmt`), Draft statements used as hypotheses;
* NEW steps that are not yet proved (referee):
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

/-- **Proposition 5.1 from its open steps.** The unstopped conjunct is the stopped conjunct by monotonicity in the stopping domain ([C21];
`S5d/UnstoppedFromStopped.lean`), so neither Proposition 4.2 nor the strict-positivity input is used; the stopped conjunct is
`iDLALowerBoundStopped_of_greenSteps` (killing set `V^ε(Λ_t) ∩ S^ε`, targets `V^ε(B⁻_δ(Λ_t)) ∪ {0}`), from the two
open Green steps: the first one is `stoppedFirstGreenStep_of_steps` from `stoppedFirstGreenInputsStep_of_floorCeiling` (open surplus floor `hfl` and open surplus maximum `hmax`, whose ceiling is derived by `stoppedFloorCeiling_of_floor_max`; exit input proved in `S5d/StoppedExitInput.lean`) and the standing steps
`hcell`, `hlap` ([C21]); the second is `hG2`; the cone-family inputs are `hfam`, `h24c`. -/
theorem firstPass_5_1_of_steps (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (hfam : ConeFamilyAEMeasurableStep)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (hfl : StoppedFloorCellStep 𝒮) (hmax : StoppedMaxOutsideStep 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt) (hμ : LQGMeasureFieldMeasurableStep 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮) (hlap : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (hG2 : StoppedSecondGreenStep 𝒮) :
    IDLALowerBoundStmt 𝒮 :=
  S5d.iDLALowerBound_of_stoppedStep 𝒮
    (iDLALowerBoundStopped_of_greenSteps 𝒮 (generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize 𝒮 h27 h28)
      hfam h24c
      (stoppedFirstGreenStep_of_steps 𝒮 (stoppedFirstGreenInputsStep_of_floorCeiling 𝒮 (stoppedFloorStep_of_cellFloor hfl) hmax h218 h217 hμ hcell hlap)
        hcell hlap) hG2)

/-- **Proposition 5.1 with the proved inputs plugged in.** Compared with
`firstPass_5_1_of_steps`: `hμ` is `LQGMeasureField.lqgMeasureFieldMeasurableStep` (Proofs/Measurability/LQGMeasureField.lean:75),
`hcell` is `adjacentCellsMeetAeStep` (Proofs/MatingOfTrees/AdjacentCells.lean:17), `hlap` is `firstPass_4_4_corrected`
(FirstPass/S3S4.lean:42), `h217` is `firstPass_2_17 h27` (FirstPass/S1S2S8SA.lean:53); the cone-family input `hfam` is replaced by
the hypotheses of `coneFamilyAEMeasurable_proved` (FirstPass/S2j.lean:32). The remaining hypotheses are the Draft statements
`h27`, `h28`, `h24c`, `h218`, the cone inputs `hcan`, `hcl`, `hE1`, `hE2`, `hscale`, `h22`; the single floor input `hfl`
(`StoppedFloorCellStep`, OPEN); the ceiling inputs of `stoppedMaxOutside_proved` (FirstPass/S5h.lean:139: `hconv`, `hgreen`, `hM`,
`hG`, `hpole` (`StoppedPoleCellStep`, OPEN), `hmeas`); the second Green inputs of `stoppedSecondGreenStep_of_inputs`
(S5e/SecondGreenStep.lean:142: `hG15`, `hG16`, `hmass` (`StoppedMassLowerStep`, OPEN)). -/
theorem firstPass_5_1_of_open_steps (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep) (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep) (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (hfl : StoppedFloorCellStep 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hconv : ConvergenceDivisibleStmt 𝒮) (hgreen : UniformConvergenceGreenKernelStmt 𝒮) (hM : MepsScalingInput 𝒮)
    (hG : MatedCRT.FrozenGreenDiscPole) (hpole : StoppedPoleCellStep 𝒮) (hmeas : ConeOriginNullMeasurableStep 𝒮)
    (hG15 : GreenFunctionCrudeBoundStmt 𝒮) (hG16 : GreenKernelLowerBoundStmt 𝒮) (hmass : S5e.StoppedMassLowerStep 𝒮) :
    IDLALowerBoundStmt 𝒮 :=
  firstPass_5_1_of_steps 𝒮 h27 h28 (coneFamilyAEMeasurable_proved hcan hcl h27 hE1 hE2 hscale h22) h24c hfl
    (stoppedMaxOutside_proved 𝒮 hconv hgreen hM hG hpole hmeas) h218
    (firstPass_2_17 h27) (LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮) (adjacentCellsMeetAeStep 𝒮)
    (firstPass_4_4_corrected 𝒮)
    (S5e.stoppedSecondGreenStep_of_inputs 𝒮 (adjacentCellsMeetAeStep 𝒮) (firstPass_4_4_corrected 𝒮) hG15 hG16 h28
      (stoppedFloorHalfStep_of_cellFloor hfl) hmass)

end MatedCRT
