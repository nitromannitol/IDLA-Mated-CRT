import MatedCRT.Proofs.Sec5.IDLALowerBound.Stopped
import MatedCRT.Proofs.Sec5.MeanValueInequality.SurplusSteps
import MatedCRT.Proofs.Sec5.LLowerBound.OfInputs
import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Steps.Sec2.MaximumPrinciple
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.Final

/-!
# Proposition 5.1: final form

`iDLALowerBound_final` proves `IDLALowerBoundStmt` from
* cited results: Lemmas 2.7, 2.8, 2.9, 2.15, 2.16, 2.18;
* the Draft statements of the earlier results it uses, each reduced elsewhere: Theorem 4.1 (`ConvergenceDivisibleStmt`),
  Theorem 2.3, Lemma 3.3, Lemma 2.17, the corrected Lemma 4.4;
* the open steps: `LQGMeasureFieldMeasurableStep`, `MeanValueSurplusLowerStep` (Lemma 5.3; E-c2-5),
  `ObstacleClusterInnerApproximationStep` (Proposition 4.2; E-x3-1), and the two steps of the stopped part,
  `StoppedMeanValueInequalityStep`, `StoppedLLowerBoundStep` (E-c1-5).
Lemma 2.13 is proved (`maximumPrinciple_of_steps` with `adjacentCellsMeetAeStep`) and Lemma 5.2 (relaxed) is reduced to
Lemmas 2.7 and 2.8 (`generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize`).
-/

namespace MatedCRT

/-- **Proposition 5.1** from cited results, earlier Draft statements and the open steps listed in the module
docstring. -/
theorem iDLALowerBound_final (𝒮 : SpaceFillingSLEModel)
    -- cited
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h215 : GreenFunctionCrudeBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    -- earlier results (reduced elsewhere)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h23 : ConeHarmonicBallsStmt) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    -- open steps
    (hμ : LQGMeasureFieldMeasurableStep 𝒮) (hlow : MeanValueSurplusLowerStep 𝒮)
    (hI : ObstacleClusterInnerApproximationStep 𝒮)
    (hSM : StoppedMeanValueInequalityStep 𝒮) (hSL : StoppedLLowerBoundStep 𝒮) :
    IDLALowerBoundStmt 𝒮 := by
  have h213 : MaximumPrincipleStmt 𝒮 := maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)
  have h53 : MeanValueInequalityStmt 𝒮 :=
    meanValueInequality_of_lower 𝒮 h44 h213 h41 h33 h218 h217 hμ hlow
  have h54 : LLowerBoundStmt 𝒮 := lLowerBound_of_inputs 𝒮 h215 h216 h29
  have hD : DiscreteClusterInnerBoundStep 𝒮 := discreteClusterInnerBound_of_steps 𝒮 hI h41 h23 h213 h33 h28
  have hstop : IDLALowerBoundStoppedStep 𝒮 :=
    iDLALowerBoundStopped_of_steps 𝒮 (generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize 𝒮 h27 h28) hSM hSL h28
  exact iDLALowerBound_of_volumeGrowth_cellSize 𝒮 h27 h28 h53 h54 hD hstop

/-- **Proposition 5.1** with the step of Proposition 4.2 replaced by the strict obstacle gap on the harmonic ball
(`HarmonicBallStrictObstacleGapStep`, E-x3-1/E-c2-5), Lemma 2.4 and cone-family measurability
(`discreteClusterInnerBound_final`). -/
theorem iDLALowerBound_final_of_strictGap (𝒮 : SpaceFillingSLEModel)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h215 : GreenFunctionCrudeBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h23 : ConeHarmonicBallsStmt) (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (hfam : ConeFamilyAEMeasurableStep) (hμ : LQGMeasureFieldMeasurableStep 𝒮) (hlow : MeanValueSurplusLowerStep 𝒮)
    (hgap : HarmonicBallStrictObstacleGapStep 𝒮)
    (hSM : StoppedMeanValueInequalityStep 𝒮) (hSL : StoppedLLowerBoundStep 𝒮) :
    IDLALowerBoundStmt 𝒮 :=
  iDLALowerBound_final 𝒮 h27 h28 h29 h215 h216 h218 h41 h23 h33 h217 h44 hμ hlow
    (obstacleClusterInnerApproximation_of_strictGap 𝒮 h27 hfam h24 hgap) hSM hSL

end MatedCRT
