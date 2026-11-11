import MatedCRT.Proofs.Sec5.StoppedSurplusSteps
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Final
import MatedCRT.Proofs.Measurability.LQGMeasureField
import MatedCRT.Steps.Sec2.MaximumPrinciple

/-!
# Lemmas 5.3 and 5.4 on `V^ε(Λ_t)`: final forms

* `stoppedLLowerBound_of_inputs` (Proofs/Sec5/StoppedLLowerBound.lean): `StoppedLLowerBoundStep` from Lemmas 2.9, 2.15
  and 2.16.
* `stoppedMeanValueInequality_of_steps`: `StoppedMeanValueInequalityStep` from Theorem 4.1, Lemmas 3.3, 3.4, 2.17,
  2.18 and the three estimates on the obstacle surplus (`StoppedSurplusInteriorStep`, `StoppedSurplusExteriorStep`,
  `StoppedLayerPotentialStep`); the corrected Lemma 4.4, Lemma 2.13 and the `σ(h)`-measurability of `μ_h` are
  discharged.
-/

namespace MatedCRT

/-- **Lemma 5.3 on `V^ε(Λ_t)`** from Theorem 4.1, Lemmas 3.3, 3.4, 2.17, 2.18 and the interior, exterior and
boundary-layer estimates on the obstacle surplus. -/
theorem stoppedMeanValueInequality_of_steps (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h1 : StoppedSurplusInteriorStep 𝒮) (h2 : StoppedSurplusExteriorStep 𝒮)
    (h3 : StoppedLayerPotentialStep 𝒮) : StoppedMeanValueInequalityStep 𝒮 :=
  stoppedMeanValueInequality_of_surplusLower 𝒮 (discreteLaplacianBoundCorrected 𝒮)
    (maximumPrinciple_of_steps (adjacentCellsMeetAeStep 𝒮)) h41 h33 h218 h34 h217
    (LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮) (stoppedMeanValueSurplusLower_of_steps 𝒮 h1 h2 h3)

end MatedCRT
