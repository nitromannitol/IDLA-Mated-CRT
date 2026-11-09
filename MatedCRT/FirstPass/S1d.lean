import MatedCRT.External.SLE
import MatedCRT.External.QuantumCone
import MatedCRT.FirstPass.S2g
import MatedCRT.FirstPass.S1c
import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.S3S4c
import MatedCRT.FirstPass.S4S6c
import MatedCRT.FirstPass.S5S6S7
import MatedCRT.FirstPass.S1S2S8SA
import MatedCRT.FirstPass.Frozen.S1d
import MatedCRT.Steps.Sec1.Convergence
import MatedCRT.Proofs.Sec1.HarmonicBallScaling
import MatedCRT.Proofs.Sec1.ConeScaleRadius

/-!
# First pass: Theorems 1.4 and 1.6 recomposed without retired inputs (q4, fp-S1d and fp-S1d2)

`firstPass_1_4` and `firstPass_1_6` replace `firstPass_1_4` / `firstPass_1_6` of FirstPass/S1c/Composition.lean, which
rest on retired inputs. Changes:

* Theorem 2.3 (`ConeHarmonicBallsStmt`) is a hypothesis (Draft; operator decision fp-S1d2 (2)). The corrected canonical
  Lemmas 2.4 and 2.5 (`ConeHarmonicBallsUpToFixedTimeCanonicalStmt`, `ConeScaleInvarianceUpToFixedTimeCanonicalStmt`,
  FirstPass/S2g.lean) and `LQGMeasurePropertiesStmt` are hypotheses too (decision (3)), so that the composition does not
  wait on the open `ConeCanonicalFactorStep` of q1. Since 2.3 is taken directly, the hypotheses for `LQGMeasurePropertiesStmt`,
  `ConeHarmonicBallsUpToFixedTimeCanonicalStmt` and `ConeScaleInvarianceUpToFixedTimeCanonicalStmt` were unused and are removed
  (fewer hypotheses; fp-S6d-6-9-faithful, q4).
* Lemma 3.4 is `MatedCRT.S3S4c.firstPass_3_4` (quenched route; the sample-path inputs are retired).
* Lemma 4.1 is `firstPass_4_1_coneLaw` (FirstPass/S4S6c.lean) with `FrozenConeScalingLaw`.
* The environment scaling enters as the frozen EXTERNAL `ConeEnvironmentScalingUnderSLE 𝒮` (Frozen/S1d.lean), with the
  three SLE closure inputs as hypotheses. The retired `FrozenConeEnvironmentScaling` is not used.
* Lemma 3.1 (corrected, `MatedCRT.S3c.firstPass_3_1_corrected`) is not consumed by this chain.
-/

namespace MatedCRT

/-- **Theorem 1.4**, first pass without retired inputs: `convergenceOfIDLA_of_steps` fed with the corrected chain. -/
theorem firstPass_1_4 (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h42 : DivSandpileLowerBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮) (h61 : IDLAUpperBoundStmt 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergence) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont) :
    ConvergenceOfIDLAStmt 𝒮 := by
  have h34 : IntegralConvergenceGreenFunctionStmt 𝒮 :=
    S3S4c.firstPass_3_4 h27 h218 hm hrevuz hdet
  have hconv : ConvergenceDivisibleStmt 𝒮 :=
    firstPass_4_1_coneLaw hm h210 h34 h214 h28 h35 h218 h27 hH hcone
  have hgreen : UniformConvergenceGreenKernelStmt 𝒮 := firstPass_3_3 h210 h34 h214 h28 h27 h218 hm hH
  have h71 : DivSandpileUpperBoundStmt 𝒮 :=
    firstPass_7_1 𝒮 hm h23 hdeg h216 h27 h28 h29 h218 hconv hgreen h0 h2 hV hR
  exact convergenceOfIDLA_of_steps 𝒮 (firstPass_8_1 h42 h51 h61 h71) (hEnvS hsc hrp hind)
    harmonicBallFamilyScalingStep (coneScaleRadiusStep_of_input hscale)
    (scaledClusterExitTimeStep_fp hdiv hF1 hF2 hF3)

/-- **Theorem 1.6**, first pass without retired inputs: the hypotheses of `firstPass_1_4`, conclusion for the divisible
sandpile cluster. -/
theorem firstPass_1_6 (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h42 : DivSandpileLowerBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮) (h61 : IDLAUpperBoundStmt 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hdiv : FrozenConeRadialDivergence) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont) :
    ConvergenceOfDivSandpileStmt 𝒮 := by
  have h34 : IntegralConvergenceGreenFunctionStmt 𝒮 :=
    S3S4c.firstPass_3_4 h27 h218 hm hrevuz hdet
  have hconv : ConvergenceDivisibleStmt 𝒮 :=
    firstPass_4_1_coneLaw hm h210 h34 h214 h28 h35 h218 h27 hH hcone
  have hgreen : UniformConvergenceGreenKernelStmt 𝒮 := firstPass_3_3 h210 h34 h214 h28 h27 h218 hm hH
  have h71 : DivSandpileUpperBoundStmt 𝒮 :=
    firstPass_7_1 𝒮 hm h23 hdeg h216 h27 h28 h29 h218 hconv hgreen h0 h2 hV hR
  exact convergenceOfDivSandpile_of_steps 𝒮 (firstPass_8_1 h42 h51 h61 h71) (hEnvS hsc hrp hind)
    harmonicBallFamilyScalingStep (coneScaleRadiusStep_of_input hscale)
    (scaledClusterExitTimeStep_fp hdiv hF1 hF2 hF3)

end MatedCRT
