import MatedCRT.FirstPass.Main
import MatedCRT.FirstPass.S1c

/-!
# Theorems 1.4 and 1.6, first pass, with hT discharged (fleet note G-hT, Lemma 1)

`firstPassMain_1_4` and `firstPassMain_1_6` (FirstPass/Main.lean) take the step `hT : ScaledClusterExitTimeStep`
(eq:btb-converge-to-inf) as a hypothesis. Here `hT` is supplied by `scaledClusterExitTimeStep_fp`
(FirstPass/S1c.lean), which needs only the frozen external inputs: the cone radial divergence
`FrozenConeRadialDivergenceCorrected` (staged) and the three frozen inputs of Lemma 1 (Lusin, field-level measurability of the
LQG measure, disc Green function). The remaining open hypotheses of the first-pass composition are unchanged.
-/

namespace MatedCRT

/-- Theorem 1.4, first pass: `firstPassMain_1_4` with the step `hT` discharged by the frozen inputs. -/
theorem firstPass_1_4 (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput) (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (h22 : LQGMeasurePropertiesStmt) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hEnv : FrozenConeEnvironmentScaling 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (h211 : RandomWalkToLBMStmt 𝒮) (hrevuz : FrozenLBMGreenOccupation 𝒮)
    (hdet : FrozenTruncatedDetFixedTime 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h42 : DivSandpileLowerBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮) (h61 : IDLAUpperBoundStmt 𝒮)
    (hdiv : FrozenConeRadialDivergenceCorrected) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont) :
    ConvergenceOfIDLAStmt 𝒮 :=
  firstPassMain_1_4 𝒮 hscale hm hdeg h22 h27 h28 h29 h210 h214 h216 h218 hH hEnv h0 h2 hV hR h24 h25 h211
    hrevuz hdet hexc h35 h42 h51 h61 (scaledClusterExitTimeStep_fp hdiv hF1 hF2 hF3)

/-- Theorem 1.6, first pass: `firstPassMain_1_6` with the step `hT` discharged by the frozen inputs. -/
theorem firstPass_1_6 (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput) (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (h22 : LQGMeasurePropertiesStmt) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hEnv : FrozenConeEnvironmentScaling 𝒮)
    (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (h211 : RandomWalkToLBMStmt 𝒮) (hrevuz : FrozenLBMGreenOccupation 𝒮)
    (hdet : FrozenTruncatedDetFixedTime 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h42 : DivSandpileLowerBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮) (h61 : IDLAUpperBoundStmt 𝒮)
    (hdiv : FrozenConeRadialDivergenceCorrected) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  firstPassMain_1_6 𝒮 hscale hm hdeg h22 h27 h28 h29 h210 h214 h216 h218 hH hEnv h0 h2 hV hR h24 h25 h211
    hrevuz hdet hexc h35 h42 h51 h61 (scaledClusterExitTimeStep_fp hdiv hF1 hF2 hF3)

end MatedCRT
