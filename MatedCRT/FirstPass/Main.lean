import MatedCRT.External.QuantumCone
import MatedCRT.External.SLE
import MatedCRT.FirstPass.Frozen.S3S4
import MatedCRT.FirstPass.Frozen.S5S6S7
import MatedCRT.FirstPass.S1S2S8SA
import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.S5S6S7
import MatedCRT.Steps.Sec1.Convergence
import MatedCRT.Proofs.Sec1.HarmonicBallScaling
import MatedCRT.Proofs.Sec1.ConeScaleRadius

/-!
# First pass: composition of Theorems 1.4 and 1.6 (q4, fp-IDLA-main-composition)

Each main theorem is obtained from the reduction of its scaling argument (`convergenceOfIDLA_of_steps`,
`convergenceOfDivSandpile_of_steps`, Steps/Sec1/Convergence.lean) by instantiating the Draft statements of the
numbered results with the committed first-pass theorems, recursively:

* Proposition 8.1 (`firstPass_8_1`) needs Propositions 4.2, 5.1, 6.1 (open) and Proposition 7.1, which is
  `firstPass_7_1`; that needs Theorem 2.3 (`firstPass_2_3`, open Lemmas 2.4 and 2.5), Theorem 4.1 (`firstPass_4_1`,
  open Lemmas 3.4 and 3.5) and Lemma 3.3 (`firstPass_3_3`).
* The scaling of the quantum cone (`coneScaleRadiusStep_of_input`), the scaling of the harmonic-ball families
  (`harmonicBallFamilyScalingStep`, proved) and the environment scaling are the remaining inputs.

The hypotheses of the two theorems are therefore (i) EXTERNAL Props (general mathematics, cited Draft statements,
frozen first-pass inputs), (ii) Draft statements of numbered results not yet PROVED-FP, and (iii) the open NEW step
`ScaledClusterExitTimeStep` (eq:btb-converge-to-inf). The full classification with locators is in
docs/campaign/FIRST-PASS-INPUTS.md. No new frozen Prop is introduced here.
-/

namespace MatedCRT

/-- **Theorem 1.4** (theorem:convergence-of-IDLA, line 251), first-pass composition.

Hypotheses, grouped as in docs/campaign/FIRST-PASS-INPUTS.md:
* EXTERNAL: `hscale` (DMS14 Proposition 4.13(i)), `hm` (eq:meps-scaling), `hdeg` (eq:degree-bound), `h22` (Fact 2.2),
  `h27`, `h28`, `h29`, `h210`, `h214`, `h216`, `h218` (cited Lemmas 2.7-2.18), `hH` (Lemma 3.2 corrected, GMS19),
  `hEnv` (environment scaling, DMS14 and mating of trees; frozen as `FrozenConeEnvironmentScaling`), `h0`-`hR` (the
  frozen whole-plane and cone inputs of FirstPass/Frozen/S5S6S7).
* Open Draft statements: `h24` (Lemma 2.4), `h25` (Lemma 2.5), `h34` (Lemma 3.4), `h35` (Lemma 3.5), `h42`
  (Proposition 4.2), `h51` (Proposition 5.1), `h61` (Proposition 6.1).
* Open NEW step: `hT` (eq:btb-converge-to-inf, line 3330). -/
theorem firstPassMain_1_4 (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput) (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (h22 : LQGMeasurePropertiesStmt) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hEnv : FrozenConeEnvironmentScaling 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h1 : FPConeWholePlaneWeylComparison)
    (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h42 : DivSandpileLowerBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮) (h61 : IDLAUpperBoundStmt 𝒮)
    (hT : ScaledClusterExitTimeStep) :
    ConvergenceOfIDLAStmt 𝒮 := by
  have hcone : ConeHarmonicBallsStmt := firstPass_2_3 h24 h25 h27 hscale h22
  have hconv : ConvergenceDivisibleStmt 𝒮 := firstPass_4_1 hm h210 h34 h214 h28 h35 h218 h27 hH hEnv
  have hgreen : UniformConvergenceGreenKernelStmt 𝒮 := firstPass_3_3 h210 h34 h214 h28 h27 h218 hm hH
  have h71 : DivSandpileUpperBoundStmt 𝒮 :=
    firstPass_7_1 𝒮 hm hcone hdeg h216 h27 h28 h29 h218 hconv hgreen h0 h1 h2 hV hR
  exact convergenceOfIDLA_of_steps 𝒮 (firstPass_8_1 h42 h51 h61 h71) hEnv harmonicBallFamilyScalingStep
    (coneScaleRadiusStep_of_input hscale) hT

/-- **Theorem 1.6** (theorem:convergence-of-div-sandpile, line 283), first-pass composition: Theorem 1.4 for the
divisible sandpile cluster. The hypotheses are those of `firstPassMain_1_4`, with the same classification. -/
theorem firstPassMain_1_6 (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput) (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (h22 : LQGMeasurePropertiesStmt) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hEnv : FrozenConeEnvironmentScaling 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h1 : FPConeWholePlaneWeylComparison)
    (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h42 : DivSandpileLowerBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮) (h61 : IDLAUpperBoundStmt 𝒮)
    (hT : ScaledClusterExitTimeStep) :
    ConvergenceOfDivSandpileStmt 𝒮 := by
  have hcone : ConeHarmonicBallsStmt := firstPass_2_3 h24 h25 h27 hscale h22
  have hconv : ConvergenceDivisibleStmt 𝒮 := firstPass_4_1 hm h210 h34 h214 h28 h35 h218 h27 hH hEnv
  have hgreen : UniformConvergenceGreenKernelStmt 𝒮 := firstPass_3_3 h210 h34 h214 h28 h27 h218 hm hH
  have h71 : DivSandpileUpperBoundStmt 𝒮 :=
    firstPass_7_1 𝒮 hm hcone hdeg h216 h27 h28 h29 h218 hconv hgreen h0 h1 h2 hV hR
  exact convergenceOfDivSandpile_of_steps 𝒮 (firstPass_8_1 h42 h51 h61 h71) hEnv harmonicBallFamilyScalingStep
    (coneScaleRadiusStep_of_input hscale) hT

end MatedCRT
