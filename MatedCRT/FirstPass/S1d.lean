import MatedCRT.External.SLE
import MatedCRT.External.QuantumCone
import MatedCRT.FirstPass.S2g
import MatedCRT.FirstPass.S2g.Canonical
import MatedCRT.FirstPass.S1c
import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.S3S4c
import MatedCRT.FirstPass.S4S6c
import MatedCRT.FirstPass.S5S6S7
import MatedCRT.FirstPass.S1S2S8SA
import MatedCRT.Steps.Sec1.Convergence
import MatedCRT.Proofs.Sec1.HarmonicBallScaling
import MatedCRT.Proofs.Sec1.ConeScaleRadius

/-!
# First pass: Theorems 1.4 and 1.6 recomposed without retired inputs (q4, task fp-S1d-1-4-1-6-composition)

`firstPass_1_4` and `firstPass_1_6` replace `firstPass_1_4` / `firstPass_1_6` of FirstPass/S1c/Composition.lean, which
rest on retired inputs. Changes:

* Lemma 2.4 and Lemma 2.5 enter in their corrected canonical forms (`ConeHarmonicBallsUpToFixedTimeCanonicalStmt`,
  `ConeScaleInvarianceUpToFixedTimeCanonicalStmt`, FirstPass/S2g.lean), proved from the open `ConeCanonicalFactorStep`.
  The bridge to Theorem 2.3 (`ConeCanonicalToHarmonicBallsStep`) is OPEN.
* Lemma 3.4 is `MatedCRT.S3S4c.firstPass_3_4` (quenched route; the sample-path inputs are retired).
* Lemma 4.1 is `firstPass_4_1_coneLaw` (FirstPass/S4S6c.lean) with `FrozenConeScalingLaw`; `FrozenConeEnvironmentScaling`
  (FALSE, truth check 2026-11-09) is retired.
* The environment scaling of the convergence reduction enters as `ConeEnvironmentScalingUnderSLE 𝒮`: the statement
  `ConeEnvironmentScalingStep 𝒮` assumed under the three model-closure inputs of External/SLE.lean (the repair of truth
  check 2 and referee route B). It is OPEN: no Lean proof of the rescaled mating-of-trees coupling exists.
* Lemma 3.1 (corrected, `MatedCRT.S3c.firstPass_3_1_corrected`) is not consumed by this chain.
-/

namespace MatedCRT

/-- Repaired environment scaling (truth check 2026-11-09, notes/fp-gaps/TRUTH-CHECK-2.md:50-56; referee route B,
notes/fp-gaps/CHATGPT-sle-inputs-referee.md §4B): the rescaled environment (`η^b = R_b⁻¹ η(b ·)`, `bm^b`, `μ^b`) is valid
for the same γ, for every model 𝒮 that satisfies the three staged SLE closure inputs. OPEN NEW (not frozen). -/
def ConeEnvironmentScalingUnderSLE (𝒮 : SpaceFillingSLEModel) : Prop :=
  SLEScaleInvarianceInput 𝒮 → SLEReparametrizationInput 𝒮 → SLEIndepMonoInput 𝒮 → ConeEnvironmentScalingStep 𝒮

/-- Theorem 2.3 from the corrected canonical Lemmas 2.4 and 2.5 (paper's proof of thm:cone-harmonic-balls). OPEN NEW:
no Lean proof from the canonical forms; `coneHarmonicBalls_of_numbered_results` (RadialContainment.lean:315) uses the
uncorrected Drafts. -/
def ConeCanonicalToHarmonicBallsStep : Prop :=
  ConeHarmonicBallsUpToFixedTimeCanonicalStmt → ConeScaleInvarianceUpToFixedTimeCanonicalStmt → ConeHarmonicBallsStmt

/-- **Theorem 1.4**, first pass without retired inputs: `convergenceOfIDLA_of_steps` fed with the corrected chain. -/
theorem firstPass_1_4 (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (h22 : LQGMeasurePropertiesStmt) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h42 : DivSandpileLowerBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮) (h61 : IDLAUpperBoundStmt 𝒮)
    (hfac : ConeCanonicalFactorStep) (hbr : ConeCanonicalToHarmonicBallsStep)
    (hdiv : FrozenConeRadialDivergence) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont) :
    ConvergenceOfIDLAStmt 𝒮 := by
  have h34 : IntegralConvergenceGreenFunctionStmt 𝒮 :=
    S3S4c.firstPass_3_4 h27 h218 hm hrevuz hdet
  have hcan24 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt := firstPass_2_4_canonical_of_factor hfac
  have hcan25 : ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
    firstPass_2_5_canonical_of_factor hfac hscale h22
  have hcone23 : ConeHarmonicBallsStmt := hbr hcan24 hcan25
  have hconv : ConvergenceDivisibleStmt 𝒮 :=
    firstPass_4_1_coneLaw hm h210 h34 h214 h28 h35 h218 h27 hH hcone
  have hgreen : UniformConvergenceGreenKernelStmt 𝒮 := firstPass_3_3 h210 h34 h214 h28 h27 h218 hm hH
  have h71 : DivSandpileUpperBoundStmt 𝒮 :=
    firstPass_7_1 𝒮 hm hcone23 hdeg h216 h27 h28 h29 h218 hconv hgreen h0 h2 hV hR
  exact convergenceOfIDLA_of_steps 𝒮 (firstPass_8_1 h42 h51 h61 h71) (hEnvS hsc hrp hind)
    harmonicBallFamilyScalingStep (coneScaleRadiusStep_of_input hscale)
    (scaledClusterExitTimeStep_fp hdiv hF1 hF2 hF3)

/-- **Theorem 1.6**, first pass without retired inputs: the hypotheses of `firstPass_1_4`, conclusion for the divisible
sandpile cluster. -/
theorem firstPass_1_6 (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput) (hsc : SLEScaleInvarianceInput 𝒮) (hrp : SLEReparametrizationInput 𝒮)
    (hind : SLEIndepMonoInput 𝒮) (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮)
    (hm : MepsScalingInput 𝒮) (hdeg : DegreeBoundInput 𝒮)
    (h22 : LQGMeasurePropertiesStmt) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail)
    (hR : FPConeMeanZeroRestriction) (hcone : FrozenConeScalingLaw 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h42 : DivSandpileLowerBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮) (h61 : IDLAUpperBoundStmt 𝒮)
    (hfac : ConeCanonicalFactorStep) (hbr : ConeCanonicalToHarmonicBallsStep)
    (hdiv : FrozenConeRadialDivergence) (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF2 : FrozenLQGTestIntegralMeasurable) (hF3 : FrozenDiskGreenNonnegCont) :
    ConvergenceOfDivSandpileStmt 𝒮 := by
  have h34 : IntegralConvergenceGreenFunctionStmt 𝒮 :=
    S3S4c.firstPass_3_4 h27 h218 hm hrevuz hdet
  have hcan24 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt := firstPass_2_4_canonical_of_factor hfac
  have hcan25 : ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
    firstPass_2_5_canonical_of_factor hfac hscale h22
  have hcone23 : ConeHarmonicBallsStmt := hbr hcan24 hcan25
  have hconv : ConvergenceDivisibleStmt 𝒮 :=
    firstPass_4_1_coneLaw hm h210 h34 h214 h28 h35 h218 h27 hH hcone
  have hgreen : UniformConvergenceGreenKernelStmt 𝒮 := firstPass_3_3 h210 h34 h214 h28 h27 h218 hm hH
  have h71 : DivSandpileUpperBoundStmt 𝒮 :=
    firstPass_7_1 𝒮 hm hcone23 hdeg h216 h27 h28 h29 h218 hconv hgreen h0 h2 hV hR
  exact convergenceOfDivSandpile_of_steps 𝒮 (firstPass_8_1 h42 h51 h61 h71) (hEnvS hsc hrp hind)
    harmonicBallFamilyScalingStep (coneScaleRadiusStep_of_input hscale)
    (scaledClusterExitTimeStep_fp hdiv hF1 hF2 hF3)

end MatedCRT
