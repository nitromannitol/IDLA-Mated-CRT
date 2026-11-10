import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.S3S4b
import MatedCRT.FirstPass.S3S4c
import MatedCRT.FirstPass.S3f
import MatedCRT.FirstPass.Closure.SLEPackage

/-!
# Closed results, Section 3 (task fp-Closure-counted-results and fp-S3f-3-7-corrected-and-closure, worker z1)

Closed for a model `𝒮` with normalized law `ν` (`hνC`, `hνF`, `hLaw`): 3.1 (`closed_3_1`, S3S4 corrected form; to move to
z12's faithful Lemma 3.1 in S3c.lean when it lands), 3.3 (`closed_3_3`), 3.4 (`closed_3_4`, module `S3S4c`), 3.6
(`closed_3_6`). The package supplies `ExitTimeUpperBoundStmt`, `GreenKernelUpperBoundStmt`, `RandomWalkToLBMStmt`,
`FrozenDiscreteHolderContinuityCorrected` and `FrozenTruncatedQuenchedLawsFixedTime`.

Lemma 3.5 (corrected, `closed_3_5`) and Lemma 3.7 (`closed_3_7`, via `firstPass_3_7_corrected` of S3f.lean, whose corrected
Dirichlet input is `closed_3_5`) are closed modulo two named inputs that remain hypotheses: `h36`, the corrected Lemma 3.6
`CorrectedHarmonicConvergenceStmt` (to be `firstPass_3_6_corrected` of z10's S3e.lean, not landed), and `hfinite`, the frozen
`FrozenFiniteDomainDirichletRepresentation` (Frozen/S3S4b.lean).
-/

open MeasureTheory

namespace MatedCRT

/-- Lemma 3.1 (discrete potential tightness), corrected form, for a model with normalized law `ν`. The model input
`MepsScalingInput 𝒮` (BG20 eq. (1.8)) is not supplied by the package and stays a hypothesis. -/
theorem closed_3_1 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνC : SLEReferenceInput ν)
    (hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (hm : MepsScalingInput 𝒮)
    (h27 : VolumeGrowthStmt) : DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  firstPass_3_1_corrected (𝒮 := 𝒮) hm h27 (slePkg_exitTimeUpper hνC hLaw) (slePkg_holder hνF hLaw)

/-- Lemma 3.4 (integral convergence of the Green function), for a model with normalized law `ν`. -/
theorem closed_3_4 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνC : SLEReferenceInput ν)
    (hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (h27 : VolumeGrowthStmt)
    (hscale : MepsScalingInput 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  MatedCRT.S3S4c.firstPass_3_4 (𝒮 := 𝒮) h27 (slePkg_exitTimeUpper hνC hLaw) hscale hrevuz
    (slePkg_truncated hνF hLaw)

/-- Lemma 3.3 (uniform convergence of the Green kernel), for a model with normalized law `ν`. The paper-owned input
`IntegralConvergenceGreenFunctionStmt 𝒮` (Lemma 3.4) is `closed_3_4`. -/
theorem closed_3_3 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνC : SLEReferenceInput ν)
    (hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h27 : VolumeGrowthStmt) (hm : MepsScalingInput 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) : UniformConvergenceGreenKernelStmt 𝒮 :=
  firstPass_3_3 (𝒮 := 𝒮) (h34 := closed_3_4 ν hνC hνF hLaw h27 hm hrevuz) h210
    (slePkg_greenKernelUpper hνC hLaw) h28 h27 (slePkg_exitTimeUpper hνC hLaw) hm (slePkg_holder hνF hLaw)

/-- Lemma 3.6 (convergence of harmonic functions), for a model with normalized law `ν`. -/
theorem closed_3_6 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνC : SLEReferenceInput ν)
    (_hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (h28 : CellSizeEstimateStmt 𝒮)
    (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit) :
    ConvergenceHarmonicFunctionsStmt 𝒮 :=
  firstPass_3_6 (𝒮 := 𝒮) (slePkg_randomWalkToLBM hνC hLaw) h28 hm hexc

/-- Lemma 3.5 (discrete Dirichlet problem), corrected form [C13] (`DiscreteDirichletProblemCorrectedStmt`), for a model with
normalized law `ν`. The corrected Lemma 3.6 `h36` and the frozen finite-domain representation `hfinite` remain inputs. -/
theorem closed_3_5 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνC : SLEReferenceInput ν)
    (hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h27 : VolumeGrowthStmt) (hm : MepsScalingInput 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (hfinite : FrozenFiniteDomainDirichletRepresentation)
    (h36 : CorrectedHarmonicConvergenceStmt 𝒮) : DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  firstPass_3_5_corrected (𝒮 := 𝒮) h27 hm h210 (closed_3_4 ν hνC hνF hLaw h27 hm hrevuz)
    (slePkg_greenKernelUpper hνC hLaw) h28 (slePkg_exitTimeUpper hνC hLaw) (slePkg_holder hνF hLaw) hfinite h36

/-- Lemma 3.7 (convergence of the normalized exit time), for a model with normalized law `ν`: `firstPass_3_7_corrected`
(S3f.lean) with its corrected Lemma 3.5 input `closed_3_5`, and the counted Lemma 3.3 input `closed_3_3`. The inputs
`h36` and `hfinite` are those of `closed_3_5`. -/
theorem closed_3_7 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνC : SLEReferenceInput ν)
    (hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h27 : VolumeGrowthStmt) (hm : MepsScalingInput 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (hfinite : FrozenFiniteDomainDirichletRepresentation)
    (h36 : CorrectedHarmonicConvergenceStmt 𝒮) : ConvergenceNormalizedExitTimeStmt 𝒮 :=
  MatedCRT.FirstPass37.firstPass_3_7_corrected (𝒮 := 𝒮) h27 (slePkg_exitTimeUpper hνC hLaw) hm
    (slePkg_holder hνF hLaw) (closed_3_3 ν hνC hνF hLaw h210 h28 h27 hm hrevuz)
    (closed_3_5 ν hνC hνF hLaw h210 h28 h27 hm hrevuz hfinite h36)

end MatedCRT
