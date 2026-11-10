import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.S3S4b
import MatedCRT.FirstPass.S3S4c
import MatedCRT.FirstPass.S3f
import MatedCRT.FirstPass.S3f.FiniteDomainRepresentation
import MatedCRT.FirstPass.Closure.SLEPackage
import MatedCRT.FirstPass.SLERef.Certified

/-!
# Closed results, Section 3 (task fp-Closure-counted-results, fp-S3f-3-7-corrected-and-closure, fp-Closure-round2; worker z1)

Closed for a model `𝒮` with normalized law `ν`: `hνE : SLEReferenceExtendedInput ν`, `hνF : SLEFrozenReferenceInput ν`,
`hLaw : HasNormalizedSLELaw 𝒮 ν`. The certified package supplies the SLE and literature per-model inputs
(`ExitTimeUpperBoundStmt`, `GreenKernelUpperBoundStmt`, `RandomWalkToLBMStmt`, `FrozenDiscreteHolderContinuityCorrected`,
`FrozenTruncatedQuenchedLawsFixedTime`, `MepsScalingInput`, `DegreeBoundInput`, `CellSizeEstimateStmt`,
`CountingMeasureConvergenceStmt`, `DegreeMeasureConvergenceStmt`, `FrozenLBMGreenOccupationRescaled`; see SLEPackage.lean).
Remaining hypotheses: the cited Lemma 2.7 `h27 : VolumeGrowthStmt` where used; `hexc` in 3.6; and `h36 :
CorrectedHarmonicConvergenceStmt 𝒮` (corrected Lemma 3.6) in 3.5 and 3.7, the closure gap of reports/z1.md.

Closed: 3.1 (`closed_3_1`, S3S4 corrected form), 3.3 (`closed_3_3`), 3.4 (`closed_3_4`, module `S3S4c`), 3.6 (`closed_3_6`),
3.5 (`closed_3_5`, corrected form), 3.7 (`closed_3_7`, via `firstPass_3_7_corrected` of S3f.lean, whose corrected Dirichlet
input is `closed_3_5`). The finite-domain representation is proved in S3f/FiniteDomainRepresentation.lean.
-/

open MeasureTheory

namespace MatedCRT

/-- Lemma 3.1 (discrete potential tightness), corrected form, for a model with normalized law `ν`. -/
theorem closed_3_1 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt) : DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  firstPass_3_1_corrected (𝒮 := 𝒮) hC.mepsScaling h27 hC.bg20Prop51 hC.frozenDiscreteHolderContinuityCorrected

/-- Lemma 3.4 (integral convergence of the Green function), for a model with normalized law `ν`. -/
theorem closed_3_4 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνE : SLEReferenceExtendedInput ν)
    (hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (h27 : VolumeGrowthStmt) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  MatedCRT.S3S4c.firstPass_3_4 (𝒮 := 𝒮) h27 (slePkg_exitTimeUpper hνE.1 hLaw) (slePkg_mepsScaling hνE hLaw)
    (slePkg_frozenLBM hνE hLaw) (slePkg_truncated hνF hLaw)

/-- Lemma 3.3 (uniform convergence of the Green kernel), for a model with normalized law `ν`. The paper-owned input
`IntegralConvergenceGreenFunctionStmt 𝒮` (Lemma 3.4) is `closed_3_4`. -/
theorem closed_3_3 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνE : SLEReferenceExtendedInput ν)
    (hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (h27 : VolumeGrowthStmt) :
    UniformConvergenceGreenKernelStmt 𝒮 :=
  firstPass_3_3 (𝒮 := 𝒮) (h34 := closed_3_4 ν hνE hνF hLaw h27) (slePkg_degreeMeasure hνE hLaw)
    (slePkg_greenKernelUpper hνE.1 hLaw) (slePkg_cellSize hνE hLaw) h27 (slePkg_exitTimeUpper hνE.1 hLaw)
    (slePkg_mepsScaling hνE hLaw) (slePkg_holder hνF hLaw)

/-- Lemma 3.6 (convergence of harmonic functions), for a model with normalized law `ν`. -/
theorem closed_3_6 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνE : SLEReferenceExtendedInput ν)
    (_hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (hexc : FrozenBrownianOutwardExcursionAtExit) :
    ConvergenceHarmonicFunctionsStmt 𝒮 :=
  firstPass_3_6 (𝒮 := 𝒮) (slePkg_randomWalkToLBM hνE.1 hLaw) (slePkg_cellSize hνE hLaw)
    (slePkg_mepsScaling hνE hLaw) hexc

/-- Lemma 3.5 (discrete Dirichlet problem), corrected form [C13] (`DiscreteDirichletProblemCorrectedStmt`), for a model with
normalized law `ν`. The corrected Lemma 3.6 `h36` remains an input; the finite-domain representation is proved
(`frozenFiniteDomainDirichletRepresentation_proved`, S3f/FiniteDomainRepresentation.lean). -/
theorem closed_3_5 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνE : SLEReferenceExtendedInput ν)
    (hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (h27 : VolumeGrowthStmt)
    (h36 : CorrectedHarmonicConvergenceStmt 𝒮) :
    DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  firstPass_3_5_corrected (𝒮 := 𝒮) h27 (slePkg_mepsScaling hνE hLaw) (slePkg_degreeMeasure hνE hLaw)
    (closed_3_4 ν hνE hνF hLaw h27) (slePkg_greenKernelUpper hνE.1 hLaw) (slePkg_cellSize hνE hLaw)
    (slePkg_exitTimeUpper hνE.1 hLaw) (slePkg_holder hνF hLaw)
    MatedCRT.FirstPass37.frozenFiniteDomainDirichletRepresentation_proved h36

/-- Lemma 3.7 (convergence of the normalized exit time), for a model with normalized law `ν`: `firstPass_3_7_corrected`
(S3f.lean) with its corrected Lemma 3.5 input `closed_3_5`, and the counted Lemma 3.3 input `closed_3_3`. The input
`h36` is that of `closed_3_5`. -/
theorem closed_3_7 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hνE : SLEReferenceExtendedInput ν)
    (hνF : SLEFrozenReferenceInput ν) (hLaw : HasNormalizedSLELaw 𝒮 ν) (h27 : VolumeGrowthStmt)
    (h36 : CorrectedHarmonicConvergenceStmt 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 :=
  MatedCRT.FirstPass37.firstPass_3_7_corrected (𝒮 := 𝒮) h27 (slePkg_exitTimeUpper hνE.1 hLaw)
    (slePkg_mepsScaling hνE hLaw) (slePkg_holder hνF hLaw) (closed_3_3 ν hνE hνF hLaw h27)
    (closed_3_5 ν hνE hνF hLaw h27 h36)

end MatedCRT
