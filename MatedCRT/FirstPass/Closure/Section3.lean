import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.S3S4b
import MatedCRT.FirstPass.S3S4c
import MatedCRT.FirstPass.S3e
import MatedCRT.FirstPass.S3f
import MatedCRT.FirstPass.S3f.FiniteDomainRepresentation
import MatedCRT.FirstPass.SLERef.Certified

/-!
# Closed results, Section 3 (task fp-Closure-counted-results, fp-S3f-3-7-corrected-and-closure, fp-Closure-round3; worker z1)

Closed for a model `𝒮` with normalized law `ν` and a certified reference model `hC : CertifiedReferenceModel ν 𝒮`
(operator chat 186; `MatedCRT/FirstPass/SLERef/Certified.lean`). Every per-model input below is a projection of `hC`
(`CertifiedReferenceModel.mepsScaling`, `.exitTimeUpperBound`, ...).

Remaining hypotheses: the cited Lemma 2.7 `h27 : VolumeGrowthStmt` where used, and the frozen external
`hexc : FrozenBrownianOutwardExcursionAtExit` in 3.6, 3.5 and 3.7 (the corrected Lemma 3.6 `h36` is no longer an input:
it is `closed_3_6_corrected`, from z10's `firstPass_3_6_convergence_corrected`, S3e.lean).

Closed: 3.1 (`closed_3_1`, S3S4 corrected form, input `hC.bg20Prop51`), 3.3 (`closed_3_3`), 3.4 (`closed_3_4`, module `S3S4c`),
3.6 (`closed_3_6`, printed form `ConvergenceHarmonicFunctionsStmt`; `closed_3_6_corrected`, corrected form
`CorrectedHarmonicConvergenceStmt`, the convergence conjunct only), 3.5 (`closed_3_5`, corrected form), 3.7 (`closed_3_7`,
via `firstPass_3_7_corrected` of S3f.lean). The finite-domain representation is proved in S3f/FiniteDomainRepresentation.lean.
-/

open MeasureTheory

namespace MatedCRT

/-- Lemma 3.1 (discrete potential tightness), corrected form, for a model with certified reference model `hC`. -/
theorem closed_3_1 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt) : DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  firstPass_3_1_corrected (𝒮 := 𝒮) hC.mepsScaling h27 hC.bg20Prop51 hC.frozenDiscreteHolderContinuityCorrected

/-- Lemma 3.4 (integral convergence of the Green function), for a model with certified reference model `hC`. -/
theorem closed_3_4 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt) : IntegralConvergenceGreenFunctionStmt 𝒮 :=
  MatedCRT.S3S4c.firstPass_3_4 (𝒮 := 𝒮) h27 hC.exitTimeUpperBound hC.mepsScaling hC.frozenLBMGreenOccupation
    hC.frozenTruncatedQuenchedLaws

/-- Lemma 3.3 (uniform convergence of the Green kernel), for a model with certified reference model `hC`. The paper-owned
input `IntegralConvergenceGreenFunctionStmt 𝒮` (Lemma 3.4) is `closed_3_4`. -/
theorem closed_3_3 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt) : UniformConvergenceGreenKernelStmt 𝒮 :=
  firstPass_3_3 (𝒮 := 𝒮) (h34 := closed_3_4 ν hC h27) hC.degreeMeasureConvergence hC.greenKernelUpperBound
    hC.cellSizeEstimate h27 hC.exitTimeUpperBound hC.mepsScaling hC.frozenDiscreteHolderContinuityCorrected

/-- Lemma 3.6 (convergence of harmonic functions), printed form `ConvergenceHarmonicFunctionsStmt`, for a model with
certified reference model `hC`. -/
theorem closed_3_6 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) : ConvergenceHarmonicFunctionsStmt 𝒮 :=
  firstPass_3_6 (𝒮 := 𝒮) hC.randomWalkToLBM hC.cellSizeEstimate hC.mepsScaling hexc

/-- Lemma 3.6, corrected form (convergence conjunct): `CorrectedHarmonicConvergenceStmt`, from z10's
`MatedCRT.FirstPass36.firstPass_3_6_convergence_corrected` (S3e.lean), with the corrected Hölder input
`hC.frozenDiscreteHolderContinuityCorrected`. The rate conjunct (`CorrectedHarmonicSameWalkRateStmt`) is not included. -/
theorem closed_3_6_corrected {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit) :
    CorrectedHarmonicConvergenceStmt 𝒮 :=
  MatedCRT.FirstPass36.firstPass_3_6_convergence_corrected (𝒮 := 𝒮) hC.randomWalkToLBM hC.cellSizeEstimate
    hC.mepsScaling hexc hC.frozenDiscreteHolderContinuityCorrected

/-- Lemma 3.5 (discrete Dirichlet problem), corrected form [C13] (`DiscreteDirichletProblemCorrectedStmt`), for a model with
certified reference model `hC`. Its corrected Lemma 3.6 input is `closed_3_6_corrected`; the finite-domain representation is
proved (`frozenFiniteDomainDirichletRepresentation_proved`, S3f/FiniteDomainRepresentation.lean). -/
theorem closed_3_5 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt) (hexc : FrozenBrownianOutwardExcursionAtExit) :
    DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  firstPass_3_5_corrected (𝒮 := 𝒮) h27 hC.mepsScaling hC.degreeMeasureConvergence (closed_3_4 ν hC h27)
    hC.greenKernelUpperBound hC.cellSizeEstimate hC.exitTimeUpperBound hC.frozenDiscreteHolderContinuityCorrected
    MatedCRT.FirstPass37.frozenFiniteDomainDirichletRepresentation_proved (closed_3_6_corrected ν hC hexc)

/-- Lemma 3.7 (convergence of the normalized exit time), for a model with certified reference model `hC`:
`firstPass_3_7_corrected` (S3f.lean) with its corrected Lemma 3.5 input `closed_3_5` and the counted Lemma 3.3 input
`closed_3_3`. The input `hexc` is that of `closed_3_5`. -/
theorem closed_3_7 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt) (hexc : FrozenBrownianOutwardExcursionAtExit) :
    ConvergenceNormalizedExitTimeStmt 𝒮 :=
  MatedCRT.FirstPass37.firstPass_3_7_corrected (𝒮 := 𝒮) h27 hC.exitTimeUpperBound hC.mepsScaling
    hC.frozenDiscreteHolderContinuityCorrected (closed_3_3 ν hC h27) (closed_3_5 ν hC h27 hexc)

end MatedCRT
