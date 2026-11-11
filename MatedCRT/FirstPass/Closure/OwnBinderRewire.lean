import MatedCRT.FirstPass.Closure.Section2
import MatedCRT.FirstPass.Closure.Section3
import MatedCRT.FirstPass.Closure.Section4
import MatedCRT.FirstPass.Closure.Section5
import MatedCRT.FirstPass.Closure.Section6
import MatedCRT.FirstPass.S1S2S8SA
import MatedCRT.FirstPass.S3c
import MatedCRT.FirstPass.S3f
import MatedCRT.FirstPass.S4x8
import MatedCRT.FirstPass.SLERef.Certified
import MatedCRT.FirstPass.Frozen.S5Cited
import MatedCRT.Proofs.Sec3.ConeBallMass

/-!
# Counted forms with their own binders rewired

Each wrapper of this file takes a counted form that binds a Draft statement of this paper
(`VolumeGrowthStmt` of Lemma 2.7, `ExitTimeUpperBoundStmt` of Lemma 2.18, and the Draft statements
that these feed into) and instantiates that binder with the counted theorem of the bound result.

The cited Berestycki-Gwynne inputs enter only through the frozen binder
`FrozenBerestyckiGwynneConeBallMass` (volume growth, `volumeGrowthStmt_of_berestyckiGwynne`) and
through the core reference model `CertifiedReferenceModel ν 𝒮` (exit-time upper bound,
`CertifiedReferenceModel.exitTimeUpperBound`). The remaining binders are those of the original
counted form, unchanged.
-/

namespace MatedCRT

open MeasureTheory

/-- Lemma 2.19 (expected exit time, explicit bound) with the volume-growth binder `h27` (Lemma 2.7,
cited from Berestycki-Gwynne, Lemma A.1) supplied by `volumeGrowthStmt_of_berestyckiGwynne`. -/
theorem closed_2_19_ownBinders (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass) :
    ExpectedExitTimeExplicitBoundStmt 𝒮 :=
  closed_2_19 (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG)

/-- Lemma 3.3 (uniform convergence of the rescaled Green kernel) with `h27` supplied as above. -/
theorem closed_3_3_ownBinders (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass) :
    UniformConvergenceGreenKernelStmt 𝒮 :=
  closed_3_3 (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG)

/-- Lemma 3.4 (integral convergence of the Green function) with `h27` supplied as above. -/
theorem closed_3_4_ownBinders (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  closed_3_4 (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG)

/-- Lemma 3.5 (discrete Dirichlet problem, corrected) with `h27` supplied as above. -/
theorem closed_3_5_ownBinders (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hexc : FrozenBrownianOutwardExcursionAtExit) :
    DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  closed_3_5 (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG)
    (hexc := hexc)

/-- Lemma 4.7 (equiboundedness) with `h27` supplied as above. -/
theorem closed_4_7_ownBinders (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass) :
    EquiboundedStmt 𝒮 :=
  closed_4_7 (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG)

/-- Lemma 4.8 (subsequential properties, corrected) with `h27` supplied as above. -/
theorem closed_4_8_corrected_ownBinders (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hexc : FrozenBrownianOutwardExcursionAtExit) :
    SubsequentialPropertiesCorrectedStmt 𝒮 :=
  closed_4_8_corrected (𝒮 := 𝒮) (ν := ν) (hC := hC)
    (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG) (hexc := hexc)

/-- Lemma 5.2 (general lower bound on the IDLA) with `h27` supplied as above. -/
theorem closed_5_2_ownBinders (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass) :
    GeneralIDLALowerBoundStmt 𝒮 :=
  closed_5_2 (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG)

/-- Lemma 2.17 (bounded exit-time random variable) with `h27` supplied as above. -/
theorem firstPass_2_17_ownBinders (hBG : FrozenBerestyckiGwynneConeBallMass) :
    BoundedExitTimeRVStmt :=
  firstPass_2_17 (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG)

/-- Lemma 3.1 (discrete potential tightness, samplewise form) with `h27` and `h218` supplied:
`h218` by the exit-time upper bound of `CertifiedReferenceModel`. The conclusion is that of
`firstPass_3_1_faithful`. The domain `D` carries `IsOpen D`, which is not stated in the paper. -/
theorem firstPass_3_1_ownBinders (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) :
    MatedCRT.S3c.DiscretePotentialTightnessPointwiseStmt 𝒮 :=
  MatedCRT.S3c.firstPass_3_1_faithful (𝒮 := 𝒮) (hm := hm)
    (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG)
    (h218 := CertifiedReferenceModel.exitTimeUpperBound hC) (h32 := h32)

/-- Lemma 3.7 (convergence of the normalized exit time, corrected) with `h27`, `h218`, `h33` and
`h35c` supplied from the wrappers of Lemmas 2.7, 2.18, 3.3 and 3.5. -/
theorem firstPass_3_7_ownBinders (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hm : MepsScalingInput 𝒮) (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) :
    ConvergenceNormalizedExitTimeStmt 𝒮 :=
  MatedCRT.FirstPass37.firstPass_3_7_corrected (𝒮 := 𝒮)
    (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG)
    (h218 := CertifiedReferenceModel.exitTimeUpperBound hC) (hm := hm) (h32 := h32)
    (h33 := closed_3_3_ownBinders 𝒮 ν hC hBG)
    (h35c := closed_3_5_ownBinders 𝒮 ν hC hBG hexc)

end MatedCRT
