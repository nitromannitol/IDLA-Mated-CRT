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
import MatedCRT.FirstPass.Closure.Final22
import MatedCRT.FirstPass.Phase2Rewire
import MatedCRT.FirstPass.S3i.LensStep
import MatedCRT.FirstPass.S3i.ExitAlmostSure
import MatedCRT.FirstPass.S3i.QuenchedBoundsCorrected
import MatedCRT.FirstPass.S3S4

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
open _root_.HarmonicBalls

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

/-- Leaf for `LQGMeasurePropertiesStmt` (Lemma 2.2, cited from DS11 and SW16): the counted form
`closed_2_2_lit` with its binders `hscale`, `hBG` (Frozen) and `hND`. -/
theorem closed_2_2_ownBinders (hscale : QuantumConeScalingInput)
    (hBG : FrozenBerestyckiGwynneConeBallMass) (hND : LQGMeasureNonDyadicDilationPart) :
    LQGMeasurePropertiesStmt :=
  closed_2_2_lit hscale hBG hND

/-- Lemma 6.10 (iterative bound) with `h27` supplied as above; the Frozen binders `h0`, `h2`,
`hV`, `hR` stay. -/
theorem closed_6_10_ownBinders (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) :
    IterativeBoundStmt 𝒮 :=
  closed_6_10 (𝒮 := 𝒮) (ν := ν) (hC := hC) (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG)
    (h0 := h0) (h2 := h2) (hV := hV) (hR := hR)

/-- Lemma 2.4 (cone harmonic balls up to a fixed time, canonical form) with `h27` supplied as above;
the other binders are those of `firstPass_2_4_canonical_p2` (Phase2Rewire.lean:199). -/
theorem firstPass_2_4_ownBinders
    (hstd : FrozenConeLogLocalCodeLawStd) (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0}) (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw) (hBG : FrozenBerestyckiGwynneConeBallMass) :
    ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
  MatedCRT.Phase2.firstPass_2_4_canonical_p2 hstd hCentre hOpen hSup hCons hMono hCompat hBdry
    hExist hThm11 hProp56 hconf hI2 hK hloc hSC hE hFL
    (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG)

/-- Lemma 2.5 (scale invariance up to a fixed time, canonical form) with `h27` supplied as above and
`h22` (`LQGMeasurePropertiesStmt`) supplied by `closed_2_2_ownBinders`. The Step-named binders
`hE1`, `hE2` stay as in `firstPass_2_5_canonical_p2` (Phase2Rewire.lean:229). -/
theorem firstPass_2_5_ownBinders
    (hstd : FrozenConeLogLocalCodeLawStd) (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0}) (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (hND : LQGMeasureNonDyadicDilationPart) :
    ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
  MatedCRT.Phase2.firstPass_2_5_canonical_p2 hstd hCentre hOpen hSup hCons hMono hCompat hBdry
    hExist hThm11 hProp56 hconf hI2 hK hloc hSC hE hFL hE1 hE2 hscale
    (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG) (h22 := closed_2_2_ownBinders hscale hBG hND)

/-- Lemma 2.6 (scale invariance, corrected form) with `h27` and `h22` supplied as in
`firstPass_2_5_ownBinders` (Phase2Rewire.lean:264). -/
theorem firstPass_2_6_ownBinders
    (hstd : FrozenConeLogLocalCodeLawStd) (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0}) (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (hND : LQGMeasureNonDyadicDilationPart) :
    ConeScaleInvarianceStmt :=
  MatedCRT.Phase2.firstPass_2_6_corrected_p2 hstd hCentre hOpen hSup hCons hMono hCompat hBdry
    hExist hThm11 hProp56 hconf hI2 hK hloc hSC hE hFL hE1 hE2 hscale
    (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG) (h22 := closed_2_2_ownBinders hscale hBG hND)

open MatedCRT.FirstPass36 in

/-- Lemma 4.1 (convergence of the divisible sandpile, `ConvergenceDivisibleStmt`) with `h210`, `h34`,
`h214`, `h28`, `h218` and `h27` supplied from the reference-model wrappers. The binder `h35`
(`DiscreteDirichletProblemStmt`, the uncorrected form of Lemma 3.5) stays: no counted theorem
concludes it. -/
theorem firstPass_4_1_ownBinders (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hm : MepsScalingInput 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮) :
    ConvergenceDivisibleStmt 𝒮 :=
  firstPass_4_1 (𝒮 := 𝒮) (hm := hm)
    (h210 := CertifiedReferenceModel.degreeMeasureConvergence hC)
    (h34 := closed_3_4_ownBinders 𝒮 ν hC hBG)
    (h214 := CertifiedReferenceModel.greenKernelUpperBound hC)
    (h28 := CertifiedReferenceModel.cellSizeEstimate hC) (h35 := h35)
    (h218 := CertifiedReferenceModel.exitTimeUpperBound hC)
    (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG) (hH := hH) (hcone := hcone)

end MatedCRT
