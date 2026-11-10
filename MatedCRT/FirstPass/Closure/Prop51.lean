import MatedCRT.FirstPass.S5q
import MatedCRT.FirstPass.S1S2S8SA
import MatedCRT.FirstPass.Closure.Section3
import MatedCRT.FirstPass.S3g
import MatedCRT.FirstPass.S4S6c
import MatedCRT.FirstPass.SLERef.Certified

/-!
# Closure of Proposition 5.1 (fp-Closure51-closed-5-1, z12)

`closed_5_1 ν hC`: the conclusion `IDLALowerBoundStmt 𝒮` of `firstPass_5_1` (`FirstPass/S5q.lean`), for a model `𝒮`
with certified reference model `hC : CertifiedReferenceModel ν 𝒮` (`FirstPass/SLERef/Certified.lean`).

Discharged from `hC` and the closed theorems of `FirstPass/Closure`:
* `hm`, `h28`, `h210`, `hcone`, `hrevuz`, `h211`, `h214`, `hG16`, `h218`, `hH`, `hdet`: projections of `hC`;
* `h33` = `closed_3_3`, `h35` = `discreteDirichletProblem_of_corrected` with `closed_3_5` and `closed_2_13 hcell`;
* `h41` = `firstPass_4_1_coneLaw` with `closed_3_4`;
* `hGB` = `HarmonicBalls.greenFunctionBall` (unconditional).

Kept as explicit hypotheses:
* FIRST-PASS FROZEN inputs (`Frozen/`), `hcell : FrozenAdjacentCellsMeetAe 𝒮` is the input of `closed_2_13`;
* the two TRUE steps `hE1`, `hE2` (chat 180 §3);
* `hscale` (External, `QuantumConeScalingInput`);
* GAPS, not discharged here (every one is a real gap; see the report):
  - `h27 : VolumeGrowthStmt`: provider `volumeGrowthStmt_of_berestyckiGwynne` needs `BerestyckiGwynneConeBallMassStmt`
    (`MatedCRT/Proposed/BerestyckiGwynne.lean:23`, Proposed, not External);
  - `h22 : LQGMeasurePropertiesStmt`: provider `lqgMeasureProperties_of_volumeGrowth` needs `h27` and the Steps
    `LQGMeasureNonDyadicDilationPart`, `ConeCircleAverageLocalityStep`, `ConeFieldScalingStep`, `ConeScaleRadiusPosStep`
    (truth tags not checked);
  - `h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt`: provider `S2b.lean:170` needs `ConeHarmonicBallLocalityStep`
    (truth tag not checked);
  - `hG15 : GreenFunctionCrudeBoundStmt 𝒮`: no provider in the repository;
  - `h32`, `h611`, `h82`, `hI2`, `hSup`, `hCons`, `hMono`, `hCompat`, `hBdry`, `hEx`, `hThm11`, `hProp56`, `hloc`, `hSC`:
    Harmonic-Balls Draft statements (`HarmonicBalls.*`), whose Harmonic-Balls providers need Proposed inputs
    (`closure_3_2` ... `closure_3_5`, `closure_1_1`, `lqgVolumeGrowthAllScalesStmt_of_ballMass`) or are not yet checked.
-/

open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

namespace MatedCRT.FirstPassClosure

/-- Proposition 5.1 (closure), with the discharged inputs of `firstPass_5_1` replaced by `hC` and the closed theorems. -/
theorem closed_5_1 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    -- FIRST-PASS FROZEN inputs
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮) (hcell : FrozenAdjacentCellsMeetAe 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hG : FrozenGreenDiscPole) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    -- TRUE steps (chat 180 §3)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    -- External input
    (hscale : QuantumConeScalingInput)
    -- GAPS (named, not discharged; see the module docstring)
    (h27 : VolumeGrowthStmt) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (hG15 : GreenFunctionCrudeBoundStmt 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0}) (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0}) :
    IDLALowerBoundStmt 𝒮 := by
  have h35 : DiscreteDirichletProblemStmt 𝒮 :=
    MatedCRT.FirstPass35Bridge.discreteDirichletProblem_of_corrected hC.cellSizeEstimate (firstPass_2_13 (𝒮 := 𝒮) hcell)
      (closed_3_5 ν hC h27 hexc)
  have h41 : ConvergenceDivisibleStmt 𝒮 :=
    firstPass_4_1_coneLaw hC.mepsScaling hC.degreeMeasureConvergence (closed_3_4 ν hC h27)
      hC.greenKernelUpperBound hC.cellSizeEstimate h35 hC.exitTimeUpperBound h27
      hC.frozenDiscreteHolderContinuityCorrected hC.frozenConeScaling
  exact firstPass_5_1 𝒮 hμae hSB hsup h27 hC.cellSizeEstimate hE1 hE2 hscale h22 h24c hC.exitTimeUpperBound hU
    hC.mepsScaling hC.degreeMeasureConvergence hC.greenKernelUpperBound hC.randomWalkToLBM
    hC.frozenLBMGreenOccupation hC.frozenTruncatedQuenchedLaws hexc h35
    hC.frozenDiscreteHolderContinuityCorrected hC.frozenConeScaling hG hG15 hC.greenKernelLowerBound h41
    (closed_3_3 ν hC h27) h32 h611 h82 hI2 hmodel hFL hLoc hpair hmeasT hstd hmin hGBC
    HarmonicBalls.greenFunctionBall hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hconf hK hloc hSC hE

end MatedCRT.FirstPassClosure
