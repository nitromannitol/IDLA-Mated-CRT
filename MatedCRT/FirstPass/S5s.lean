import MatedCRT.FirstPass.S5q
import MatedCRT.FirstPass.S5s.Copies

open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

namespace MatedCRT

/-- **Proposition 5.1 from the ball form of Lemma 2.18** (z2, fp-S5-exit-ball). Same binders and conclusion as
`firstPass_5_1` (`FirstPass/S5q.lean`), except that the exit-time input is the ball clause
`ExitTimeUpperBoundBallStmt` (`FirstPass/SLERef/Corrected.lean`, Berestycki-Gwynne Proposition 5.1 for balls
`ball x s ⊆ ball 0 ρ`), in place of the printed `ExitTimeUpperBoundStmt`. The chain is the ball copies in
`FirstPass/S5s/Copies.lean` (`MatedCRT.ball_*`). -/
theorem firstPass_5_1_ball (𝒮 : SpaceFillingSLEModel)
    -- inputs of `stoppedFloorObstacleVersion_proved` (FIRST-PASS FROZEN, `FirstPass/Frozen/S4S6c.lean`, `Frozen/S5k.lean`)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    -- volume growth, cell size, cone and exit-time inputs (Draft Section 2 and External)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    -- `hE1`, `hE2`: TRUE (chat 180 §3)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (h218b : ExitTimeUpperBoundBallStmt 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮)
    (hG : FrozenGreenDiscPole) (hG15 : GreenFunctionCrudeBoundStmt 𝒮) (hG16 : GreenKernelLowerBoundStmt 𝒮)
    -- inputs of the floor `stoppedFloorCell_proved` (Draft Sections 3, 4)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    -- inputs of the strict obstacle gap `firstPass_strictObstacleGap` (§5)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0}) (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4)
    -- inputs of the canonical half-ball step `coneCanonicalHalfBallStep_of_draft`
    (hmeasT : FrozenLQGTestIntegralMeasurable) (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hC : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    -- inputs of the closure step `coneHalfBallClosureInsideStep_corrected`
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) (hloc : HarmonicBallLocalSetStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0}) (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) :
    IDLALowerBoundStmt 𝒮 :=
  MatedCRT.ball_firstPass_5_1_of_obstacleVersion 𝒮 h27 h28 hE1 hE2 hscale h22 h24c h218b hU hm h210 h214 h211 hrevuz hdet hexc h35
    hH hcone hG hG15 hG16 h41 h33 (stoppedFloorObstacleVersion_proved 𝒮 hμae hSB hsup hG) h32 h611 h82 hI2 hmodel hFL
    hLoc hpair hmeasT hstd hmin hC hGB hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hconf hK hloc hSC hE

end MatedCRT

#print axioms MatedCRT.firstPass_5_1_ball
