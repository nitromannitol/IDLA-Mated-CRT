import MatedCRT.FirstPass.Frozen.S4S6c
import MatedCRT.FirstPass.S2b
import MatedCRT.FirstPass.S5m
import MatedCRT.FirstPass.S5o
import MatedCRT.FirstPass.S5k
import MatedCRT.FirstPass.S5d.FloorProof
import MatedCRT.FirstPass.S4S5b
import MatedCRT.FirstPass.S2g.HalfBallGate
import MatedCRT.FirstPass.S5r.ClosureInside
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-!
# Proposition 5.1 from the obstacle version

Final assembly of the IDLA lower bound `IDLALowerBoundStmt 𝒮` (Proposition 5.1, `Draft/Section5.lean:27`) from the
measurable obstacle version of §4, `StoppedFloorObstacleVersion 𝒮` (`FirstPass/S5k.lean:31`, the hypothesis `hobs`).

Route. Every `*Step` input is discharged by an existing theorem; the remaining hypotheses are Draft statements,
External Props or FIRST-PASS FROZEN Props.
* `hfc` (`StoppedFloorCellStep`): `FloorProof.stoppedFloorCell_proved` (`FirstPass/S5d/FloorProof.lean:214`), with
  `hcell := adjacentCellsMeetAeStep 𝒮` (`Proofs/MatingOfTrees/AdjacentCells.lean:17`) and
  `hconst := MatedCRT.S5o.floorConstantStep_proved` (`FirstPass/S5o.lean:160`).
* `hgap` (`HarmonicBallStrictObstacleGapStep`, [C20]): `firstPass_strictObstacleGap` (`FirstPass/S4S5b.lean:25`).
* `hcan` (`ConeCanonicalHalfBallStep`): `coneCanonicalHalfBallStep_of_draft` (`FirstPass/S2g/HalfBallGate.lean:16`).
  `coneCanonicalHalfBallStep_of_factor` is NOT used: it is marked CYCLE (`FirstPass/S2g/Assembly24.lean:11`).
* `hcl` (`ConeHalfBallClosureInsideStep`): `S5r.coneHalfBallClosureInsideStep_corrected` (renamed copy of `FirstPass/S2g/Corrected24.lean:33`, `FirstPass/S5r/ClosureInside.lean`; `Corrected24` is not imported because it clashes with `S2b` on `firstPass_2_4_corrected`).
* `hE1`, `hE2` (`ConeCircleLawUniqueStep`, `ConeReferenceExistsStep`) have no proved discharge and remain hypotheses
  (FIRST-PASS FROZEN, `FirstPass/Frozen/S2i.lean`).

Then `firstPass_5_1_of_floorCell` (`FirstPass/S5m.lean:100`) gives the conclusion.

Part (2), `firstPass_5_1`, takes `hobs` from the PROVED `stoppedFloorObstacleVersion_proved`
(`FirstPass/S5k.lean`), so it needs only the three frozen inputs of that theorem. It does not import
`FirstPass/S5p.lean`.
-/

open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

namespace MatedCRT

/-- **Proposition 5.1 from the obstacle version.** The IDLA lower bound `IDLALowerBoundStmt 𝒮` from the
measurable obstacle version `hobs` of §4 (`StoppedFloorObstacleVersion 𝒮`) and the named inputs of the floor and of the
strict obstacle gap; every `*Step` input is discharged by a proved theorem (see the module docstring). -/
theorem firstPass_5_1_of_obstacleVersion (𝒮 : SpaceFillingSLEModel)
    -- volume growth, cell size, cone and exit-time inputs (Draft Section 2 and External)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    -- `hE1`, `hE2`: TRUE
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮)
    (hG : FrozenGreenDiscPole) (hG15 : GreenFunctionCrudeBoundStmt 𝒮) (hG16 : GreenKernelLowerBoundStmt 𝒮)
    -- inputs of the floor `stoppedFloorCell_proved` (Draft Sections 3, 4)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    -- §4 obstacle version and the strict gap of §5 (its inputs)
    (hobs : StoppedFloorObstacleVersion 𝒮)
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
  firstPass_5_1_of_floorCell 𝒮 h27 h28
    (coneCanonicalHalfBallStep_of_draft hU hmeasT hstd hmin hC hGB hG h32 hSup hCons hMono hCompat hBdry hEx
      hThm11 hProp56 hconf)
    (S5r.coneHalfBallClosureInsideStep_corrected hI2 hK hloc hEx hSC h27 hE hFL)
    hE1 hE2 hscale h22 h24c h218
    (FloorProof.stoppedFloorCell_proved h41 h33 h28 hm (adjacentCellsMeetAeStep 𝒮)
      (MatedCRT.S5o.floorConstantStep_proved 𝒮 hobs
        (firstPass_strictObstacleGap 𝒮 h32 h611 h82 hI2 h27 hmodel hFL hLoc hpair)))
    hU hm h210 h214 h211 hrevuz hdet hexc h35 hH hcone hG hG15 hG16

/-- **Proposition 5.1 (part (2)).** `IDLALowerBoundStmt 𝒮` with the §4 obstacle version discharged by the proved
`stoppedFloorObstacleVersion_proved` (`FirstPass/S5k.lean`). Same hypotheses as `firstPass_5_1_of_obstacleVersion`
without `hobs`, plus the three frozen inputs `hμae`, `hSB`, `hsup` of that theorem (`hG` is shared).
Input forms: `h24c` is the provider form of Lemma 2.4 (existence of `T`, `Λ` with the uniqueness clause on
`Ioo 0 T`, no `T' = T`; `ConeHarmonicBallsUpToFixedTimeCorrectedStmt`, the same proposition as `ConeHarmonicBallsProviderFP4`
at `FirstPass/S4d/Provider24.lean:27`); `hrevuz`, `hdet` are `FrozenLBMGreenOccupationRescaled`, `FrozenTruncatedQuenchedLawsFixedTime`
(the retired `FrozenLBMGreenOccupation`, `FrozenTruncatedDetFixedTime` are no longer used); `hcone` is `FrozenConeScalingLaw`
(the retired `FrozenConeEnvironmentScaling` is no longer used). Truth tags: `hE1`, `hE2` TRUE. -/
theorem firstPass_5_1 (𝒮 : SpaceFillingSLEModel)
    -- inputs of `stoppedFloorObstacleVersion_proved` (FIRST-PASS FROZEN, `FirstPass/Frozen/S4S6c.lean`, `Frozen/S5k.lean`)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    -- volume growth, cell size, cone and exit-time inputs (Draft Section 2 and External)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    -- `hE1`, `hE2`: TRUE
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
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
  firstPass_5_1_of_obstacleVersion 𝒮 h27 h28 hE1 hE2 hscale h22 h24c h218 hU hm h210 h214 h211 hrevuz hdet hexc h35
    hH hcone hG hG15 hG16 h41 h33 (stoppedFloorObstacleVersion_proved 𝒮 hμae hSB hsup hG) h32 h611 h82 hI2 hmodel hFL
    hLoc hpair hmeasT hstd hmin hC hGB hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hconf hK hloc hSC hE

end MatedCRT
