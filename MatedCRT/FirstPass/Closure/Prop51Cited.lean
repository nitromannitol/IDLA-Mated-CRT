import MatedCRT.FirstPass.Closure.Prop51
import MatedCRT.FirstPass.Frozen.S5Cited

/-!
# Closure of Proposition 5.1 with the cited inputs frozen

`closed_5_1_cited` has the hypotheses and the conclusion of `closed_5_1` (`MatedCRT/FirstPass/Closure/Prop51.lean`). The
cited Harmonic-Balls and BG20 gap hypotheses are typed by their FIRST-PASS FROZEN names from
`MatedCRT/FirstPass/Frozen/S5Cited.lean`: `hG15`, `h611`, `h82`, `hI2`, `hBdry`, `hEx`, `hProp56`, `hloc`, `hSC`.
A frozen name is definitionally its Stmt, so the proof is `closed_5_1` itself.

Still plain Stmt gaps (not frozen by this file): `h27 : VolumeGrowthStmt` (its provider
`volumeGrowthStmt_of_berestyckiGwynne` needs `FrozenBerestyckiGwynneConeBallMass`; wiring it is still pending),
`h22`, `h24c`, `h32`, `hSup`, `hCons`, `hMono`, `hCompat`, `hThm11`.
-/

open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

namespace MatedCRT.FirstPassClosure

/-- Proposition 5.1 (closure with cited inputs frozen). Same conclusion and hypotheses as `closed_5_1`, with the cited
gap inputs typed by the frozen names of `MatedCRT/FirstPass/Frozen/S5Cited.lean`. -/
theorem closed_5_1_cited {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
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
    -- TRUE steps
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    -- External input
    (hscale : QuantumConeScalingInput)
    -- gaps still typed by Stmts
    (h27 : VolumeGrowthStmt) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    -- cited gaps, typed by the frozen names (FirstPass/Frozen/S5Cited.lean)
    (hG15 : FrozenGreenFunctionCrudeBound 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1 ν hC hμae hSB hsup hcell hU hexc hG hmodel hFL hLoc hpair hmeasT hstd hmin hGBC hconf hK hE hE1 hE2
    hscale h27 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC

#print axioms closed_5_1_cited

end MatedCRT.FirstPassClosure
