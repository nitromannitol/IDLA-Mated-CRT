import MatedCRT.FirstPass.Closure.Section2
import MatedCRT.FirstPass.Closure.Prop51
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-!
# Counted forms without the duplicate cell-adjacency binder

The binder `hcell : FrozenAdjacentCellsMeetAe 𝒮` (the mating-of-trees fact that cells of adjacent vertices meet almost
surely, Frozen/S1S2S8SA.lean:16) has the same body as `AdjacentCellsMeetAeStep 𝒮` (Steps/Infra/MatingOfTrees.lean:30),
which is proved as `MatedCRT.adjacentCellsMeetAeStep` (Proofs/MatingOfTrees/AdjacentCells.lean:17). The wrappers below
apply the counted theorems `closed_2_13` and `closed_5_1`, which bind `hcell`, to that proof. They bind no `hcell`;
every other binder is that of the theorem they apply.
-/

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

namespace MatedCRT

/-- **Lemma 2.13** (lemma:maximum-principle), counted form without the binder `hcell`. -/
theorem closed_2_13_cellRewire {𝒮 : SpaceFillingSLEModel} : MaximumPrincipleStmt 𝒮 :=
  closed_2_13 (adjacentCellsMeetAeStep 𝒮)

end MatedCRT

namespace MatedCRT.FirstPassClosure

/-- **Proposition 5.1** (prop:IDLA-lower-bound), counted form without the binder `hcell`. The binders are
those of `closed_5_1` (Closure/Prop51.lean:44) minus `hcell`. -/
theorem closed_5_1_cellRewire {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hG : FrozenGreenDiscPole) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (h27 : VolumeGrowthStmt) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (hG15 : GreenFunctionCrudeBoundStmt 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0}) (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0}) :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1 (𝒮 := 𝒮) ν hC hμae hSB hsup (MatedCRT.adjacentCellsMeetAeStep 𝒮) hU hexc hG hmodel hFL hLoc hpair
    hmeasT hstd hmin hGBC hconf hK hE hE1 hE2 hscale h27 h22 h24c hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry
    hEx hThm11 hProp56 hloc hSC

end MatedCRT.FirstPassClosure
