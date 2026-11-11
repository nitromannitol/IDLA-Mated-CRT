import MatedCRT.FirstPass.Closure.Prop51
import MatedCRT.FirstPass.Frozen.S5Cited
import MatedCRT.FirstPass.Frozen.S5BG56
import MatedCRT.FirstPass.S5u
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-!
# Closure of Proposition 5.1 from the canonical Berestycki–Gwynne Green bound

`closed_5_1_canon` has the hypotheses and the conclusion of `closed_5_1_cited`
(`MatedCRT/FirstPass/Closure/Prop51Cited.lean`), except one hypothesis. The cited Green-function crude bound
`hG15 : FrozenGreenFunctionCrudeBound 𝒮` (Lemma 2.15, `GreenFunctionCrudeBoundStmt`, killing set the interior vertices
`V^ε(B_ρ) \ V^ε(∂B_ρ)`) is replaced by its canonical Berestycki–Gwynne input
`hcanon : FrozenBG20GreenCrudeCanonical 𝒮` (BG20 Lemma 5.6, equation (5.20), killing set `V^ε(B_ρ)`;
`MatedCRT/FirstPass/Frozen/S5BG56.lean:29`). The IDLA form is derived from it by domain monotonicity of the killed
Green function, `MatedCRT.greenFunctionCrudeBound_of_canonical` (`MatedCRT/FirstPass/S5u.lean:61`).

The extra input of that derivation is `hcell : AdjacentCellsMeetAeStep 𝒮` (`MatedCRT/Steps/Infra/MatingOfTrees.lean:30`).
It is supplied by the frozen `hcell : FrozenAdjacentCellsMeetAe 𝒮` already in `closed_5_1_cited`
(`MatedCRT/FirstPass/Frozen/S1S2S8SA.lean:22`), which has the same body, so no new hypothesis is added for it.

Nothing else differs from `closed_5_1_cited`: the other gap hypotheses keep their frozen or Stmt types.
-/

open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

namespace MatedCRT.FirstPassClosure

/-- Proposition 5.1 (closure with the canonical BG20 Green bound). Same conclusion and hypotheses as
`closed_5_1_cited`, except that `hG15` is replaced by `hcanon : FrozenBG20GreenCrudeCanonical 𝒮`, from which the IDLA
crude bound is derived by `MatedCRT.greenFunctionCrudeBound_of_canonical`. -/
theorem closed_5_1_canon {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
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
    -- canonical Berestycki–Gwynne Green bound (replaces the cited Lemma 2.15 input `hG15`)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    -- cited gaps, typed by the frozen names (FirstPass/Frozen/S5Cited.lean)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1 ν hC hμae hSB hsup hcell hU hexc hG hmodel hFL hLoc hpair hmeasT hstd hmin hGBC hconf hK hE hE1 hE2
    hscale h27 h22 h24c (MatedCRT.greenFunctionCrudeBound_of_canonical 𝒮 hcanon hcell) h32 h611 h82 hI2 hSup hCons
    hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC

/-- Proposition 5.1 (closure with the canonical BG20 Green bound and the proved cell adjacency). Same conclusion and
hypotheses as `closed_5_1_canon`, except that the frozen `hcell : FrozenAdjacentCellsMeetAe 𝒮` is removed: it is
discharged by the proved `MatedCRT.adjacentCellsMeetAeStep 𝒮` (`MatedCRT/Proofs/MatingOfTrees/AdjacentCells.lean:17`),
which has the same body. -/
theorem closed_5_1_canon_noCell {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    -- FIRST-PASS FROZEN inputs
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
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
    -- canonical Berestycki–Gwynne Green bound (replaces the cited Lemma 2.15 input `hG15`)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    -- cited gaps, typed by the frozen names (FirstPass/Frozen/S5Cited.lean)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : FrozenVeryGoodAnnulusHarnackType)
    (h82 : FrozenTypicalPointManyGoodScales) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : FrozenClusterBoundaryMeasureZero) (hEx : FrozenExistenceHarmonicBalls)
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : FrozenUniquenessHarmonicBalls)
    (hloc : FrozenHarmonicBallLocalSet) (hSC : FrozenClusterStrongCompatibility) :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1_canon ν hC hμae hSB hsup (MatedCRT.adjacentCellsMeetAeStep 𝒮) hU hexc hG hmodel hFL hLoc hpair hmeasT
    hstd hmin hGBC hconf hK hE hE1 hE2 hscale h27 h22 h24c hcanon h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx
    hThm11 hProp56 hloc hSC

#print axioms closed_5_1_canon
#print axioms closed_5_1_canon_noCell

end MatedCRT.FirstPassClosure
