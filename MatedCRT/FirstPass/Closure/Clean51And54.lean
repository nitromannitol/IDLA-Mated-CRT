import MatedCRT.FirstPass.Closure.H24cBridge
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.S5u
import MatedCRT.FirstPass.S5S6S7
import MatedCRT.FirstPass.SLERef.Certified
import MatedCRT.FirstPass.Frozen.S5BG56
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-!
# Proposition 5.1 and Lemma 5.4 with no Draft binder (task p2-clean-5-1-5-4-then-steps-4-2)

`closed_5_1_clean` is `closed_5_1_ownBinders` (Closure/H24cBridge.lean) with the two paper-own binders of the
Draft form replaced:

* `h22 : LQGMeasurePropertiesStmt` (Lemma 2.2) is supplied by the proved counted form `closed_2_2_ownBinders`
  (Closure/OwnBinderRewire.lean), whose binders are the literature input `hscale`, the Frozen
  `hBG : FrozenBerestyckiGwynneConeBallMass` and the operator-kept Step `hND : LQGMeasureNonDyadicDilationPart`.
* `hG15 : GreenFunctionCrudeBoundStmt 𝒮` (Lemma 2.15) is supplied by the Berestycki–Gwynne canonical Green bound
  `greenFunctionCrudeBound_of_canonical` (FirstPass/S5u.lean:61) from the Frozen input
  `hcanon : FrozenBG20GreenCrudeCanonical 𝒮` (BG20 Lemma 5.6, eq. (5.20); FirstPass/Frozen/S5BG56.lean:18), and the
  proved cell adjacency `adjacentCellsMeetAeStep` (Proofs/MatingOfTrees/AdjacentCells.lean:17).

`closed_5_4_clean` is `firstPass_5_4` (FirstPass/S5S6S7.lean:42) with its three Draft binders discharged:
`h215 : GreenFunctionCrudeBoundStmt 𝒮` as in `closed_5_1_clean`, and `h216 : GreenKernelLowerBoundStmt 𝒮`
(Lemma 2.16) and `h29 : CountingMeasureConvergenceStmt 𝒮` (Lemma 2.9) as the projections of the core certified
reference model `hC : CertifiedReferenceModel ν 𝒮` (FirstPass/SLERef/Certified.lean:103 and :131). The projections are
conjuncts of `hC` (Berestycki–Gwynne Lemma A.4 and Lemma 2.16); no counted row of COUNTED.md covers Lemmas 2.9 or 2.16.
-/

open MeasureTheory
open _root_.HarmonicBalls

namespace MatedCRT.FirstPassClosure

/-- **Proposition 5.1** (prop:IDLA-lower-bound), counted form `closed_5_1_ownBinders` with the Draft binders `h22`
(Lemma 2.2) and `hG15` (Lemma 2.15) discharged: `h22` by `closed_2_2_ownBinders hscale hBG hND`, and `hG15` by the
canonical Berestycki–Gwynne Green bound `greenFunctionCrudeBound_of_canonical` from `hcanon`, with the proved
cell adjacency `adjacentCellsMeetAeStep`. The binders are those of `closed_5_1_ownBinders` minus `h22` and `hG15`,
plus `hND` and `hcanon`. -/
theorem closed_5_1_clean {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
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
    (hND : LQGMeasureNonDyadicDilationPart)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0}) (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1_ownBinders ν hC hμae hSB hsup hU hexc hG hmodel hFL hLoc hpair hmeasT hstd hmin hGBC hconf hK hE hE1 hE2
    hscale (closed_2_2_ownBinders hscale hBG hND)
    (MatedCRT.greenFunctionCrudeBound_of_canonical 𝒮 hcanon (MatedCRT.adjacentCellsMeetAeStep 𝒮))
    h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hBG

/-- **Lemma 5.4** (L lower bound, lemma:L-lower-bound), counted form `firstPass_5_4` with its three Draft binders
discharged: `h215` (Lemma 2.15) by `greenFunctionCrudeBound_of_canonical` from `hcanon` and the proved cell adjacency,
`h216` (Lemma 2.16, `GreenKernelLowerBoundStmt`) and `h29` (Lemma 2.9, `CountingMeasureConvergenceStmt`) by the
projections of the core certified reference model `hC`. The binders are `ν`, `hC`, and `hcanon`. -/
theorem closed_5_4_clean {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hcanon : FrozenBG20GreenCrudeCanonical 𝒮) :
    LLowerBoundStmt 𝒮 :=
  firstPass_5_4 𝒮 (MatedCRT.greenFunctionCrudeBound_of_canonical 𝒮 hcanon (MatedCRT.adjacentCellsMeetAeStep 𝒮))
    hC.greenKernelLowerBound hC.countingMeasureConvergence

end MatedCRT.FirstPassClosure
