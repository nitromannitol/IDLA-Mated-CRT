import MatedCRT.FirstPass.S5q
import MatedCRT.FirstPass.Closure.Prop51Canon
import MatedCRT.FirstPass.S3t
import MatedCRT.FirstPass.S3t.BLEnvelopeClosure
import MatedCRT.FirstPass.HdetSwap

/-!
# Proposition 5.1 with the truncated quenched laws derived (fp-S3t-consumers, z5)

`firstPass_5_1_derived` is `firstPass_5_1` (`FirstPass/S5q.lean:98`) with the frozen hypothesis
`hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮` removed (it was at `S5q.lean:55` in `firstPass_5_1_of_obstacleVersion`
and at `S5q.lean:111` in `firstPass_5_1`). The `_derived` declarations take the local hypothesis `hT`, standing for the
derivation `truncatedQuenchedLawsFixedTime_of_inputs` (not yet committed). The `_closed` declarations
(`firstPass_5_1_derived_closed`, `closed_5_1_canon_noCell_derived_closed`) use the committed four-binder theorem
`MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs` (`FirstPass/S3t/BLEnvelopeClosure.lean:43`); they have
no `hT` and no routed measurability binder. The old `firstPass_5_1` is unchanged.

`closed_5_1_canon_noCell_derived` is `closed_5_1_canon_noCell` (`Closure/Prop51Canon.lean:70`) with the same substitution.
The closure `closed_5_1` (`Closure/Prop51.lean:43`) took `hdet := hC.frozenTruncatedQuenchedLaws`; here the body is
inlined and `hdet := hT hC.randomWalkToLBM hC.cellSizeEstimate hC.mepsScaling hexc`. The canonical Green bound
(`MatedCRT.greenFunctionCrudeBound_of_canonical`) and the proved cell adjacency (`MatedCRT.adjacentCellsMeetAeStep`) are
used as in `closed_5_1_canon_noCell`.

Terminology: Armstrong–Kuusi–Mourrat for the obstacle problem; Berestycki–Gwynne for the canonical BG20 Green bound.
-/

open MeasureTheory Filter Topology Set Metric
open _root_.HarmonicBalls

namespace MatedCRT

/-- **Proposition 5.1 (first pass), truncated quenched laws derived.** `firstPass_5_1` with `hdet` replaced by `hT`
applied to `h211`, `h28`, `hm`, `hexc`. The binders are those of `firstPass_5_1` in the same order. -/
theorem firstPass_5_1_derived (𝒮 : SpaceFillingSLEModel)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (hT : RandomWalkToLBMStmt 𝒮 → CellSizeEstimateStmt 𝒮 → MepsScalingInput 𝒮 →
      BrownianOutwardExcursionAtExitStep → FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮)
    (hG : FrozenGreenDiscPole) (hG15 : GreenFunctionCrudeBoundStmt 𝒮) (hG16 : GreenKernelLowerBoundStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0}) (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4)
    (hmeasT : FrozenLQGTestIntegralMeasurable) (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hC : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) (hloc : HarmonicBallLocalSetStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) :
    IDLALowerBoundStmt 𝒮 :=
  firstPass_5_1 𝒮 hμae hSB hsup h27 h28 hE1 hE2 hscale h22 h24c h218 hU hm h210 h214 h211 hrevuz
    (hT h211 h28 hm hexc) hexc h35 hH hcone hG hG15 hG16 h41 h33 h32 h611 h82 hI2 hmodel hFL hLoc hpair hmeasT hstd
    hmin hC hGB hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hconf hK hloc hSC hE

open _root_.HarmonicBalls MeasureTheory Set Filter Topology MatedCRT.TruncatedLaws in
/-- **Proposition 5.1 (first pass), truncated quenched laws derived from the four-binder theorem.** `firstPass_5_1` with
its frozen input `hdet` replaced by `truncatedQuenchedLawsFixedTime_of_inputs` (`FirstPass/S3t/BLEnvelopeClosure.lean:43`)
applied to `h211`, `h28`, `hm`, `hexc`. No measurability binder remains (the Brownian measurability is the named closure
input `BLEnvelopeClosureInput`, proved in `blEnvelopeClosureInput_holds`). The other binders are those of `firstPass_5_1`
in the same order, with `hmeas` and `hShellMeas` removed. -/
theorem firstPass_5_1_derived_closed (𝒮 : SpaceFillingSLEModel)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮)
    (hG : FrozenGreenDiscPole) (hG15 : GreenFunctionCrudeBoundStmt 𝒮) (hG16 : GreenKernelLowerBoundStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0}) (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4)
    (hmeasT : FrozenLQGTestIntegralMeasurable) (hstd : FrozenConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hC : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) (hloc : HarmonicBallLocalSetStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) :
    IDLALowerBoundStmt 𝒮 :=
  firstPass_5_1 𝒮 hμae hSB hsup h27 h28 hE1 hE2 hscale h22 h24c h218 hU hm h210 h214 h211 hrevuz
    (MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs h211 h28 hm hexc) hexc h35 hH hcone hG hG15 hG16
    h41 h33 h32 h611 h82 hI2 hmodel hFL hLoc hpair hmeasT hstd hmin hC hGB hSup hCons hMono hCompat hBdry hEx hThm11
    hProp56 hconf hK hloc hSC hE

#print axioms firstPass_5_1_derived_closed

end MatedCRT

namespace MatedCRT.FirstPassClosure

/-- **Proposition 5.1 (closure with the canonical BG20 Green bound and the proved cell adjacency), truncated quenched
laws derived.** Same conclusion and hypotheses as `closed_5_1_canon_noCell`, with the additional local hypothesis `hT`
(see the module docstring); the truncated quenched laws are `hT hC.randomWalkToLBM hC.cellSizeEstimate hC.mepsScaling hexc`
in place of `hC.frozenTruncatedQuenchedLaws`. -/
theorem closed_5_1_canon_noCell_derived {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hT : RandomWalkToLBMStmt 𝒮 → CellSizeEstimateStmt 𝒮 → MepsScalingInput 𝒮 →
      BrownianOutwardExcursionAtExitStep → FrozenTruncatedQuenchedLawsFixedTime 𝒮)
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
    -- TRUE steps (chat 180 §3)
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
    IDLALowerBoundStmt 𝒮 := by
  have hcell : FrozenAdjacentCellsMeetAe 𝒮 := MatedCRT.adjacentCellsMeetAeStep 𝒮
  have hG15 : GreenFunctionCrudeBoundStmt 𝒮 := MatedCRT.greenFunctionCrudeBound_of_canonical 𝒮 hcanon hcell
  have h35 : DiscreteDirichletProblemStmt 𝒮 :=
    MatedCRT.FirstPass35Bridge.discreteDirichletProblem_of_corrected hC.cellSizeEstimate
      (firstPass_2_13 (𝒮 := 𝒮) hcell) (closed_3_5 ν hC h27 hexc)
  have h41 : ConvergenceDivisibleStmt 𝒮 :=
    firstPass_4_1_coneLaw hC.mepsScaling hC.degreeMeasureConvergence (closed_3_4 ν hC h27)
      hC.greenKernelUpperBound hC.cellSizeEstimate h35 hC.exitTimeUpperBound h27
      hC.frozenDiscreteHolderContinuityCorrected hC.frozenConeScaling
  exact firstPass_5_1_derived 𝒮 hμae hSB hsup h27 hC.cellSizeEstimate hE1 hE2 hscale h22 h24c hC.exitTimeUpperBound
    hU hC.mepsScaling hC.degreeMeasureConvergence hC.greenKernelUpperBound hC.randomWalkToLBM
    hC.frozenLBMGreenOccupation hT hexc h35 hC.frozenDiscreteHolderContinuityCorrected hC.frozenConeScaling hG hG15
    hC.greenKernelLowerBound h41 (closed_3_3 ν hC h27) h32 h611 h82 hI2 hmodel hFL hLoc hpair hmeasT hstd hmin hGBC
    HarmonicBalls.greenFunctionBall hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hconf hK hloc hSC hE

#print axioms MatedCRT.firstPass_5_1_derived
#print axioms closed_5_1_canon_noCell_derived

/-- **Lemma 3.5 (discrete Dirichlet problem, corrected), with the truncated quenched laws derived.** `closed_3_5`
(`FirstPass/Closure/Section3.lean:66`) with its Lemma 3.4 input `closed_3_4` replaced by `closed_3_4_hdetSwap`, fed by the
four-binder theorem through `blEnvelopeClosureInput_holds`. The binders are those of `closed_3_5`. It is needed on the
chain of `closed_5_1_canon_noCell_derived_closed` (the `h35` of that proof). -/
theorem closed_3_5_hdetSwap {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (h27 : VolumeGrowthStmt) (hexc : FrozenBrownianOutwardExcursionAtExit) :
    DiscreteDirichletProblemCorrectedStmt 𝒮 :=
  firstPass_3_5_corrected (𝒮 := 𝒮) h27 hC.mepsScaling hC.degreeMeasureConvergence
    (closed_3_4_hdetSwap ν hC h27 hexc (MatedCRT.TruncatedLaws.blEnvelopeClosureInput_holds 𝒮))
    hC.greenKernelUpperBound hC.cellSizeEstimate hC.exitTimeUpperBound hC.frozenDiscreteHolderContinuityCorrected
    MatedCRT.FirstPass37.frozenFiniteDomainDirichletRepresentation_proved (closed_3_6_corrected ν hC hexc)

#print axioms closed_3_5_hdetSwap

/-- **Proposition 5.1 (closure with the canonical BG20 Green bound and the proved cell adjacency), truncated quenched
laws derived from the four-binder theorem.** Same conclusion and hypotheses as `closed_5_1_canon_noCell_derived` with
the local hypothesis `hT` removed: the truncated quenched laws are
`MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs` (`FirstPass/S3t/BLEnvelopeClosure.lean:43`) applied to
`hC.randomWalkToLBM hC.cellSizeEstimate hC.mepsScaling hexc`, and the Lemmas 3.3, 3.4, 3.5 used on the chain are
`closed_3_3_hdetSwap`, `closed_3_4_hdetSwap`, `closed_3_5_hdetSwap` (`FirstPass/HdetSwap.lean`, this file). No binder of
type `FrozenTruncatedQuenchedLawsFixedTime` remains. -/
theorem closed_5_1_canon_noCell_derived_closed {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
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
    -- TRUE steps (chat 180 §3)
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
    IDLALowerBoundStmt 𝒮 := by
  have hcell : FrozenAdjacentCellsMeetAe 𝒮 := MatedCRT.adjacentCellsMeetAeStep 𝒮
  have hG15 : GreenFunctionCrudeBoundStmt 𝒮 := MatedCRT.greenFunctionCrudeBound_of_canonical 𝒮 hcanon hcell
  have h35 : DiscreteDirichletProblemStmt 𝒮 :=
    MatedCRT.FirstPass35Bridge.discreteDirichletProblem_of_corrected hC.cellSizeEstimate
      (firstPass_2_13 (𝒮 := 𝒮) hcell) (closed_3_5_hdetSwap ν hC h27 hexc)
  have h41 : ConvergenceDivisibleStmt 𝒮 :=
    firstPass_4_1_coneLaw hC.mepsScaling hC.degreeMeasureConvergence
      (closed_3_4_hdetSwap ν hC h27 hexc (MatedCRT.TruncatedLaws.blEnvelopeClosureInput_holds 𝒮))
      hC.greenKernelUpperBound hC.cellSizeEstimate h35 hC.exitTimeUpperBound h27
      hC.frozenDiscreteHolderContinuityCorrected hC.frozenConeScaling
  exact firstPass_5_1_derived_closed 𝒮 hμae hSB hsup h27 hC.cellSizeEstimate hE1 hE2 hscale h22 h24c hC.exitTimeUpperBound
    hU hC.mepsScaling hC.degreeMeasureConvergence hC.greenKernelUpperBound hC.randomWalkToLBM
    hC.frozenLBMGreenOccupation hexc h35 hC.frozenDiscreteHolderContinuityCorrected hC.frozenConeScaling
    hG hG15 hC.greenKernelLowerBound h41
    (closed_3_3_hdetSwap ν hC h27 hexc (MatedCRT.TruncatedLaws.blEnvelopeClosureInput_holds 𝒮))
    h32 h611 h82 hI2 hmodel hFL hLoc hpair hmeasT hstd hmin
    hGBC HarmonicBalls.greenFunctionBall hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hconf hK hloc hSC hE

#print axioms closed_5_1_canon_noCell_derived_closed

end MatedCRT.FirstPassClosure
