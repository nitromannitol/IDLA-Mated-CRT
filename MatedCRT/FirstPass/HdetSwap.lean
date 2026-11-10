import MatedCRT.FirstPass.S4d.Final42
import MatedCRT.FirstPass.S3t
import MatedCRT.FirstPass.Closure.Section3

/-!
# Consumers of `FrozenTruncatedQuenchedLawsFixedTime` fed by the closure derivation (fp-hT-consumer-map)

The frozen input `hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮` (`FirstPass/Frozen/S3S4b.lean:102`) is replaced,
in each counted consumer that has no derived variant in `FirstPass/S34d.lean` (Lemma 3.4), `FirstPass/S5qd.lean`
(Proposition 5.1) or `FirstPass/Closure/Theorem14d.lean` (Theorems 1.4 and 1.6), by its derivation
`MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs_closure` (`FirstPass/S3t.lean:365`, z8, commit d275a53).
That derivation takes the named inputs `h211 h28 hmeps hexit hcl`. Each variant keeps the binders of its original, with
`hdet` replaced by these inputs; a binder already present in the original (`hm`, `h28`) is reused. The conclusions are
unchanged. When z8 commits the four-binder theorem `truncatedQuenchedLawsFixedTime_of_inputs` (`h211 h28 hm hexit`),
the binder `hcl` is dropped from each variant and the derivation argument is replaced by that theorem.
-/

namespace MatedCRT

open MeasureTheory

open _root_.HarmonicBalls in
/-- Proposition 4.2 (`firstPass_4_2_of_wholeplane_model`, `FirstPass/S4d/Final42.lean:60`) with the fixed-time
truncated quenched laws derived from the named inputs `h211`, `hexit`, `hcl` (and the binders `hm`, `h28` of the
original). The conclusion `DivSandpileLowerBoundStmt 𝒮` is unchanged. -/
theorem firstPass_4_2_of_wholeplane_model_hdetSwap {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h36 : CorrectedHarmonicConvergenceStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮) (hsc : SLEScaleInvarianceInput 𝒮)
    (hrp : SLEReparametrizationInput 𝒮) (hind : SLEIndepMonoInput 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hexit : BrownianOutwardExcursionAtExitStep)
    (hcl : MatedCRT.TruncatedLaws.BLEnvelopeClosureInput 𝒮)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hG : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hwmp : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hmeasT : FrozenLQGTestIntegralMeasurable)
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
    (hFL : MatedCRT.FPConeWholePlaneFieldLaw)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) :
    DivSandpileLowerBoundStmt 𝒮 :=
  firstPass_4_2_of_wholeplane_model hm h210 h214 h28 h36 h218 h27 hH hEnvS hsc hrp hind hrevuz
    (MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs_closure h211 h28 hm hexit hcl)
    hrescale hG hpc hsmp hwmp hpole hU hmeasT hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist hThm11
    hProp56 hconf hI2 hK hloc hSC hE hFL hE1 hE2 hscale h22

/-- Lemma 3.4 for a certified reference model `hC` (`closed_3_4`, `FirstPass/Closure/Section3.lean:39`), with the
frozen `hC.frozenTruncatedQuenchedLaws` replaced by the closure derivation. The inputs `h211`, `h28`, `hmeps` of that
derivation are the projections `hC.randomWalkToLBM`, `hC.cellSizeEstimate`, `hC.mepsScaling`; `hexit` and `hcl` are
named inputs (they are not conjuncts of `CertifiedReferenceModel`). The conclusion is unchanged. -/
theorem closed_3_4_hdetSwap {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (h27 : VolumeGrowthStmt)
    (hexit : BrownianOutwardExcursionAtExitStep) (hcl : MatedCRT.TruncatedLaws.BLEnvelopeClosureInput 𝒮) :
    IntegralConvergenceGreenFunctionStmt 𝒮 :=
  MatedCRT.S3S4c.firstPass_3_4 (𝒮 := 𝒮) h27 hC.exitTimeUpperBound hC.mepsScaling hC.frozenLBMGreenOccupation
    (MatedCRT.TruncatedLaws.truncatedQuenchedLawsFixedTime_of_inputs_closure hC.randomWalkToLBM
      hC.cellSizeEstimate hC.mepsScaling hexit hcl)

/-- Lemma 3.3 for a certified reference model `hC` (`closed_3_3` in `FirstPass/Closure/Section3.lean`), with its
Lemma 3.4 input `closed_3_4` replaced by `closed_3_4_hdetSwap`. It is consumed by the 5.1 closure
`closed_5_1_canon_noCell_derived` (`FirstPass/S5qd.lean:171`), so it is on the same counted chain. The conclusion is
unchanged. -/
theorem closed_3_3_hdetSwap {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (h27 : VolumeGrowthStmt)
    (hexit : BrownianOutwardExcursionAtExitStep) (hcl : MatedCRT.TruncatedLaws.BLEnvelopeClosureInput 𝒮) :
    UniformConvergenceGreenKernelStmt 𝒮 :=
  firstPass_3_3 (𝒮 := 𝒮) (h34 := closed_3_4_hdetSwap ν hC h27 hexit hcl) hC.degreeMeasureConvergence
    hC.greenKernelUpperBound hC.cellSizeEstimate h27 hC.exitTimeUpperBound hC.mepsScaling
    hC.frozenDiscreteHolderContinuityCorrected

end MatedCRT

#print axioms MatedCRT.firstPass_4_2_of_wholeplane_model_hdetSwap
#print axioms MatedCRT.closed_3_4_hdetSwap
#print axioms MatedCRT.closed_3_3_hdetSwap
