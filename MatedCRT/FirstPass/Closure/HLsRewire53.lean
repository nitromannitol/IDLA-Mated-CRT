import MatedCRT.FirstPass.S2g.LawCoded
import MatedCRT.FirstPass.S2i.GlobalFactor
import MatedCRT.FirstPass.S5c.FinalSurplus
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.Closure.Section4
import MatedCRT.FirstPass.Closure.CellRewire
import MatedCRT.FirstPass.Closure.H35CorrectedRewire
import MatedCRT.FirstPass.Closure.Steps42
import MatedCRT.FirstPass.HBRewire
import MatedCRT.FirstPass.LPBridge.MinimumPrinciples
import MatedCRT.FirstPass.LPBridge.UniversalMeasurability
import MatedCRT.FirstPass.LPBridge.BrownianOutwardExcursion
import MatedCRT.FirstPass.LPBridge.InRepoProofs

/-! # Lemma 5.3 in counted form, with the paper-own binder `hLs` discharged

`firstPass_5_3_final` (S5c/FinalSurplus.lean) takes the coded Lemma 2.6 `hLs : ConeScaleInvarianceCodedStmt` as a
binder. This file supplies it: the coded Lemma 2.6 is `firstPass_2_6_coded_of_globalFamilyFactor` (S2g/LawCoded.lean),
whose input is the global family factor `ConeGlobalFamilyFactorStep`, and that factor is
`coneGlobalFamilyFactor_proved` (S2i/GlobalFactor.lean) applied to the canonical half-ball step `hcan`, the closure step
`hcl`, the volume growth of Lemma 2.7, the cone-circle law and reference binders, the cone scaling in law, and the LQG
measure properties of Lemma 2.2 (`closed_2_2_ownBinders`).

The other Draft binders of Lemma 5.3 are supplied by the counted or own-binder forms of this paper: Lemma 4.4 by
`closed_4_4`, Lemma 2.13 by `closed_2_13_cellRewire`, Lemma 3.3 by `closed_3_3_ownBinders`, Lemma 2.17 by
`firstPass_2_17_ownBinders`, Lemma 2.18 by the field `hC.exitTimeUpperBound` of the core reference model, and
Lemma 4.1 (`ConvergenceDivisibleStmt`) by `firstPass_4_1_coneLaw_ownBinders`, the cone-law form of Lemma 4.1 on the
corrected Lemma 3.5. The remaining binders are the paper steps `hcan` and `hcl` (`ConeCanonicalHalfBallStep`,
`ConeHalfBallClosureInsideStep`), the Step `hND`, the Frozen inputs, and the Frozen binders `hexc` (Lemma 3.5
route) and `hcone` (the repaired cone-scaling law of Lemma 4.1, `FrozenConeScalingLaw`). -/

namespace MatedCRT

open MeasureTheory
open _root_.HarmonicBalls

/-- **Lemma 2.6, global family factor.** `ConeGlobalFamilyFactorStep` from the canonical half-ball step `hcan`, the
closure step `hcl`, the cone-circle law and reference binders, the volume growth of Lemma 2.7 (supplied by
`volumeGrowthStmt_of_berestyckiGwynne`), the cone scaling in law `hscale`, and the LQG measure properties of Lemma 2.2
(supplied by `closed_2_2_ownBinders`). -/
theorem coneGlobalFamilyFactor_ownBinders (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hND : LQGMeasureNonDyadicDilationPart) (hscale : QuantumConeScalingInput)
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep) :
    ConeGlobalFamilyFactorStep :=
  coneGlobalFamilyFactor_proved hcan hcl (volumeGrowthStmt_of_berestyckiGwynne hBG) hE1 hE2 hscale
    (closed_2_2_ownBinders hscale hBG hND)

/-- **Lemma 2.6, coded law, with its own binders.** The binder `hLs` of Lemma 5.3: the joint law of the circle process
and of the global code of the family is that of the rescaled pair (`ConeScaleInvarianceCodedStmt`, from the global family
factor `coneGlobalFamilyFactor_ownBinders` through `firstPass_2_6_coded_of_globalFamilyFactor`). -/
theorem coneScaleInvarianceCoded_ownBinders (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hND : LQGMeasureNonDyadicDilationPart) (hscale : QuantumConeScalingInput)
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep) :
    ConeScaleInvarianceCodedStmt :=
  firstPass_2_6_coded_of_globalFamilyFactor
    (coneGlobalFamilyFactor_ownBinders hBG hND hscale hcan hcl hE1 hE2) hscale
    (closed_2_2_ownBinders hscale hBG hND)

/-- **Lemma 4.1 (convergence of the divisible sandpile), cone-law form, with its own binders.**
`firstPass_4_1_coneLaw_h35c` with the Draft binders `h210`, `h34`, `h214`, `h28`, `h218`, `h27` and `hH` supplied by the
core reference model `hC`, and the corrected Lemma 3.5 binder `h35c` supplied by `closed_3_5` (which takes the Frozen
input `hexc`). The Frozen cone-scaling law `hcone` and `hBG` remain. -/
theorem firstPass_4_1_coneLaw_ownBinders {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hexc : FrozenBrownianOutwardExcursionAtExit) (hcone : FrozenConeScalingLaw 𝒮) :
    ConvergenceDivisibleStmt 𝒮 :=
  firstPass_4_1_coneLaw_h35c hC.mepsScaling hC.degreeMeasureConvergence
    (closed_3_4 ν hC (volumeGrowthStmt_of_berestyckiGwynne hBG)) hC.greenKernelUpperBound
    hC.cellSizeEstimate (closed_3_5 ν hC (volumeGrowthStmt_of_berestyckiGwynne hBG) hexc)
    hC.exitTimeUpperBound (volumeGrowthStmt_of_berestyckiGwynne hBG)
    hC.frozenDiscreteHolderContinuityCorrected hcone

/-- **Lemma 5.3 (mean value inequality), counted form with its own binders.** `firstPass_5_3_final` with the binder
`hLs` supplied by `coneScaleInvarianceCoded_ownBinders`, the Draft binders `h44`, `h213`, `h41`, `h33`, `h218`, `h217`
supplied as in the module documentation, and the remaining binders the paper steps `hcan`, `hcl`, the Step `hND`, the Frozen inputs, and the Frozen binders `hexc` and `hcone`. -/
theorem closed_5_3_ownBinders {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hND : LQGMeasureNonDyadicDilationPart) (hcan : ConeCanonicalHalfBallStep)
    (hcl : ConeHalfBallClosureInsideStep) (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep) (hF : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (hF3 : FrozenDiskGreenNonnegCont)
    (hG : FrozenGreenDiscPole) (hmin : FPStrongMinimumPrinciple) (hscale : QuantumConeScalingInput)
    (hfirst : FPFirstHitVisits 𝒮) (hM : MepsScalingInput 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) (hcone : FrozenConeScalingLaw 𝒮) :
    MeanValueInequalityStmt 𝒮 :=
  firstPass_5_3_final hF hF1 hF3 hG hmin
    (coneScaleInvarianceCoded_ownBinders hBG hND hscale hcan hcl hE1 hE2) hscale hfirst hM
    closed_4_4 closed_2_13_cellRewire (firstPass_4_1_coneLaw_ownBinders ν hC hBG hexc hcone)
    (closed_3_3_ownBinders 𝒮 ν hC hBG) hC.exitTimeUpperBound (firstPass_2_17_ownBinders hBG)

/-- **Lemma 5.3 (mean value inequality), counted form with the discharged binders removed.** This is
`closed_5_3_ownBinders` with the following binders given by committed proofs.
* `hcan`, `hcl` (Step binders) by `MatedCRT.FirstPassClosure.coneCanonicalHalfBallStep_proof` and
  `MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof` (Closure/Steps42.lean:40, :106); the strong
  compatibility input `hSC` of both is `frozenClusterStrongCompatibility_of_volumeGrowth hI2` (Closure/HSCDerived.lean:19).
* `hM`, `hcone` (the Lemma 4.1 cone-scaling input) by the projections `hC.mepsScaling` and `hC.frozenConeScaling` of the
  certified reference model.
* `hF`, `hmin`, `hF1`, `hG`, `hexc` (Frozen binders with unconditional committed proofs): `frozenLQGMeasureFieldMeasurable_holds` (LPBridge/InRepoProofs.lean:35), `fpStrongMinimumPrinciple_holds`
  (LPBridge/MinimumPrinciples.lean:30), `frozenUniversalMeasurabilityOfAnalytic_holds` (LPBridge/UniversalMeasurability.lean:18),
  `MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb` (HBRewire.lean:40), `frozenBrownianOutwardExcursionAtExit_holds`
  (LPBridge/BrownianOutwardExcursion.lean:113).

Remaining binders, by class. Core: `hC`. Data: `𝒮`, `ν`. Step: `hND`. Frozen: `hBG`, `hE1`, `hE2`,
`hF3`, `hfirst`, and the inputs of the two Steps42 proofs: `hstd`, `hCentre`, `hconf`, `hK`, `hE`, `hFL`.
HB (Harmonic-Balls Draft statements, class HB): `hOpen`, `hSup`, `hCons`, `hMono`, `hCompat`, `hBdry`, `hExist`, `hThm11`,
`hProp56`, `hloc`, `hI2`. External: `hscale`. -/
theorem closed_5_3_clean {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hstd : FrozenConeLogLocalCodeLawStd) (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0}) (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule) (hloc : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) (hFL : FPConeWholePlaneFieldLaw)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hscale : QuantumConeScalingInput) (hfirst : FPFirstHitVisits 𝒮) :
    MeanValueInequalityStmt 𝒮 :=
  have hcan : ConeCanonicalHalfBallStep :=
    MatedCRT.FirstPassClosure.coneCanonicalHalfBallStep_proof hstd hCentre hOpen hSup hCons hMono hCompat hBdry
      hExist hThm11 hProp56 hconf hI2 hK hloc (frozenClusterStrongCompatibility_of_volumeGrowth hI2) hE hFL hBG
  have hcl : ConeHalfBallClosureInsideStep :=
    MatedCRT.FirstPassClosure.coneHalfBallClosureInsideStep_proof hI2 hK hloc hExist hE hFL hBG
  firstPass_5_3_final (frozenLQGMeasureFieldMeasurable_holds 𝒮) frozenUniversalMeasurabilityOfAnalytic_holds hF3 HBRewire.FrozenGreenDiscPole_of_hb
    fpStrongMinimumPrinciple_holds (coneScaleInvarianceCoded_ownBinders hBG hND hscale hcan hcl hE1 hE2) hscale hfirst
    hC.mepsScaling closed_4_4 closed_2_13_cellRewire
    (firstPass_4_1_coneLaw_ownBinders ν hC hBG frozenBrownianOutwardExcursionAtExit_holds hC.frozenConeScaling)
    (closed_3_3_ownBinders 𝒮 ν hC hBG) hC.exitTimeUpperBound (firstPass_2_17_ownBinders hBG)

end MatedCRT
