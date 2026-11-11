import MatedCRT.FirstPass.S5S6S7
import MatedCRT.FirstPass.Closure.HSCRewire
import MatedCRT.FirstPass.Closure.HLsRewire53
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.SLERef.Certified
import MatedCRT.Proofs.Sec3.ConeBallMass

/-!
# Proposition 7.1 (divisible sandpile upper bound), counted form without Draft binders

`closed_7_1_clean` is `firstPass_7_1` (FirstPass/S5S6S7.lean:98) with each Draft binder discharged by a committed
counted form. The conclusion is the Draft statement `DivSandpileUpperBoundStmt 𝒮` (prop:div-sandpile-upper-bound),
unchanged.

Discharges (Draft binder of `firstPass_7_1` ← committed form):
* `hcone : ConeHarmonicBallsStmt` (Theorem 2.3, cone harmonic balls) ← `closed_2_3_lit_noSC`
  (FirstPass/Closure/HSCRewire.lean). This binder is the cone harmonic-balls statement, not the retired
  `FrozenConeEnvironmentScaling`, so it is not replaced by `FrozenConeScalingLaw`.
* `h216 : GreenKernelLowerBoundStmt 𝒮` (Lemma 2.16) ← `CertifiedReferenceModel.greenKernelLowerBound`.
* `h27 : VolumeGrowthStmt` (Lemma 2.7, Berestycki-Gwynne, BG20 Lemma A.1) ← `volumeGrowthStmt_of_berestyckiGwynne hBG`.
* `h28 : CellSizeEstimateStmt 𝒮` (Lemma 2.8, BG20 Lemma 2.4) ← `CertifiedReferenceModel.cellSizeEstimate`.
* `h29 : CountingMeasureConvergenceStmt 𝒮` (Lemma 2.9, BG20 Lemma A.4) ← `CertifiedReferenceModel.countingMeasureConvergence`.
* `h218 : ExitTimeUpperBoundStmt 𝒮` (Lemma 2.18, BG20 Proposition 5.1) ← `CertifiedReferenceModel.exitTimeUpperBound`.
* `hconv : ConvergenceDivisibleStmt 𝒮` (Lemma 4.1) ← `firstPass_4_1_coneLaw_ownBinders` (FirstPass/Closure/HLsRewire53.lean),
  with the corrected Lemma 3.5 supplied by `closed_3_5` and the frozen cone-scaling law by
  `CertifiedReferenceModel.frozenConeScaling`.
* `hgreen : UniformConvergenceGreenKernelStmt 𝒮` (Lemma 3.3, uniform convergence of the rescaled Green kernel)
  ← `closed_3_3_ownBinders` (FirstPass/Closure/OwnBinderRewire.lean).

The External binders `hscale : MepsScalingInput 𝒮` and `hdeg : DegreeBoundInput 𝒮` of `firstPass_7_1` are the fields
`mepsScaling` and `degreeBound` of the certified reference model `hC`.
-/

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- **Proposition 7.1** (prop:div-sandpile-upper-bound), counted form without Draft binders. The binders that remain
are the certified reference model `hC` (core), the Frozen inputs `hBG`, `hexc`, `h0`, `h2`, `hV`, `hR`, and the
binders of `closed_2_3_lit_noSC` (the literature inputs of Theorem 2.3, with their Frozen, Step and External classes). -/
theorem closed_7_1_clean
    (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (hBG : FrozenBerestyckiGwynneConeBallMass) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction)
    (hscale : QuantumConeScalingInput) (hND : LQGMeasureNonDyadicDilationPart)
    (hstd : FrozenConeLogLocalCodeLawStd) (hGBC : FrozenGreenBallCentre)
    (h32 : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0}) (hconf : FrozenHBInitialConfinement)
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0}) (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw) (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole) (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    DivSandpileUpperBoundStmt 𝒮 :=
  firstPass_7_1 𝒮 hC.mepsScaling
    (closed_2_3_lit_noSC hBG hscale hND hstd hGBC h32 hSup hCons hMono hCompat hBdryHB hExistHB hThm11
      hProp56HB hconf hI2HB hK hlocHB hE hFL hE1 hE2 hU hmeasT hmin hGB hpole hrescale)
    hC.degreeBound hC.greenKernelLowerBound (volumeGrowthStmt_of_berestyckiGwynne hBG)
    hC.cellSizeEstimate hC.countingMeasureConvergence hC.exitTimeUpperBound
    (firstPass_4_1_coneLaw_ownBinders ν hC hBG hexc hC.frozenConeScaling)
    (closed_3_3_ownBinders 𝒮 ν hC hBG) h0 h2 hV hR

end MatedCRT
