import MatedCRT.FirstPass.Closure.Clean51And54
import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.Closure.HSCDerived
import MatedCRT.FirstPass.Closure.Chain42ConeLaw
import MatedCRT.FirstPass.S2g.Assembly2456
import MatedCRT.FirstPass.S1S2S8SA
import MatedCRT.Proofs.Sec3.ConeBallMass

/-!
# Propositions 6.1 and 8.1 with the Draft binders discharged (task p2-clean-6-1-then-8-1)

* `closed_6_1_clean` is `firstPass_6_1_corrected` (`S2g/Assembly2456.lean:31`) with
  - `h610`: the own-binder form `closed_6_10_ownBinders` (Lemma 6.10, `Closure/OwnBinderRewire.lean:123`);
  - `h51`: the clean form `closed_5_1_clean` (Proposition 5.1, `Closure/Clean51And54.lean:40`);
  - `h27`: `volumeGrowthStmt_of_berestyckiGwynne hBG` (Lemma 2.7, `Proofs/Sec3/ConeBallMass.lean:17`);
  - `hSC`: `frozenClusterStrongCompatibility_of_volumeGrowth hI2` (Lemma 5.8, `Closure/HSCDerived.lean:19`).
* `closed_8_1_clean` is `firstPass_8_1` (`S1S2S8SA.lean:65`) with `h42 := closed_4_2_clean`
  (`Closure/Chain42ConeLaw.lean`), `h51 := closed_5_1_clean`, `h61 := closed_6_1_clean`, and `h71`
  (Proposition 7.1, `DivSandpileUpperBoundStmt 𝒮`) kept as a binder until the clean form `closed_7_1_clean` is committed.

Binders with the same Prop type are merged into one name. -/

open MeasureTheory Set
open _root_.HarmonicBalls

namespace MatedCRT

/-- **Proposition 6.1, clean form.** The upper bound `IDLAUpperBoundStmt 𝒮` from `firstPass_6_1_corrected`, with its
Draft binders `h610`, `h51`, `h27` and the cluster strong compatibility `hSC` derived from `hI2`. The remaining
binders are the Frozen, External, Step and core inputs of the own-binder forms. -/
theorem closed_6_1_clean {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hpole : FrozenGreenDiscPole) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hCentre : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (hND : LQGMeasureNonDyadicDilationPart)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0}) (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0}) (hExist : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0}) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction)
    (hGB : _root_.HarmonicBalls.GreenFunctionBallStmt) :
    IDLAUpperBoundStmt 𝒮 :=
  firstPass_6_1_corrected 𝒮 (closed_6_10_ownBinders 𝒮 ν hC hBG h0 h2 hV hR)
    (MatedCRT.FirstPassClosure.closed_5_1_clean ν hC hμae hSB hsup hU hexc hpole hmodel hFL hLoc hpair hmeasT hstd
      hmin hCentre hconf hK hE hE1 hE2 hscale hND hcanon hOpen h611 h82 hI2 hSup hCons hMono hCompat hBdry hExist
      hThm11 hProp56 hloc (frozenClusterStrongCompatibility_of_volumeGrowth hI2) hBG)
    hU hmeasT hstd hmin hCentre hGB hpole hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hconf hI2 hK hloc
    (frozenClusterStrongCompatibility_of_volumeGrowth hI2) hE hFL (volumeGrowthStmt_of_berestyckiGwynne hBG)

#print axioms closed_6_1_clean

/-- **Proposition 8.1, clean form.** The constrained convergence `IDLAConstrainedConvergenceStmt 𝒮` from
`firstPass_8_1`, with `h42 := closed_4_2_clean`, `h51 := closed_5_1_clean`, `h61 := closed_6_1_clean`; the
binder `h71` (Proposition 7.1) is kept until `closed_7_1_clean` is committed. -/
theorem closed_8_1_clean {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    -- inputs of `closed_4_2_clean`, in its order
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (hG : _root_.HarmonicBalls.GreenFunctionBallStmt) (hpc : FrozenPunctureConnected)
    (hsmp : FPStrongMinimumPrinciple) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hpole : FrozenGreenDiscPole)
    (hstd : FrozenConeLogLocalCodeLawStd) (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0}) (hconf : FrozenHBInitialConfinement)
    (hI2 : FrozenLQGVolumeGrowthAllScales)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (hND : LQGMeasureNonDyadicDilationPart)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    -- further inputs of `closed_5_1_clean` and `closed_6_1_clean`
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hmodel : FPWholePlaneLQGModel) (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4)
    (hmeasT : FrozenLQGTestIntegralMeasurable) (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{0}) (h82 : TypicalPointManyGoodScalesStmt.{0})
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction)
    -- Proposition 7.1 (Draft binder, pending `closed_7_1_clean`)
    (h71 : DivSandpileUpperBoundStmt 𝒮) :
    IDLAConstrainedConvergenceStmt 𝒮 :=
  firstPass_8_1 (𝒮 := 𝒮)
    (closed_4_2_clean hm h210 h34 h214 h28 h35c h218 hH hcone h23 h24c h33 hG hpc hsmp hmin hpole hstd hCentre hOpen
      hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hconf hI2 hK hloc hE hFL hBG hE1 hE2 hscale hND hrescale)
    (MatedCRT.FirstPassClosure.closed_5_1_clean ν hC hμae hSB hsup hU hexc hpole hmodel hFL hLoc hpair hmeasT hstd
      hmin hCentre hconf hK hE hE1 hE2 hscale hND hcanon hOpen h611 h82 hI2 hSup hCons hMono hCompat hBdry hExist
      hThm11 hProp56 hloc (frozenClusterStrongCompatibility_of_volumeGrowth hI2) hBG)
    (closed_6_1_clean ν hC hμae hSB hsup hU hexc hpole hmodel hFL hLoc hpair hmeasT hstd hmin hCentre hconf hK hE hE1
      hE2 hscale hND hcanon hOpen h611 h82 hI2 hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hloc hBG h0 h2 hV
      hR hG)
    h71

#print axioms closed_8_1_clean

end MatedCRT
