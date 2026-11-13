import MatedCRT.FirstPass.Closure.Chain42ConeLaw
import MatedCRT.FirstPass.Closure.Clean51And54
import MatedCRT.FirstPass.Closure.HLsRewire53
import MatedCRT.FirstPass.HBRewire
import MatedCRT.FirstPass.LPBridge.PunctureConnected
import MatedCRT.FirstPass.LPBridge.MinimumPrinciples
import MatedCRT.FirstPass.LPBridge.InRepoProofs
import MatedCRT.FirstPass.LPBridge.FiniteMeasureStandardBorel
import MatedCRT.FirstPass.LPBridge.UniversalMeasurability
import MatedCRT.FirstPass.LPBridge.BrownianOutwardExcursion
import MatedCRT.FirstPass.LPBridge.LQGTestIntegralMeasurable
import MatedCRT.FirstPass.LPBridge.PairingLawIG4

/-!
# Proposition 4.2, Proposition 5.1, Lemma 5.3 and Lemma 5.4 with the LP-bridge binders discharged

Each theorem `closed_X_lp` has the conclusion of its counted form `closed_X_clean` and the binders of that form
that have a committed concluder in `MatedCRT/FirstPass/LPBridge` or `MatedCRT/FirstPass/HBRewire.lean` removed.
The removed binder is supplied by that concluder, whose type is the binder's type exactly; no other binder is
changed, and no binder is supplied by a named hypothesis.

* `closed_4_2_lp` (`closed_4_2_clean`, `MatedCRT/FirstPass/Closure/Chain42ConeLaw.lean:116`): five binders
  removed: `hG` by `HBRewire.GreenFunctionBallStmt_of_hb`, `hpc` by `frozenPunctureConnected_holds`,
  `hsmp` by `fpStrongMinimumPrinciple_holds`, `hwmp` by `frozenSuperharmonicMinimumPrinciple_holds`,
  `hpole` by `HBRewire.FrozenGreenDiscPole_of_hb`.
* `closed_5_1_lp` (`closed_5_1_clean`, `MatedCRT/FirstPass/Closure/Clean51And54.lean:40`): nine binders
  removed: `hμae` by `frozenLQGMeasureFieldMeasurable_holds`, `hSB` by `frozenFiniteMeasureDiskStandardBorel_holds`,
  `hU` by `frozenUniversalMeasurabilityOfAnalytic_holds`, `hexc` by `frozenBrownianOutwardExcursionAtExit_holds`,
  `hG` by `HBRewire.FrozenGreenDiscPole_of_hb`, `hLoc` by `fpLQGMeasureLocality_holds`,
  `hpair` by `fpPairingLawIG4_holds`, `hmeasT` by `frozenLQGTestIntegralMeasurable_holds`,
  `hmin` by `frozenSuperharmonicMinimumPrinciple_holds`.
* `closed_5_3_lp` (`closed_5_3_clean`, `MatedCRT/FirstPass/Closure/HLsRewire53.lean:110`) and
  `closed_5_4_lp` (`closed_5_4_clean`, `MatedCRT/FirstPass/Closure/Clean51And54.lean:73`): no binder of the
  counted form has a committed concluder, so the binder lists are those of the counted forms.

The remaining binders are those of the counted forms, and each proof is an application of the counted form.
-/

namespace MatedCRT.FirstPassClosure

open MeasureTheory Set
open _root_.HarmonicBalls

/-- **Proposition 4.2, counted form with the LP-bridge binders discharged.** The conclusion is
`DivSandpileLowerBoundStmt 𝒮`, as for `MatedCRT.closed_4_2_clean`; the five discharged binders are
`hG`, `hpc`, `hsmp`, `hwmp`, `hpole` (see the module docstring). -/
theorem closed_4_2_lp {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮)
    (h23 : ConeHarmonicBallsStmt) (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮)
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
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    DivSandpileLowerBoundStmt 𝒮 :=
  MatedCRT.closed_4_2_clean hm h210 h34 h214 h28 h35c h218 hH hcone h23 h24c h33
    MatedCRT.HBRewire.GreenFunctionBallStmt_of_hb frozenPunctureConnected_holds fpStrongMinimumPrinciple_holds
    frozenSuperharmonicMinimumPrinciple_holds MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb
    hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hconf hI2 hK hloc hE hFL hBG
    hE1 hE2 hscale hND hrescale

/-- **Proposition 5.1, counted form with the LP-bridge binders discharged.** The conclusion is
`IDLALowerBoundStmt 𝒮`, as for `closed_5_1_clean`; the nine discharged binders are listed in the module
docstring. -/
theorem closed_5_1_lp {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
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
  closed_5_1_clean ν hC (frozenLQGMeasureFieldMeasurable_holds 𝒮) frozenFiniteMeasureDiskStandardBorel_holds hsup
    frozenUniversalMeasurabilityOfAnalytic_holds frozenBrownianOutwardExcursionAtExit_holds
    MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb hmodel hFL fpLQGMeasureLocality_holds fpPairingLawIG4_holds
    frozenLQGTestIntegralMeasurable_holds hstd frozenSuperharmonicMinimumPrinciple_holds hGBC hconf hK hE hE1 hE2
    hscale hND hcanon h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC hBG

/-- **Lemma 5.3 (mean value inequality), counted form under the LP-bridge names.** No binder of
`closed_5_3_clean` has a committed concluder, so the binder list is that of the counted form. -/
theorem closed_5_3_lp {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
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
  MatedCRT.closed_5_3_clean ν hC hBG hND hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56
    hconf hI2 hK hloc hE hFL hE1 hE2 hF3 hscale hfirst

/-- **Lemma 5.4 (L lower bound), counted form under the LP-bridge names.** No binder of `closed_5_4_clean`
has a committed concluder (`FrozenBG20GreenCrudeCanonical` is the only Frozen binder), so the binder list is
that of the counted form. -/
theorem closed_5_4_lp {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hcanon : FrozenBG20GreenCrudeCanonical 𝒮) :
    LLowerBoundStmt 𝒮 :=
  closed_5_4_clean ν hC hcanon

end MatedCRT.FirstPassClosure
