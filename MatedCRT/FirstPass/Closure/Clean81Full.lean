import MatedCRT.FirstPass.Closure.Clean61And81
import MatedCRT.FirstPass.Closure.Clean71

/-!
# Proposition 8.1, full form with no DRAFT binder (task p2-clean-8-1-full-and-3-6-hBE)

`closed_8_1_full` is `closed_8_1_clean` (Closure/Clean61And81.lean:68) with its Draft binder `h71`
(Proposition 7.1, `DivSandpileUpperBoundStmt 𝒮`) discharged by `closed_7_1_clean` (Closure/Clean71.lean:42).
Every binder of `closed_7_1_clean` already occurs in `closed_8_1_clean` with the same name and type, so the binder
list of `closed_8_1_full` is that of `closed_8_1_clean` without `h71`. -/

open MeasureTheory Set
open _root_.HarmonicBalls

namespace MatedCRT

/-- **Proposition 8.1, full form.** The constrained convergence `IDLAConstrainedConvergenceStmt 𝒮` from the clean form
`closed_8_1_clean` with `h71` supplied by `closed_7_1_clean`. -/
theorem closed_8_1_full {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
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
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hmodel : FPWholePlaneLQGModel) (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4)
    (hmeasT : FrozenLQGTestIntegralMeasurable) (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{0}) (h82 : TypicalPointManyGoodScalesStmt.{0})
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) :
    IDLAConstrainedConvergenceStmt 𝒮 :=
  closed_8_1_clean ν hC hm h210 h34 h214 h28 h35c h218 hH hcone h23 h24c h33 hG hpc hsmp hmin hpole hstd hCentre hOpen
    hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hconf hI2 hK hloc hE hFL hBG hE1 hE2 hscale hND hrescale hμae
    hSB hsup hU hexc hmodel hLoc hpair hmeasT hcanon h611 h82 h0 h2 hV hR
    (closed_7_1_clean 𝒮 ν hC hBG hexc h0 h2 hV hR hscale hND hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist
      hThm11 hProp56 hconf hI2 hK hloc hE hFL hE1 hE2 hU hmeasT hmin hG hpole hrescale)

#print axioms closed_8_1_full

end MatedCRT
