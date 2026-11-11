import MatedCRT.FirstPass.Closure.Clean81Full
import MatedCRT.FirstPass.HBRewire
import MatedCRT.FirstPass.LPBridge.InRepoProofs
import MatedCRT.FirstPass.LPBridge.MinimumPrinciples
import MatedCRT.FirstPass.LPBridge.UniversalMeasurability
import MatedCRT.FirstPass.LPBridge.LQGTestIntegralMeasurable
import MatedCRT.FirstPass.LPBridge.BrownianOutwardExcursion
import MatedCRT.FirstPass.LPBridge.FiniteMeasureStandardBorel
import MatedCRT.FirstPass.LPBridge.PunctureConnected
import MatedCRT.FirstPass.LPBridge.PairingLawIG4
import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestrictionFinal

/-!
# Proposition 8.1 with the LP-bridge binders discharged

`closed_8_1_lp` is `closed_8_1_full` (FirstPass/Closure/Clean81Full.lean:19) with every binder whose Prop has a committed
concluder of the same type discharged:

* `hsmp` `FPStrongMinimumPrinciple` by `fpStrongMinimumPrinciple_holds` (LPBridge/MinimumPrinciples.lean:30);
* `hmin` `FrozenSuperharmonicMinimumPrinciple` by `frozenSuperharmonicMinimumPrinciple_holds` (LPBridge/MinimumPrinciples.lean:22);
* `hU` `FrozenUniversalMeasurabilityOfAnalytic` by `frozenUniversalMeasurabilityOfAnalytic_holds` (LPBridge/UniversalMeasurability.lean:18);
* `hmeasT` `FrozenLQGTestIntegralMeasurable` by `frozenLQGTestIntegralMeasurable_holds` (LPBridge/LQGTestIntegralMeasurable.lean:49);
* `hexc` `FrozenBrownianOutwardExcursionAtExit` by `frozenBrownianOutwardExcursionAtExit_holds` (LPBridge/BrownianOutwardExcursion.lean:113);
* `hμae` `FrozenLQGMeasureFieldMeasurable 𝒮` by `frozenLQGMeasureFieldMeasurable_holds 𝒮` (LPBridge/InRepoProofs.lean:35);
* `hLoc` `FPLQGMeasureLocality` by `fpLQGMeasureLocality_holds` (LPBridge/InRepoProofs.lean:45);
* `hSB` `FrozenFiniteMeasureDiskStandardBorel` by `frozenFiniteMeasureDiskStandardBorel_holds` (LPBridge/FiniteMeasureStandardBorel.lean:18);
* `hpc` `FrozenPunctureConnected` by `frozenPunctureConnected_holds` (LPBridge/PunctureConnected.lean:15);
* `hpair` `FPPairingLawIG4` by `fpPairingLawIG4_holds` (LPBridge/PairingLawIG4.lean:81);
* `hR` `FPConeMeanZeroRestriction` by `MatedCRT.ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds` (LPBridge/ConeMeanZeroRestrictionFinal.lean:144);
* `hpole` `FrozenGreenDiscPole` by `HBRewire.FrozenGreenDiscPole_of_hb` (FirstPass/HBRewire.lean:40);
* `hG` `HarmonicBalls.GreenFunctionBallStmt` by `HBRewire.GreenFunctionBallStmt_of_hb` (FirstPass/HBRewire.lean:33).

The other binders are those of `closed_8_1_full`, with the same names and types.
-/

namespace MatedCRT

open MeasureTheory Set
open _root_.HarmonicBalls

/-- **Proposition 8.1 with the LP-bridge binders discharged.** Same conclusion as `closed_8_1_full`:
`IDLAConstrainedConvergenceStmt 𝒮`. -/
theorem closed_8_1_lp {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
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
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hmodel : FPWholePlaneLQGModel)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{0}) (h82 : TypicalPointManyGoodScalesStmt.{0})
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) :
    IDLAConstrainedConvergenceStmt 𝒮 :=
  closed_8_1_full ν hC hm h210 h34 h214 h28 h35c h218 hH hcone h23 h24c h33
    HBRewire.GreenFunctionBallStmt_of_hb frozenPunctureConnected_holds fpStrongMinimumPrinciple_holds
    frozenSuperharmonicMinimumPrinciple_holds HBRewire.FrozenGreenDiscPole_of_hb hstd hCentre hOpen hSup hCons hMono
    hCompat hBdry hExist hThm11 hProp56 hconf hI2 hK hloc hE hFL hBG hE1 hE2 hscale hND hrescale
    (frozenLQGMeasureFieldMeasurable_holds 𝒮) frozenFiniteMeasureDiskStandardBorel_holds hsup
    frozenUniversalMeasurabilityOfAnalytic_holds frozenBrownianOutwardExcursionAtExit_holds hmodel
    fpLQGMeasureLocality_holds fpPairingLawIG4_holds frozenLQGTestIntegralMeasurable_holds hcanon h611 h82 h0 h2 hV
    ConeMeanZeroRestriction.fpConeMeanZeroRestriction_holds

end MatedCRT
