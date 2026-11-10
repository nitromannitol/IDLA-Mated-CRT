import MatedCRT.FirstPass.S4d
import MatedCRT.FirstPass.S2g.Assembly2456
import MatedCRT.FirstPass.S2g.Draft24
import MatedCRT.FirstPass.S2m
import MatedCRT.FirstPass.Frozen.S4S5b
import MatedCRT.FirstPass.Frozen.S3S4b
import MatedCRT.FirstPass.S4d.ScaleBridge
import MatedCRT.FirstPass.S1S2S8SA
import MatedCRT.FirstPass.S3S4
import MatedCRT.FirstPass.S3S4c

/-!
# FIRST PASS, Proposition 4.2 (prop:div-sandpile-lower-bound): the assembly (q4, fp-S4d-4-2-assembly)

`firstPass_4_2_of_halfball_gate` (`FirstPass/S4d.lean`) takes the Draft and NEW steps as explicit hypotheses. In
`firstPass_4_2_of_wholeplane_model` they are supplied as follows.

* `hcl` := `coneHalfBallClosureInsideStep_corrected` (`FirstPass/S2g/Corrected24.lean`, route B, q1), with the
  whole-plane field law `FPConeWholePlaneFieldLaw` (`Frozen/S4S5b.lean`) and `FrozenLQGMeasureExistenceInsertion`
  (`Frozen/S2m.lean`).
* `hScaleInv` (Draft Lemma 2.6) := `firstPass_2_6_corrected` (`FirstPass/S2g/Assembly2456.lean`, q1), same inputs.
* `h24` (Draft Lemma 2.4) := `coneHarmonicBallsUpToFixedTimeStmt_of_canonical` (`FirstPass/S2g/Draft24.lean`, q1).
* `h25` (Draft Lemma 2.5) := `coneScaleInvarianceUpToFixedTimeStmt_of_canonical` (`FirstPass/S4d/ScaleBridge.lean`, q4),
  from the canonical form `firstPass_2_5_corrected` and the explicit NEW step `hRU`.
* `h23` (Draft Lemma 2.3, `ConeHarmonicBallsStmt`) := `firstPass_2_3` (`FirstPass/S1S2S8SA.lean`) from `h24`, `h25`, `h27`,
  `hscale`, `h22`; no new hypothesis.
* `h34` (Draft Lemma 3.4, `IntegralConvergenceGreenFunctionStmt`) := `MatedCRT.S3S4c.firstPass_3_4`
  (`FirstPass/S3S4c.lean`) from `h27`, `h218`, `hm`, and the frozen inputs `hrevuz`, `hdet` (now explicit, replacing `h34`).
* `h33` (Draft Lemma 3.3, `UniformConvergenceGreenKernelStmt`) := `firstPass_3_3` (`FirstPass/S3S4.lean`) from `h210`, `h34`,
  `h214`, `h28`, `h27`, `h218`, `hm`, `hH`; no new hypothesis.

The remaining explicit NEW input is `hRU : ConeRescaledHalfBallHorizonUniqueFPStep` (`FirstPass/S4d/ScaleBridge.lean`; OPEN).
The cone externals `hE1`, `hE2` stay explicit (`FirstPass/Frozen/S2i.lean`).
-/

namespace MatedCRT

open _root_.HarmonicBalls in
/-- **Proposition 4.2 (`DivSandpileLowerBoundStmt`), assembled (q4, fp-S4d-4-2-assembly).**
The Draft hypotheses `h23`, `h33`, `h34`, `h24`, `h25` and the closure and Lemma 2.6 steps are derived in the proof (see the
module docstring); the explicit inputs are the frozen `hrevuz`, `hdet` (for `h34`), the NEW step `hRU`, and the frozen and
external hypotheses listed in the signature. The statement of Proposition 4.2 is unchanged. -/
theorem firstPass_4_2_of_wholeplane_model {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (hRU : ConeRescaledHalfBallHorizonUniqueFPStep)
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
    DivSandpileLowerBoundStmt 𝒮 := by
  have hcan := coneCanonicalHalfBallStep_of_draft hU hmeasT hstd hwmp hCentre hG hpole hOpen hSup hCons hMono hCompat
    hBdry hExist hThm11 hProp56 hconf
  have hcl := coneHalfBallClosureInsideStep_corrected hI2 hK hloc hExist hSC h27 hE hFL
  have h24 := coneHarmonicBallsUpToFixedTimeStmt_of_canonical hcan hcl
  have h25 := coneScaleInvarianceUpToFixedTimeStmt_of_canonical hcan hcl
    (firstPass_2_5_corrected hU hmeasT hstd hwmp hCentre hG hpole hOpen hSup hCons hMono hCompat hBdry hExist hThm11
      hProp56 hconf hI2 hK hloc hSC hE hFL h27 hE1 hE2 hscale h22)
    hRU
  have h23 := firstPass_2_3 h24 h25 h27 hscale h22
  have h34 := MatedCRT.S3S4c.firstPass_3_4 h27 h218 hm hrevuz hdet
  have h33 := firstPass_3_3 h210 h34 h214 h28 h27 h218 hm hH
  exact firstPass_4_2_of_halfball_gate hm h210 h34 h214 h28 h35 h218 h27 hH hcone h23 h24
    h25 h33 hG hpc hsmp hwmp hpole
    (firstPass_2_6_corrected hU hmeasT hstd hwmp hCentre hG hpole hOpen hSup hCons hMono hCompat hBdry hExist hThm11
      hProp56 hconf hI2 hK hloc hSC
      hE hFL h27 hE1 hE2 hscale h22)
    hU hmeasT hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hconf
    hcl
    hE1 hE2 hscale h22

end MatedCRT
