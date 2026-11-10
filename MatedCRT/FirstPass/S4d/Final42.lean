import MatedCRT.FirstPass.S4d
import MatedCRT.FirstPass.S2g.Assembly2456
import MatedCRT.FirstPass.S2g.Draft24
import MatedCRT.FirstPass.S2m
import MatedCRT.FirstPass.Frozen.S4S5b
import MatedCRT.FirstPass.S4d.ScaleBridge

/-!
# FIRST PASS, Proposition 4.2 (prop:div-sandpile-lower-bound): the assembly with no open cone step (q4)

Task fp-S4d-4-2-assembly. `firstPass_4_2_of_halfball_gate` (`FirstPass/S4d.lean`) takes the NEW steps as explicit
hypotheses. Here they are supplied by proofs, except one:

* `hcl` := `coneHalfBallClosureInsideStep_corrected` (`FirstPass/S2g/Corrected24.lean`, route B, q1), with the
  whole-plane field law `FPConeWholePlaneFieldLaw` (`Frozen/S4S5b.lean`) and the frozen existence insertion
  `FrozenLQGMeasureExistenceInsertion` (`Frozen/S2m.lean`).
* `hScaleInv` (Draft Lemma 2.6) := `firstPass_2_6_corrected` (`FirstPass/S2g/Assembly2456.lean`, q1), same inputs.
* `h24` (Draft Lemma 2.4) := `coneHarmonicBallsUpToFixedTimeStmt_of_canonical` (`FirstPass/S2g/Draft24.lean`, q1).
* `h25` (Draft Lemma 2.5) := `coneScaleInvarianceUpToFixedTimeStmt_of_canonical` (`FirstPass/S4d/ScaleBridge.lean`, q4),
  from the canonical form `firstPass_2_5_corrected` (`Assembly2456.lean`) and the explicit step `hRU`.

The remaining explicit NEW input is `hRU : ConeRescaledHalfBallHorizonUniqueFPStep` (`FirstPass/S4d/ScaleBridge.lean`, a
copy of `ConeRescaledHalfBallHorizonUniqueStep`, `Proofs/Sec2/ConeFamilyMeasurable/ScaledUniqueness.lean`; OPEN). The remaining hypotheses are Draft statements, frozen or external inputs, and the cone
externals `hE1`, `hE2`.
-/

namespace MatedCRT

open _root_.HarmonicBalls in
/-- **Proposition 4.2 (`DivSandpileLowerBoundStmt`), assembled (q4, fp-S4d-4-2-assembly).**
Compared with `firstPass_4_2_of_halfball_gate`, the closure step `hcl`, Lemma 2.6 `hScaleInv`, Draft Lemma 2.4 `h24` and
Draft Lemma 2.5 `h25` are no longer hypotheses. `h25` is derived from the canonical form of Lemma 2.5
(`firstPass_2_5_corrected`) by `coneScaleInvarianceUpToFixedTimeStmt_of_canonical`, which takes the rescaled horizon
uniqueness `hRU` as its only extra input. The statement of Proposition 4.2 is unchanged. -/
theorem firstPass_4_2_of_wholeplane_model {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (hRU : ConeRescaledHalfBallHorizonUniqueFPStep) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
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
  exact firstPass_4_2_of_halfball_gate hm h210 h34 h214 h28 h35 h218 h27 hH hcone h23 h24
    h25 h33 hG hpc hsmp hwmp hpole
    (firstPass_2_6_corrected hU hmeasT hstd hwmp hCentre hG hpole hOpen hSup hCons hMono hCompat hBdry hExist hThm11
      hProp56 hconf hI2 hK hloc hSC
      hE hFL h27 hE1 hE2 hscale h22)
    hU hmeasT hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hconf
    hcl
    hE1 hE2 hscale h22

end MatedCRT
