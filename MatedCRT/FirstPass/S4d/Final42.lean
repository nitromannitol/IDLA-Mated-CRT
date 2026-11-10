import MatedCRT.FirstPass.S4d
import MatedCRT.FirstPass.S2g.Assembly2456
import MatedCRT.FirstPass.S2g.Draft24
import MatedCRT.FirstPass.S2m
import MatedCRT.FirstPass.Frozen.S4S5b

/-!
# FIRST PASS, Proposition 4.2 (prop:div-sandpile-lower-bound): the assembly with no open cone step (q4)

Task fp-S4d-4-2-assembly, round 12. `firstPass_4_2_of_halfball_gate` (`FirstPass/S4d.lean`) still takes two NEW steps as
explicit hypotheses: `hcl : ConeHalfBallClosureInsideStep` and `hScaleInv : ConeScaleInvarianceStmt` (Lemma 2.6). Both are
now supplied by proofs. Both take the frozen existence insertion `FrozenLQGMeasureExistenceInsertion`
(`Frozen/S2m.lean`), from which z8's `firstPass_wholePlaneLQGModel_of_existence` (`FirstPass/S2m.lean`) gives the
whole-plane model `WholePlaneLQGModelStep`; the q1 theorems (commit 7a2a48b) use it internally:

* `hcl` := `coneHalfBallClosureInsideStep_corrected` (`FirstPass/S2g/Corrected24.lean`, route B, q1), with the
  whole-plane field law `FPConeWholePlaneFieldLaw` (`Frozen/S4S5b.lean`, frozen by the operator decision of 02:03 UTC).
* `hScaleInv` := `firstPass_2_6_corrected` (`FirstPass/S2g/Assembly2456.lean`, q1), with the same inputs.

The remaining hypotheses are Draft statements, frozen or external inputs, and the cone externals `hE1`, `hE2`.
-/

namespace MatedCRT

open _root_.HarmonicBalls in
/-- **Proposition 4.2 (`DivSandpileLowerBoundStmt`), fully assembled (q4, fp-S4d-4-2-assembly).**
Compared with `firstPass_4_2_of_halfball_gate`, the closure step `hcl`, Lemma 2.6 `hScaleInv` and Draft Lemma 2.4 `h24`
(`coneHarmonicBallsUpToFixedTimeStmt_of_canonical`, `FirstPass/S2g/Draft24.lean`, q1) are no longer hypotheses; the
hypothesis `h25` (Draft Lemma 2.5) stays explicit, since its canonical form `ConeScaleInvarianceUpToFixedTimeCanonicalStmt`
(`Assembly2456.lean:73`) has no bridge to the Draft statement in the repository. The statement of Proposition 4.2 is unchanged. -/
theorem firstPass_4_2_of_wholeplane_model {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮)
    (h34 : IntegralConvergenceGreenFunctionStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeEnvironmentScaling 𝒮)
    (h23 : ConeHarmonicBallsStmt)
    (h25 : ConeScaleInvarianceUpToFixedTimeStmt) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
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
  firstPass_4_2_of_halfball_gate hm h210 h34 h214 h28 h35 h218 h27 hH hcone h23
    (coneHarmonicBallsUpToFixedTimeStmt_of_canonical
      (coneCanonicalHalfBallStep_of_draft hU hmeasT hstd hwmp hCentre hG hpole hOpen hSup hCons hMono hCompat hBdry
        hExist hThm11 hProp56 hconf)
      (coneHalfBallClosureInsideStep_corrected hI2 hK hloc hExist hSC h27 hE hFL))
    h25 h33 hG hpc hsmp hwmp hpole
    (firstPass_2_6_corrected hU hmeasT hstd hwmp hCentre hG hpole hOpen hSup hCons hMono hCompat hBdry hExist hThm11
      hProp56 hconf hI2 hK hloc hSC
      hE hFL h27 hE1 hE2 hscale h22)
    hU hmeasT hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hconf
    (coneHalfBallClosureInsideStep_corrected hI2 hK hloc hExist hSC h27 hE hFL)
    hE1 hE2 hscale h22

end MatedCRT
