import MatedCRT.FirstPass.S1S2S8SA
import MatedCRT.FirstPass.Phase2Rewire
import MatedCRT.FirstPass.S5r.ClosureInside
import MatedCRT.FirstPass.S2g.HalfBallGate
import MatedCRT.FirstPass.S4d.Provider24
import MatedCRT.FirstPass.S4d.ScaleBridge
import MatedCRT.FirstPass.S4d.HorizonUnique
import MatedCRT.Proofs.Sec3.ConeBallMass

/-!
# Theorem 2.3 (cone harmonic balls) from literature inputs

`closed_2_3_lit` is `firstPass_2_3` (`MatedCRT/FirstPass/S1S2S8SA.lean`), which derives Theorem 2.3
(`ConeHarmonicBallsStmt`) from Lemma 2.4 (`ConeHarmonicBallsUpToFixedTimeStmt`), Lemma 2.5
(`ConeScaleInvarianceUpToFixedTimeStmt`), Lemma 2.7 (`VolumeGrowthStmt`), the quantum cone scaling input and
Lemma 2.2 (`LQGMeasurePropertiesStmt`). Each paper hypothesis is discharged by an existing theorem, recursively:

* Lemma 2.7 from the Berestycki-Gwynne cone ball mass estimate (`volumeGrowthStmt_of_berestyckiGwynne`).
* Lemma 2.4 from the provider form of the canonical half-ball family (`coneHarmonicBallsProviderFP4_of_canonical`,
  fed by `MatedCRT.Phase2.firstPass_2_4_canonical_p2`) and the closure-inside step
  (`MatedCRT.S5r.coneHalfBallClosureInsideStep_corrected`).
* Lemma 2.5 from the canonical half-ball step (`coneCanonicalHalfBallStep_of_draft`), the closure-inside step, the
  canonical scale-invariance step (`MatedCRT.Phase2.firstPass_2_5_canonical_p2`) and the horizon uniqueness of the
  rescaled half-balls (`coneRescaledHalfBallHorizonUnique_fp`).

The binders of `closed_2_3_lit` are literature inputs only: Frozen statements (`MatedCRT/FirstPass/Frozen/*`), a
Proposed statement (`MatedCRT/Proposed/*`, through the frozen alias `FrozenBerestyckiGwynneConeBallMass`), External
statements, and the Draft statements of Harmonic Balls cited in the paper. The binder `h22` (Lemma 2.2) is kept until
the corresponding closure is available.
-/

namespace MatedCRT
open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls

/-- **Theorem 2.3 (cone harmonic balls) from literature inputs.** The conclusion is `ConeHarmonicBallsStmt`, as for
`firstPass_2_3`. The hypotheses of `firstPass_2_3` other than `hscale` and `h22` are discharged by the existing
theorems listed in the module docstring; the Lemma 2.7 hypothesis is discharged from `hBG`. -/
theorem closed_2_3_lit
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdryHB : ClusterBoundaryMeasureZeroStmt.{0})
    (hExistHB : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56HB : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2HB : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hlocHB : HarmonicBallLocalSetStmt.{0})
    (hSCHB : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGB : HarmonicBalls.GreenFunctionBallStmt)
    (hpole : FrozenGreenDiscPole)
    (hrescale : ConeRescaledMeasureIsConeFieldInput) :
    ConeHarmonicBallsStmt := by
  have hVG : VolumeGrowthStmt := volumeGrowthStmt_of_berestyckiGwynne hBG
  have hcan : ConeCanonicalHalfBallStep :=
    coneCanonicalHalfBallStep_of_draft hU hmeasT hstd hmin hGBC hGB hpole h32 hSup hCons hMono hCompat hBdryHB
      hExistHB hThm11 hProp56HB hconf
  have hcl : ConeHalfBallClosureInsideStep :=
    MatedCRT.S5r.coneHalfBallClosureInsideStep_corrected hI2HB hK hlocHB hExistHB hSCHB hVG hE hFL
  have hc24 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
    MatedCRT.Phase2.firstPass_2_4_canonical_p2 hstd hGBC h32 hSup hCons hMono hCompat hBdryHB hExistHB hThm11
      hProp56HB hconf hI2HB hK hlocHB hSCHB hE hFL hVG
  have h24 : ConeHarmonicBallsUpToFixedTimeStmt :=
    coneHarmonicBallsUpToFixedTimeStmt_of_provider (coneHarmonicBallsProviderFP4_of_canonical hc24) hcl
  have hc25 : ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
    MatedCRT.Phase2.firstPass_2_5_canonical_p2 hstd hGBC h32 hSup hCons hMono hCompat hBdryHB hExistHB hThm11
      hProp56HB hconf hI2HB hK hlocHB hSCHB hE hFL hVG hE1 hE2 hscale h22
  have h25 : ConeScaleInvarianceUpToFixedTimeStmt :=
    coneScaleInvarianceUpToFixedTimeStmt_of_canonical hcan hcl hc25
      (coneRescaledHalfBallHorizonUnique_fp hcan hcl hrescale)
  exact firstPass_2_3 h24 h25 hVG hscale h22

end MatedCRT
