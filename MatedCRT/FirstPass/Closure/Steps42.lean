import MatedCRT.FirstPass.Closure.OwnBinderRewire
import MatedCRT.FirstPass.S4d.FixedTimeFinal
import MatedCRT.FirstPass.S4d.Provider24
import MatedCRT.FirstPass.S4d.ScaleBridge
import MatedCRT.FirstPass.S4d.HorizonUnique
import MatedCRT.FirstPass.S2j
import MatedCRT.FirstPass.Frozen.S4d2

/-!
# The paper-own steps of Proposition 4.2 (task p2-clean-5-1-5-4-then-steps-4-2)

The three steps of `firstPass_4_2_final` (COUNTED.md:124-126) and their status:

* `hcan` = `ConeCanonicalHalfBallStep` (FirstPass/S2g.lean:81). Written argument: printed Lemma 2.4
  (`lemma:existence-up-to-fixed-time`, paper/idla_mated_crt-corrected.tex:534-541): on a probability-one event there is a
  unique family of harmonic balls on `(0, T)`, `T = sup {t > 0 : Λ_t ⊂ B_{1/2}}`, with the existence from
  Theorems 1.1, 5.5 and Lemma 3.2 of Harmonic-Balls-LQG and the uniqueness from its Proposition 5.6 (tex:543-544).
  The canonical stopping time is `halfBallTime (μ ω)`. Proved as the projection of the counted canonical Lemma 2.4
  `firstPass_2_4_ownBinders` (OwnBinderRewire.lean:133), whose binders are Frozen and HB.
* `hnj` = `StrictGapFixedTimeUnionStep 𝒮` (FirstPass/S4d/StrictGapReduction.lean:35). Written argument: the corrected
  proof of `prop:div-sandpile-lower-bound` (tex:1919-1921, CORRECTION [C20] in docs/campaign/CORRECTIONS.md). Its Lean
  chain is `strictGapFixedTimeUnionStep_of_provider` (FirstPass/S4d/FixedTimeFinal.lean:51); the chain uses the
  Lemma 2.5 and 2.6 forms and `ConeHalfBallClosureInsideStep` (hcl). Proved here conditionally on the named hypothesis
  `hcl`; see the report for the gap in the printed sentence at tex:1920.
* `hcl` = `ConeHalfBallClosureInsideStep` (Proofs/Sec2/ConeFamilyMeasurable/StoppedClosure.lean:18): no printed
  argument (its docstring says "Not stated in the paper"). Not proved here; reported.
-/

open MeasureTheory
open _root_.HarmonicBalls

namespace MatedCRT.FirstPassClosure

/-- **`hcan` (`ConeCanonicalHalfBallStep`) from the canonical Lemma 2.4.** The witness `T` of the canonical form is
`halfBallTime (μ ω)`, and its family `Λ` is the one of `firstPass_2_4_ownBinders`; the uniqueness clause is dropped. -/
theorem coneCanonicalHalfBallStep_proof
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
    (hFL : FPConeWholePlaneFieldLaw) (hBG : FrozenBerestyckiGwynneConeBallMass) :
    ConeCanonicalHalfBallStep := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨_, Λ, _, hΛ⟩ := MatedCRT.firstPass_2_4_ownBinders hstd hCentre hOpen hSup hCons hMono hCompat hBdry
    hExist hThm11 hProp56 hconf hI2 hK hloc hSC hE hFL hBG γ hγ0 hγ2 Ω P hC hcirc μ hcone
  filter_upwards [hΛ] with ω hω
  exact ⟨Λ ω, hω.1, (hω.2.1).1, hω.2.2⟩

/-- **`hnj` (`StrictGapFixedTimeUnionStep`), CONDITIONAL on `hcl`.** The chain of `strictGapFixedTimeUnionStep_of_provider`
with its inputs derived from the counted forms: the provider of the canonical Lemma 2.4 (`hprov`), the Lemma 2.5 form
(`h25`, through `coneScaleInvarianceUpToFixedTimeStmt_of_canonical` and the Frozen rescaling input `hrescale`), the
measurability `hfam` (`coneFamilyAEMeasurable_proved`), and the Lemma 2.6 form `h26`. The closure-containment step `hcl`
is a named hypothesis: it has no written argument in the corrected paper (`ConeHalfBallClosureInsideStep`, reported). -/
theorem strictGapFixedTimeUnionStep_proof {𝒮 : SpaceFillingSLEModel}
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
    (hFL : FPConeWholePlaneFieldLaw) (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput) (hND : LQGMeasureNonDyadicDilationPart)
    (hrescale : ConeRescaledMeasureIsConeFieldInput)
    (hcl : ConeHalfBallClosureInsideStep) :
    StrictGapFixedTimeUnionStep 𝒮 := by
  have hcan : ConeCanonicalHalfBallStep :=
    coneCanonicalHalfBallStep_proof hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hconf
      hI2 hK hloc hSC hE hFL hBG
  have hc24 : ConeHarmonicBallsUpToFixedTimeCanonicalStmt :=
    MatedCRT.firstPass_2_4_ownBinders hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hconf
      hI2 hK hloc hSC hE hFL hBG
  have hprov : ConeHarmonicBallsProviderFP4 := coneHarmonicBallsProviderFP4_of_canonical hc24
  have hc25 : ConeScaleInvarianceUpToFixedTimeCanonicalStmt :=
    MatedCRT.firstPass_2_5_ownBinders hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hconf
      hI2 hK hloc hSC hE hFL hBG hE1 hE2 hscale hND
  have h25 : ConeScaleInvarianceUpToFixedTimeStmt :=
    coneScaleInvarianceUpToFixedTimeStmt_of_canonical hcan hcl hc25
      (coneRescaledHalfBallHorizonUnique_fp hcan hcl hrescale)
  have h22 : LQGMeasurePropertiesStmt := closed_2_2_ownBinders hscale hBG hND
  have h27 : VolumeGrowthStmt := volumeGrowthStmt_of_berestyckiGwynne hBG
  have hfam : ConeFamilyAEMeasurableStep := coneFamilyAEMeasurable_proved hcan hcl h27 hE1 hE2 hscale h22
  have h26 : ConeScaleInvarianceStmt :=
    MatedCRT.firstPass_2_6_ownBinders hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hconf
      hI2 hK hloc hSC hE hFL hBG hE1 hE2 hscale hND
  exact strictGapFixedTimeUnionStep_of_provider 𝒮 hprov h25 hfam h26 hscale

end MatedCRT.FirstPassClosure
