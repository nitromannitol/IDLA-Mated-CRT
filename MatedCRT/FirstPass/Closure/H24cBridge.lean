import MatedCRT.FirstPass.Phase2Rewire
import MatedCRT.FirstPass.Closure.CellRewire
import MatedCRT.FirstPass.Frozen.S5Cited
import MatedCRT.Proofs.Sec3.ConeBallMass

/-!
# Corrected Lemma 2.4 from its canonical form, and Proposition 5.1 with own binders (BLOCKED h24c)

## Clause-by-clause comparison (task p2-h24c-bridge-5-1)

`ConeHarmonicBallsUpToFixedTimeCorrectedStmt` (FirstPass/S2b.lean:43, the binder `h24c` of `closed_5_1`) and
`ConeHarmonicBallsUpToFixedTimeCanonicalStmt` (FirstPass/S2g.lean:37, the conclusion of the counted row 2.4,
`firstPass_2_4_canonical_p2`, FirstPass/Phase2Rewire.lean:199):

* Hypotheses `∀ γ, 0 < γ → γ < 2`, `Ω`, `P`, `hC`, `hcirc`, `μ`, `IsConeField γ P hC hcirc μ`: identical.
* Canonical only: `AEMeasurable (fun ω => halfBallTime (μ ω)) P`, and a random family `Λ : Ω → ℝ → Set ℂ` whose joint
  process `(circleProcess (hcirc ω), familyProcess (Λ ω) (halfBallTime (μ ω)))` is `AEMeasurable`. The corrected form
  has no measurability conjunct.
* Corrected: `∀ᵐ ω, ∃ T, 0 < T ∧ ∃ Λ, ...`, with `T` and `Λ` existential inside the a.s. quantifier. Canonical: `T` is
  `halfBallTime (μ ω)` and `Λ` is `Λ ω`, with `∀ᵐ ω, 0 < halfBallTime (μ ω) ∧ ...`.
* Family and uniqueness: `IsConeHarmonicBallFamilyOn (μ ω) Λ T` (corrected) is the first conjunct of
  `UniqueConeFamilyOn (μ ω) (Λ ω) T` (canonical); the clause `∀ Λ', IsConeHarmonicBallFamilyOn (μ ω) Λ' T → EqOn Λ' Λ (Ioo 0 T)`
  is the same in both.
* `IsStoppedAtHalfBall Λ T`: identical.

Hence the corrected form is the canonical form with its measurability conjuncts dropped. Neither form contains the
uniqueness of the stopping time `T' = T` of the Draft (`ConeHarmonicBallsUpToFixedTimeStmt`, Draft/Section2.lean:66); the
corrected form omits it as its docstring (S2b.lean:36-42) says.

No clause of the corrected form needs an argument outside the corrected tex, so no named hypothesis is introduced.
-/

open MeasureTheory Set Filter Topology Metric
open _root_.HarmonicBalls MatedCRT.FirstPassClosure

namespace MatedCRT

/-- Corrected Lemma 2.4 (`ConeHarmonicBallsUpToFixedTimeCorrectedStmt`) from its canonical form: take `T = halfBallTime (μ ω)`
and `Λ ω`, and drop the measurability conjuncts of the canonical form. -/
theorem coneHarmonicBallsUpToFixedTimeCorrected_of_canonical
    (h : ConeHarmonicBallsUpToFixedTimeCanonicalStmt) :
    ConeHarmonicBallsUpToFixedTimeCorrectedStmt := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨-, Λ, -, hmain⟩ := h γ hγ0 hγ2 Ω P hC hcirc μ hcone
  refine hmain.mono fun ω hω => ?_
  obtain ⟨hpos, huniq, hstop⟩ := hω
  unfold UniqueConeFamilyOn at huniq
  exact ⟨halfBallTime (μ ω), hpos, Λ ω, huniq.1, hstop, huniq.2⟩

/-- Corrected Lemma 2.4 (`ConeHarmonicBallsUpToFixedTimeCorrectedStmt`, the binder `h24c` of `closed_5_1`), from the counted
canonical form `firstPass_2_4_canonical_p2` (FirstPass/Phase2Rewire.lean:199). The volume-growth input `h27` is supplied by
`volumeGrowthStmt_of_berestyckiGwynne hBG` (Lemma 2.7, cited from Berestycki-Gwynne, Lemma A.1). The binders are those of
`firstPass_2_4_canonical_p2` minus `h27`, plus `hBG`. -/
theorem coneHarmonicBallsUpToFixedTimeCorrected_of_firstPass_2_4
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hCentre : FrozenGreenBallCentre)
    (hOpen : ClusterOpenLaplacianStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0})
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hFL : FPConeWholePlaneFieldLaw)
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    ConeHarmonicBallsUpToFixedTimeCorrectedStmt :=
  coneHarmonicBallsUpToFixedTimeCorrected_of_canonical
    (MatedCRT.Phase2.firstPass_2_4_canonical_p2 (hstd := hstd) (hCentre := hCentre) (hOpen := hOpen)
      (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat) (hBdry := hBdry)
      (hExist := hExist) (hThm11 := hThm11) (hProp56 := hProp56) (hconf := hconf) (hI2 := hI2) (hK := hK)
      (hloc := hloc) (hSC := hSC) (hE := hE) (hFL := hFL) (h27 := volumeGrowthStmt_of_berestyckiGwynne hBG))

end MatedCRT

namespace MatedCRT.FirstPassClosure

/-- **Proposition 5.1** (prop:IDLA-lower-bound), counted form `closed_5_1_cellRewire` (without `hcell`) with the binder
`h24c` discharged by `coneHarmonicBallsUpToFixedTimeCorrected_of_firstPass_2_4` and the binder `h27` by
`volumeGrowthStmt_of_berestyckiGwynne hBG`. The remaining binders are those of `closed_5_1_cellRewire` minus `h24c` and `h27`,
plus `hBG`; the classes are listed in the report. -/
theorem closed_5_1_ownBinders {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hμae : FrozenLQGMeasureFieldMeasurable 𝒮) (hSB : FrozenFiniteMeasureDiskStandardBorel)
    (hsup : FrozenLeastSupersolutionMemCone 𝒮)
    (hU : FrozenUniversalMeasurabilityOfAnalytic) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hG : FrozenGreenDiscPole) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) (hmeasT : FrozenLQGTestIntegralMeasurable)
    (hstd : FrozenConeLogLocalCodeLawStd) (hmin : FrozenSuperharmonicMinimumPrinciple)
    (hGBC : FrozenGreenBallCentre) (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep) (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) (hG15 : GreenFunctionCrudeBoundStmt 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0}) (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0}) (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0}) (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0}) (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0}) (hSC : ClusterStrongCompatibilityStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1_cellRewire (𝒮 := 𝒮) ν hC hμae hSB hsup hU hexc hG hmodel hFL hLoc hpair hmeasT hstd hmin hGBC hconf hK
    hE hE1 hE2 hscale (volumeGrowthStmt_of_berestyckiGwynne hBG) h22
    (MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_firstPass_2_4 hstd hGBC h32 hSup hCons hMono hCompat hBdry hEx
      hThm11 hProp56 hconf hI2 hK hloc hSC hE hFL hBG)
    hG15 h32 h611 h82 hI2 hSup hCons hMono hCompat hBdry hEx hThm11 hProp56 hloc hSC

end MatedCRT.FirstPassClosure

#print axioms MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_canonical
#print axioms MatedCRT.coneHarmonicBallsUpToFixedTimeCorrected_of_firstPass_2_4
#print axioms MatedCRT.FirstPassClosure.closed_5_1_ownBinders
