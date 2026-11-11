import MatedCRT.FirstPass.S2c
import MatedCRT.Proofs.Sec4.Prop42Closure.ConePrematureNull
import MatedCRT.Proofs.Sec4.Prop42Closure.PlateauScalingAssembly
import MatedCRT.Proofs.Sec4.Prop42Closure.BoundedRepresentatives

/-! # FIRST PASS S2d: no two rational touching times

`ConeNoTwoTouchStep` (`FirstPass/S2c.lean`, NEW) is the almost-sure absence of two rational touching times of a stopped
cone family.

Route (all Lean pieces already in `Proofs/Sec4/Prop42Closure`, re-used here):
* `ConePrematureContactNullStep` (`HalfBallClosure.lean`): a.s. the raw `3/4`-clusters of the cone measure have no
  premature half-ball contact (`prop42-proof.tex:275-289`), via `conePrematureContactNullStep_of_fieldLaw`
  (`ConePrematureNull.lean`).
* The plateau input `PlateauScaleInvarianceStep` is `plateauScaleInvarianceStep_assembled` (`PlateauScalingAssembly.lean`),
  fed with the bounded-set repair `scaledBoundedRepresentativesStep_of_localization_and_smoothing`
  (`BoundedRepresentatives.lean`).
* This file: the deterministic link premature contact `⇒` no two rational touches of a stopped family, then the
  closure step `ConeHalfBallClosureInsideStep` through `coneHalfBallClosureInsideStep_of_noTwoTouch` (`S2c.lean`).

Hypotheses of `firstPass_noTwoTouch` are only Draft statements of Harmonic-Balls-LQG and of this paper, cited or
EXTERNAL Props (see the docstring of that theorem). -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace

/-- **Deterministic core (`prop42-proof.tex:275-289`).** If the raw `3/4`-clusters of `ν` have no premature half-ball
contact, a stopped cone family `Λ` (`IsConeHarmonicBallFamilyOn`, `IsStoppedAtHalfBall`) has no two rational times
`0 < q₁ < q₂ < T` with both `Λ_{q₁}` and `Λ_{q₂}` touching `∂B_{1/2}`. Proof: the touch at `q₁` makes
`Λ_{q₁} = interior (closure (cluster ν (3/4) 0 q₁))` non-halfBall (a dense sequence in a closedBall of radius `r < 1/2`
would confine its closure, contradicting the touch point of norm `1/2`), while `Λ_{q₂} ⊆ B_{1/2}` by stopping. -/
theorem noTwoTouch_of_not_prematureContact {ν : Measure ℂ} {Λ : ℝ → Set ℂ} {T : ℝ}
    (hf : IsConeHarmonicBallFamilyOn ν Λ T) (hs : IsStoppedAtHalfBall Λ T)
    (hnot : ¬ halfBallPrematureContact
      (fun t : Ioi (0 : ℝ) => interior (closure (cluster ν (3 / 4) 0 t))))
    (q₁ q₂ : ℚ) (h0 : (0 : ℝ) < q₁) (h12 : (q₁ : ℝ) < q₂) (h2 : (q₂ : ℝ) < T) :
    ¬ (TouchesHalfCircle (Λ (q₁ : ℝ)) ∧ TouchesHalfCircle (Λ (q₂ : ℝ))) := by
  intro hboth
  obtain ⟨⟨x, hx, hxr⟩, -⟩ := hboth
  have hq1 : (q₁ : ℝ) ∈ Ioo 0 T := ⟨h0, h12.trans h2⟩
  have hq2 : (q₂ : ℝ) ∈ Ioo 0 T := ⟨h0.trans h12, h2⟩
  have hC1 : interior (closure (cluster ν (3 / 4) 0 (q₁ : ℝ))) = Λ q₁ :=
    (hf.eq_threeQuarterDisk_cluster hs hq1).symm
  have hC2 : interior (closure (cluster ν (3 / 4) 0 (q₂ : ℝ))) = Λ q₂ :=
    (hf.eq_threeQuarterDisk_cluster hs hq2).symm
  refine hnot ⟨⟨q₁, h0⟩, ⟨q₂, h0.trans h12⟩, h12, ?_, ?_⟩
  · rintro ⟨r', hr', hdense⟩
    have hdense' : ∀ n : ℕ, denseSeq ℂ n ∈ interior (closure (cluster ν (3 / 4) 0 (q₁ : ℝ))) →
        denseSeq ℂ n ∈ closedBall (0 : ℂ) (r' : ℝ) := hdense
    have hcl := closure_subset_closedBall_of_halfBallTest isOpen_interior hdense'
    have hx' : x ∈ closure (interior (closure (cluster ν (3 / 4) 0 (q₁ : ℝ)))) := by
      rw [hC1]
      exact hx
    have hd : dist x 0 ≤ (r' : ℝ) := mem_closedBall.mp (hcl hx')
    rw [dist_zero_right, hxr] at hd
    linarith
  · intro n hn
    have hn' : denseSeq ℂ n ∈ Λ q₂ := by
      rw [← hC2]
      exact hn
    exact ball_subset_closedBall (hs.1 (q₂ : ℝ) hq2 hn')

/-- **`ConeNoTwoTouchStep` from premature contact.** The almost-sure form: a.s. the raw clusters have no premature
contact (`ConePrematureContactNullStep`) implies `ConeNoTwoTouchStep`, by `noTwoTouch_of_not_prematureContact`
applied to the stopped family of the a.s. event. -/
theorem coneNoTwoTouchStep_of_prematureContactNull (h : ConePrematureContactNullStep) :
    ConeNoTwoTouchStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  filter_upwards [h γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω
  intro T Λ hΛ hs q₁ q₂ h0 h12 h2
  exact noTwoTouch_of_not_prematureContact hΛ hs hω q₁ q₂ h0 h12 h2

/-- **`ConeNoTwoTouchStep` (NEW, `prop42-proof.tex:230-289`) from Draft statements and EXTERNAL inputs.**
Inputs and status:
* `hI2 : LQGVolumeGrowthAllScalesStmt` (Harmonic-Balls-LQG input I2, `HarmonicBalls/Draft/Section2.lean:122`): Draft of
  the other paper, cited.
* `hDS : DS11CoordinateRuleFixedAffine` (`Proposed/DuplantierSheffieldCoordinate2011`): EXTERNAL, the Duplantier-Sheffield
  coordinate rule for the LQG measure under affine maps.
* `hJG : JensenGreenLocalizationStmt`, `hJS : JensenSmoothingStmt` (`BoundedRepresentatives.lean`): EXTERNAL, Riesz
  localization (Saff 2010 Thm 2.4) and superharmonic smoothing.
* `hloc : HarmonicBallLocalSetStmt`, `hEx : ExistenceHarmonicBallsStmt`, `hSC : ClusterStrongCompatibilityStmt`:
  Draft statements of Harmonic-Balls-LQG (cited).
* `hVG : VolumeGrowthStmt` (`Draft/Section2.lean`, inventory row 2.7, BG20 Lemma A.1): cited, EXTERNAL.
* `hB2 : WholePlaneLQGModelStep` (`ConeWholePlaneSteps.lean:57`): EXTERNAL, existence of a whole-plane GFF with its
  γ-LQG measure (Duplantier-Miller-Sheffield).
* `hFL : ConeWholePlaneFieldLawStep` (`ConeWholePlaneSteps.lean:66`): EXTERNAL, IDLA eq. (2.4), the restriction law of the
  quantum cone to `B_1` (Duplantier-Sheffield). The LQG locality input is proved internally
  (`LQGMeasureLocalityFunctionalStep_proof`). -/
theorem firstPass_noTwoTouch (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hDS : MatedCRT.Proposed.DS11CoordinateRuleFixedAffine)
    (hJG : JensenGreenLocalizationStmt) (hJS : JensenSmoothingStmt)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0}) (hVG : VolumeGrowthStmt)
    (hB2 : WholePlaneLQGModelStep) (hFL : ConeWholePlaneFieldLawStep) : ConeNoTwoTouchStep :=
  coneNoTwoTouchStep_of_prematureContactNull
    (conePrematureContactNullStep_of_fieldLaw hloc hEx hSC
      (plateauScaleInvarianceStep_assembled hI2 hDS
        (scaledBoundedRepresentativesStep_of_localization_and_smoothing hJG hJS))
      hVG (wholePlaneVolumeGrowthAeStep_of_allScales hI2) hB2 hFL)

/-- **`ConeHalfBallClosureInsideStep` (`StoppedClosure.lean:18`) through the no-two-touch step.** Same inputs as
`firstPass_noTwoTouch`. -/
theorem firstPass_closureInside (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hDS : MatedCRT.Proposed.DS11CoordinateRuleFixedAffine)
    (hJG : JensenGreenLocalizationStmt) (hJS : JensenSmoothingStmt)
    (hloc : HarmonicBallLocalSetStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0}) (hVG : VolumeGrowthStmt)
    (hB2 : WholePlaneLQGModelStep) (hFL : ConeWholePlaneFieldLawStep) :
    ConeHalfBallClosureInsideStep :=
  coneHalfBallClosureInsideStep_of_noTwoTouch
    (firstPass_noTwoTouch hI2 hDS hJG hJS hloc hEx hSC hVG hB2 hFL)

end MatedCRT
