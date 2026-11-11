import HarmonicBalls.Proofs.Sec2.Assembly
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly

/-! # FIRST PASS S2VG, Literature: the all-scales volume-growth input I2

`LQGVolumeGrowthAllScalesStmt` (I2, `HarmonicBalls/Draft/Section2.lean:122`) is one constant in both repositories:
IDLA has no local definition and reaches `HarmonicBalls.LQGVolumeGrowthAllScalesStmt` through `open HarmonicBalls`.

`HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_literature` (`HarmonicBalls/Proofs/Sec2/Assembly.lean:120`) proves I2 from
six hypotheses. Here:
* `hAff` (`WholePlaneGFFAffineInvariance`) is discharged by the proved theorem `wholePlaneGFFAffineInvariance_proved`
  (`HarmonicBalls/Proofs/Sec9/AffineInvarianceAssembly.lean:21`);
* the mixture step `wholePlaneGFFMixtureStep_holds` is proved in HB (`HarmonicBalls/Proofs/Sec2/MixtureGFF.lean:123`);
* the five other inputs stay named hypotheses, typed by the HB literature Props `LitWholePlaneBallMass`, `LitCoordChange`,
  `LitWeylScaling`, `LitExistence`, `LitNonatomic` (HB `HarmonicBalls/Proposed/LQG.lean`). They are cited inputs
  (class b). No new IDLA frozen Prop is introduced.
-/

namespace MatedCRT.S2VG

open MeasureTheory HarmonicBalls

/-- Cited input (class b): whole-plane LQG ball mass bounds `WholePlaneLQGBallMassBounds` (HB `Proposed/LQG.lean:154`);
Ding-Gwynne, arXiv:1807.01072, Comm. Math. Phys. 374 (2020), Lemma 3.8, eq. (3.14). -/
abbrev LitWholePlaneBallMass : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    WholePlaneLQGBallMassBounds P γ hC hcirc

/-- Cited input (class b): the coordinate change of the LQG measure `LQGMeasureCoordChange` at `α₀ = 0`
(HB `Proposed/LQG.lean:116`); Duplantier-Sheffield (2011) Prop. 2.1; Sheffield-Wang, arXiv:1605.06171, Thms. 1.1, 1.4;
Bou-Rabee-Gwynne, arXiv:2208.11795, Fact 2.1 IV. -/
abbrev LitCoordChange : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureCoordChange P γ 0 hC hcirc

/-- Cited input (class b): Weyl scaling of the LQG measure `LQGMeasureWeylScaling` at `α₀ = 0`
(HB `Proposed/LQG.lean:95`); Bou-Rabee-Gwynne, arXiv:2208.11795, Fact 2.1 III. -/
abbrev LitWeylScaling : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureWeylScaling P γ 0 hC hcirc

/-- Cited input (class b): existence of the LQG measure `LQGMeasureExistence` at `α₀ = 0` (HB `Proposed/LQG.lean:68`);
Duplantier-Sheffield (2011) Thm. 1.1; Bou-Rabee-Gwynne, arXiv:2208.11795, Sec. 2.2. -/
abbrev LitExistence : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureExistence P γ 0 hC hcirc

/-- Cited input (class b): non-atomicity of the LQG measure `LQGMeasureNonatomic` for general `α₀` (HB
`Proposed/LQG.lean:77`); Bou-Rabee-Gwynne, arXiv:2208.11795, Fact 2.1 I. -/
abbrev LitNonatomic : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureNonatomic P γ α₀ hC hcirc

/-- **I2 from the literature.** `LQGVolumeGrowthAllScalesStmt` (eq:volume-growth) from the five
cited inputs above. The affine invariance of the whole-plane GFF is the proved theorem `wholePlaneGFFAffineInvariance_proved`. -/
theorem lqgVolumeGrowthAllScalesStmt_litI2
    (hDG : LitWholePlaneBallMass) (hCC : LitCoordChange) (hW : LitWeylScaling) (hE : LitExistence)
    (hN : LitNonatomic) : LQGVolumeGrowthAllScalesStmt.{0} :=
  HarmonicBalls.lqgVolumeGrowthAllScalesStmt_of_literature.{0} hDG
    (fun _ _ P hC hcirc => HarmonicBalls.wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC hW hE hN

end MatedCRT.S2VG
