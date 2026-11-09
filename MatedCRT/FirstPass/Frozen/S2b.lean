import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime
import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime

/-!
# First-pass frozen external inputs for IDLA paper Lemmas 2.4 and 2.5 (q1, wave 2)

Each `def` below is an EXTERNAL input of the first-pass formalization (operator note 2026-11-09 17:00 UTC: freeze the
external inputs, prove the new steps). A frozen `Prop` is used only as an explicit hypothesis of a `firstPass_…`
theorem in `MatedCRT/FirstPass/S2b.lean`. Nothing here is proved, and no strict growth of harmonic balls is assumed.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set HarmonicBalls

/-- FIRST-PASS FROZEN. Existence of a whole-plane GFF `h^ℂ` (normalized by `h^ℂ_1(0) = 0`) on a probability space whose
LQG measure is the `γ`-LQG measure of `h^ℂ - γ log |·|`. Source: Sheffield 2007 (whole-plane GFF); Duplantier-Sheffield
2011 Proposition 1.1 and Weyl scaling (the setting of HB22, line 531); standard; locator pending.
Same statement as the Step `WholePlaneLogLQGExistenceStep` (Steps/Sec2/ConeHarmonicBallsUpToFixedTime.lean:50).
Used by: firstPass_2_4_corrected, firstPass_2_5_corrected. -/
def FrozenWholePlaneLogLQGExistence : Prop := WholePlaneLogLQGExistenceStep

/-- FIRST-PASS FROZEN. The restrictions to `B_1` of the `γ`-quantum cone field and of `h^ℂ - γ log |·|` agree in law
through their circle average processes over the circles in `B_1` (eq:gff, paper line 444, stated after Definition 2.1 as
immediate from the definitions). Source: standard GFF restriction fact, stated in the paper as immediate from
Definition 2.1; locator pending. Same statement as the Step `ConeRestrictionStep`
(Steps/Sec2/ConeHarmonicBallsUpToFixedTime.lean:79).
Used by: firstPass_2_4_corrected, firstPass_2_5_corrected. -/
def FrozenConeRestriction : Prop := ConeRestrictionStep

/-- FIRST-PASS FROZEN. Locality of harmonic balls: for `γ ∈ (0, 2)` there is one measurable set `S` of restrictions to
`B_1` such that, for the quantum cone and for `h^ℂ - γ log |·|`, a.s. the event of Lemma 2.4 holds iff the restriction of
the circle average process to `B_1` lies in `S`. Source: HB22 = [bou2022harmonic], Proposition 1.3 (harmonic balls depend
locally on the field), cited at the paper's line 542 (proof of Lemma 2.4); operator ruling 2026-11-09 17:00 (EXTERNAL,
freeze). Same statement as the Step `ConeHarmonicBallLocalityStep` (Steps/Sec2/ConeHarmonicBallsUpToFixedTime.lean:94).
Used by: firstPass_2_4_corrected, firstPass_2_5_corrected. -/
def FrozenConeHarmonicBallLocality : Prop := ConeHarmonicBallLocalityStep

/-- FIRST-PASS FROZEN. Measurability of the event of Lemma 2.4 in the circle average process, in the stopped form.
For `γ ∈ (0, 2)` there is a set `G` of circle average processes such that, for every quantum cone field `(P, hC, hcirc, μ)`,
`G` is null-measurable for the law of the circle average process `P.map (circleProcess ∘ hcirc)`; and for every
continuous circle average process `c` with LQG measure `ν` (circle average limit), `circleProcess c ∈ G` iff there is a
family of harmonic balls `{Λ_t}_{0 < t < T}` for `ν` with the properties of Theorem 2.3 on `(0, T)`, stopped at `∂B_{1/2}`
(`IsStoppedAtHalfBall`, Lemma 2.4).
Source: HB22 Proposition 1.3 (locality), as the first conjunct of the Step `ConeHalfBallFamilyFunctionalStep`
(Steps/Sec2/ConeScaleInvarianceUpToFixedTime.lean:72), restated: (i) the strict growth clause `IsStrictHalfBallFamily` is
removed (`ConeHarmonicBallStrictGrowthStep` is not assumed; the paper does not assert it), and (ii) the functional `Φ` with
`familyProcess Λ T = Φ (circleProcess c)` is omitted (it needs uniqueness of the stopping time, not used by the existence
and fixed-domain uniqueness of firstPass_2_5_corrected). Standard HB22 input; locator pending.
Used by: firstPass_2_5_corrected. -/
def FrozenConeHalfBallFamilyMeasurable : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set (Set.Ioi (0 : ℝ) × ℂ → ℝ),
    (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
      NullMeasurableSet G (P.map fun ω => circleProcess (hcirc ω))) ∧
    ∀ c : ℝ → ℂ → ℝ, ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) → ∀ ν : Measure ℂ,
      IsLQGLimit γ c ν →
      (circleProcess c ∈ G ↔ ∃ (T : ℝ) (Λ : ℝ → Set ℂ), 0 < T ∧ IsConeHarmonicBallFamilyOn ν Λ T ∧
        IsStoppedAtHalfBall Λ T)

end MatedCRT
