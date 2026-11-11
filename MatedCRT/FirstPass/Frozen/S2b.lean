import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime
import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime

/-!
# Frozen external inputs for IDLA paper Lemmas 2.4 and 2.5

Each `def` below is an external input of the formalization. A frozen `Prop` is used only as an explicit hypothesis of a theorem of the formalization. Nothing here is proved, and no strict growth of harmonic balls is assumed.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set HarmonicBalls

/-- Existence of a whole-plane GFF `h^ℂ` (normalized by `h^ℂ_1(0) = 0`) on a probability space whose LQG measure is the `γ`-LQG measure of `h^ℂ - γ log |·|`. Source: Sheffield 2007 (whole-plane GFF); Duplantier-Sheffield 2011 Proposition 1.1 and Weyl scaling (the setting of HB22, line 531); standard; locator not yet pinned.
Truth check: TRUE. -/
def FrozenWholePlaneLogLQGExistence : Prop := WholePlaneLogLQGExistenceStep

/-- The restrictions to `B_1` of the `γ`-quantum cone field and of `h^ℂ - γ log |·|` agree in law through their circle average processes over the circles in `B_1` (eq:gff, paper line 444, stated after Definition 2.1 as immediate from the definitions). Source: standard GFF restriction fact, stated in the paper as immediate from Definition 2.1; locator not yet pinned.
Truth check: TRUE. `UnitBallCircle` admits only radii whose closed disk lies inside `B_1`. -/
def FrozenConeRestriction : Prop := ConeRestrictionStep

/-- Locality of harmonic balls: for `γ ∈ (0, 2)` there is one measurable set `S` of restrictions to `B_1` such that, for the quantum cone and for `h^ℂ - γ log |·|`, a.s. the event of Lemma 2.4 holds iff the restriction of the circle average process to `B_1` lies in `S`. Source: HB22 = [bou2022harmonic], Proposition 1.3 (harmonic balls depend locally on the field), cited at the paper's line 542 (proof of Lemma 2.4). Literature input, frozen.
Truth check: TRUE. `HasConeHarmonicBallsUpToHalfBall` is ordinary stopped-family existence, which holds almost surely for both specified models. -/
def FrozenConeHarmonicBallLocality : Prop := ConeHarmonicBallLocalityStep

/-- Measurability of the event of Lemma 2.4 in the circle average process, in the stopped form. For `γ ∈ (0, 2)` there is a set `G` of circle average processes such that, for every quantum cone field `(P, hC, hcirc, μ)`, `G` is null-measurable for the law of the circle average process `P.map (circleProcess ∘ hcirc)`; and for every continuous circle average process `c` with LQG measure `ν` (circle average limit), `circleProcess c ∈ G` iff there is a family of harmonic balls `{Λ_t}_{0 < t < T}` for `ν` with the properties of Theorem 2.3 on `(0, T)`, stopped at `∂B_{1/2}` (`IsStoppedAtHalfBall`, Lemma 2.4).
Source: HB22 Proposition 1.3 (locality), restated: (i) the strict growth clause `IsStrictHalfBallFamily` is removed (the paper does not assert it), and (ii) the functional `Φ` with `familyProcess Λ T = Φ (circleProcess c)` is omitted (it needs uniqueness of the stopping time, which the existence and fixed-domain uniqueness statements do not use). Standard HB22 input; locator not yet pinned.
Retired: the functional `G`, with the equivalence to the existence of a stopped family, asserts more than any printed HB22 result, so it is not an admissible hypothesis. Its measurability is to be proved before its consumer is admissible again. -/
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
