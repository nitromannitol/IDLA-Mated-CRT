import MatedCRT.FirstPass.S4S6c.BallMassLower
import MatedCRT.FirstPass.Frozen.S4S6c

/-!
# Lemma 2, eq (8), almost-everywhere form

`BallMassLower.ballMass_lower_of_polyHighProb` assumes the everywhere measurability `hμ` of the ball masses. Here the
measure family is only assumed to agree almost surely with an `m'`-measurable random measure `g` (the freezable form
`FrozenLQGMeasureFieldMeasurable`). The polynomial hypothesis transfers from `μ` to `g` on the full-measure set `{μ = g}`
(`PolyHighProb` only depends on the probabilities of the complements), and the everywhere theorem applies to `g`.
The conclusion transfers back on the same full-measure set.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace MatedCRT

namespace BallMassLowerAE

/-- **Lemma 2, eq (8), a.e. form**: the ball-mass lower bound with a field-measurable radius, when the measures agree a.s.
with an `m'`-measurable random measure. -/
theorem ballMass_lower_of_ae {Ω : Type*} {m' : MeasurableSpace Ω} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (μ : Ω → Measure ℂ)
    (hμm : ∃ g : Ω → Measure ℂ, Measurable[m'] g ∧ ∀ᵐ ω ∂P, μ ω = g ω)
    {ρ ρ₁ b : ℝ} (hρ : 0 < ρ) (hρρ₁ : ρ < ρ₁) (hρ₁ : ρ₁ < 1) (hb : 0 < b)
    (hlow : HarmonicBalls.PolyHighProb P fun δ =>
      {ω | ∀ z ∈ Metric.ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ b) ≤ μ ω (Metric.ball z δ)}) :
    ∃ tStar : Ω → ℝ, Measurable[m'] tStar ∧ ∀ᵐ ω ∂P, 0 < tStar ω ∧
      ∀ y ∈ closedBall (0 : ℂ) ρ, ∀ t : ℝ, 0 < t → t < tStar ω →
        ENNReal.ofReal ((t / 4) ^ b) ≤ μ ω (Metric.ball y t) := by
  obtain ⟨g, hgm, hgae⟩ := hμm
  have hGood : P {ω | ¬ μ ω = g ω} = 0 := ae_iff.1 hgae
  have hμg : ∀ (q : ℂ) (s : ℝ), Measurable[m'] fun ω => g ω (Metric.ball q s) := fun q s =>
    Measure.measurable_measure.1 hgm _ measurableSet_ball
  -- the polynomial bound transfers from `μ` to `g` (the two events agree on `{μ = g}`)
  have hlowg : HarmonicBalls.PolyHighProb P fun δ =>
      {ω | ∀ z ∈ Metric.ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ b) ≤ g ω (Metric.ball z δ)} := by
    obtain ⟨p, hp, C, r₀, hr₀, h⟩ := hlow
    refine ⟨p, hp, C, r₀, hr₀, fun r hr hr' => ?_⟩
    have hsub : {ω | ∀ z ∈ Metric.ball (0 : ℂ) (1 - r),
          ENNReal.ofReal (r ^ b) ≤ g ω (Metric.ball z r)}ᶜ ⊆
        {ω | ∀ z ∈ Metric.ball (0 : ℂ) (1 - r), ENNReal.ofReal (r ^ b) ≤ μ ω (Metric.ball z r)}ᶜ ∪
          {ω | ¬ μ ω = g ω} := by
      intro ω hω
      by_cases hG : μ ω = g ω
      · left
        intro hE
        apply hω
        intro z hz
        rw [← hG]
        exact hE z hz
      · right
        exact hG
    calc P {ω | ∀ z ∈ Metric.ball (0 : ℂ) (1 - r),
            ENNReal.ofReal (r ^ b) ≤ g ω (Metric.ball z r)}ᶜ
        ≤ P ({ω | ∀ z ∈ Metric.ball (0 : ℂ) (1 - r), ENNReal.ofReal (r ^ b) ≤ μ ω (Metric.ball z r)}ᶜ ∪
            {ω | ¬ μ ω = g ω}) := measure_mono hsub
      _ ≤ P {ω | ∀ z ∈ Metric.ball (0 : ℂ) (1 - r), ENNReal.ofReal (r ^ b) ≤ μ ω (Metric.ball z r)}ᶜ +
            P {ω | ¬ μ ω = g ω} := measure_union_le _ _
      _ = P {ω | ∀ z ∈ Metric.ball (0 : ℂ) (1 - r), ENNReal.ofReal (r ^ b) ≤ μ ω (Metric.ball z r)}ᶜ := by
          rw [hGood, add_zero]
      _ ≤ ENNReal.ofReal (C * r ^ p) := h r hr hr'
  obtain ⟨tStar, htm, htS⟩ := BallMassLower.ballMass_lower_of_polyHighProb g hρ hρρ₁ hρ₁ hb hlowg hμg
  refine ⟨tStar, htm, ?_⟩
  filter_upwards [htS, hgae] with ω hω hμω
  refine ⟨hω.1, fun y hy t ht hts => ?_⟩
  rw [hμω]
  exact hω.2 y hy t ht hts

#print axioms MatedCRT.BallMassLowerAE.ballMass_lower_of_ae

end BallMassLowerAE

end MatedCRT
