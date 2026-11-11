import MatedCRT.Defs.Setting

/-!
# Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity*: Lemma 3.1 as a cited input

Lemma 3.1 of Bou-Rabee and Gwynne, arXiv:2208.11795 (the companion paper HB22), is the basic property of the least
supersolution of the obstacle problem: almost surely, the least supersolution is finite, continuous and an element of
the set of supersolutions. It is cited verbatim, as an input of the mated-CRT development, and not imported from the
Harmonic-Balls-LQG package.

Setting of the printed lemma (`paper/lqg_harmonic_ball-corrected.tex`, lines 377-387): `γ ∈ (0,2)`,
`α₀ ∈ (-∞, Q)`, and `h = h^ℂ - α₀ log|·|` for a whole-plane Gaussian free field `h^ℂ`; `μ_h` is its LQG measure.

The objects are those of `MatedCRT.Defs.Setting`, which re-exports the HB22 definitions `HarmonicBalls.supersolutions`
(eq:super-solutions, line 583), `HarmonicBalls.leastSupersolution` (eq:least-super-solution, line 588),
`HarmonicBalls.IsWholePlaneGFF` and `HarmonicBalls.IsLQGMeasureOfField`.
-/

namespace MatedCRT

open HarmonicBalls MeasureTheory Set Metric

/-- **HB22 Lemma 3.1 (`lemma:basic-properties`), printed statement.** Printed text
(`paper/lqg_harmonic_ball-corrected.tex`, lines 627-629; `paper/lqg_harmonic_ball.tex`, lines 621-623; page 13 as cited by
`MatedCRT/FirstPass/Frozen/S5k.lean`): "On an event of probability 1, for all $t, r > 0$ and~$z \in B_r$,
$\lss{B_r;z}{t}$ is finite, continuous, and an element of $\mclS{B_r;z}{t}$."

Here `finite` is the bounded-below clause `BddBelow` of the values of the supersolutions at each point of the closed
ball, `continuous` is `ContinuousOn` on the closed ball, and the last clause is membership in `supersolutions`. The
statement quantifies over all `γ ∈ (0,2)` and `α₀ < Q = lqgQ γ` as in HB22 (line 377). The Harmonic-Balls-LQG draft
`LeastSupersolutionMemStmt` (`HarmonicBalls/Draft/Section3.lean:47`) is the same statement with a universe-polymorphic
probability space. -/
def HarmonicBallsLemma31Printed : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ t r : ℝ, 0 < t → 0 < r → ∀ z ∈ ball (0 : ℂ) r,
    (∀ x ∈ closedBall (0 : ℂ) r, BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutions (μ ω) r z t)) ∧
    ContinuousOn (leastSupersolution (μ ω) r z t) (closedBall 0 r) ∧
    leastSupersolution (μ ω) r z t ∈ supersolutions (μ ω) r z t

end MatedCRT
