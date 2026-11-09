import MatedCRT.FirstPass.S1c.Threshold

/-!
# FIRST PASS, Lemma 5.3 (B1b): supersolution values are bounded below off the pole (deterministic)

For `p ∈ B̄_R` with `p ≠ 0`, every supersolution `w` of the obstacle problem at level `u` satisfies the obstacle bound
`-u G_{B_R}(0,p) ≤ w(p)` (the third component of `supersolutions`, as in S1c/Threshold.lean). So the values `w(p)` are bounded below,
which is the hypothesis `hbdd` of the B1b lemmas (B1bThreshold.lean). At the pole `p = 0` the bound needs the volume-growth input
(`bddBelow_supersolutionsOn_values_pole`, Harmonic-Balls) and is not used here.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric HarmonicBalls

/-- **Supersolution values are bounded below off the pole** (B1b, deterministic): see the module docstring. -/
theorem bddBelow_supersolution_values_of_ne_zero {μ : Measure ℂ} {R u : ℝ} {p : ℂ}
    (hp : p ∈ closedBall (0 : ℂ) R) (hp0 : p ≠ 0) :
    BddBelow ((fun w : ℂ → ℝ => w p) '' supersolutions μ R 0 u) := by
  refine ⟨-u * greenFunction (ball (0 : ℂ) R) 0 p, ?_⟩
  rintro y ⟨w, hw, rfl⟩
  obtain ⟨-, -, hob⟩ := hw
  exact hob p hp hp0

end MatedCRT.S5c
