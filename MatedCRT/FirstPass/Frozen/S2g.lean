import MatedCRT.FirstPass.S2f

/-!
# First-pass frozen inputs of the good-set step (fp-S2g, q1)

EXTERNAL facts of classical potential theory used by the deterministic certificate lemmas of
`FirstPass/S2g/GoodSet.lean` (the good set of `ConeClosureGoodMeasureLawStep`). They are about the Green function of a
disc and the minimum principle, not about the paper's clusters or harmonic balls.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- FIRST-PASS FROZEN. Minimum principle for weakly superharmonic functions (EXTERNAL: classical potential theory).
Let `U ⊆ ℂ` be bounded and open, and let `f` be continuous on `closure U` with `Δf ≤ 0` in `U` in the distributional
sense (`LaplacianLE f 0 U`, HarmonicBalls.Defs.Laplacian). If `f ≥ 0` on the frontier of `U`, then `f ≥ 0` on `U`.
Source: standard; locator pending (Armitage and Gardiner, *Classical Potential Theory*, Springer 2001: a continuous
distributionally superharmonic function is superharmonic, by mollification, and the usual minimum principle applies;
no boundary smoothness or connectedness is needed).
Used by: `certificate_le_supersolution` (FirstPass/S2g/GoodSet.lean). -/
def FrozenSuperharmonicMinimumPrinciple : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℝ), IsOpen U → Bornology.IsBounded U → ContinuousOn f (closure U) →
    LaplacianLE f 0 U → (∀ x ∈ frontier U, 0 ≤ f x) → ∀ x ∈ U, 0 ≤ f x

/-- FIRST-PASS FROZEN. Green function of a disc with pole at the centre (EXTERNAL: classical potential theory). For
`R > 0`, `x ↦ G_{B_R}(0, x)` is continuous on `closedBall 0 R \ {0}` and tends to `+∞` at the pole, since the Newton
kernel `-(2π)⁻¹ log ‖x‖` dominates and the harmonic correction is locally bounded (explicitly `G = (2π)⁻¹ log (R/‖x‖)`).
Source: standard; locator pending (Armitage and Gardiner, *Classical Potential Theory*, Green function of a ball).
HB `continuousOn_greenFunction_ball_of_stmt` gives the continuity part conditionally on `GreenFunctionBallStmt`.
Used by: `isOpen_certCluster` (FirstPass/S2g/GoodSet.lean). -/
def FrozenGreenDiscPole : Prop :=
  ∀ R : ℝ, 0 < R → ContinuousOn (greenFunction (ball 0 R) 0) (closedBall 0 R \ {0}) ∧
    Tendsto (greenFunction (ball 0 R) 0) (𝓝[≠] 0) atTop

end MatedCRT
