import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.EnvTestHolderExtension
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.EnvTestHolderFamily

/-!
# Countable approximation of Hölder tests on a ball (E-c2-9)

Combining the Hölder extension to the closed ball with the countable dense family of Hölder tests on the
compact closed ball: for fixed Hölder constants there is a countable family of Hölder tests on
`closedBall z r` which approximates every `(C, χ)`-Hölder function on `ball z r` uniformly on the ball,
to any accuracy. This is the approximation property used in the cover argument of E-c2-9.
-/

namespace MatedCRT

open Metric Set
open scoped NNReal

/-- **Countable approximation of Hölder tests on a ball.** For `0 < r` and fixed `C, χ` with `0 < χ`, there
is a countable family `D` of `(C, χ)`-Hölder tests on `closedBall z r` such that every `(C, χ)`-Hölder
function `f` on `ball z r` is approximated uniformly on the ball, to any accuracy `δ > 0`, by a member of
`D`. -/
theorem exists_countable_holderWith_approx_ball {z : ℂ} {r : ℝ} (hr : 0 < r) {C χ : ℝ≥0}
    (hχ : 0 < χ) :
    ∃ D : Set C(closedBall z r, ℝ), D.Countable ∧ (∀ G ∈ D, HolderWith C χ G) ∧
      ∀ f : ℂ → ℝ, HolderOnWith C χ f (ball z r) → ∀ δ : ℝ, 0 < δ →
        ∃ G ∈ D, ∀ x (hx : x ∈ ball z r), |f x - G ⟨x, ball_subset_closedBall hx⟩| < δ := by
  have : CompactSpace (closedBall z r) := isCompact_iff_compactSpace.1 (isCompact_closedBall z r)
  obtain ⟨D, hDc, hDH, hDd⟩ := exists_countable_holderWith_dense (closedBall z r) C χ
  refine ⟨D, hDc, hDH, fun f hf δ hδ => ?_⟩
  obtain ⟨F, hFH, hFf⟩ := exists_holderWith_closedBall_extension hr hχ hf
  obtain ⟨G, hG, hdist⟩ := hDd F hFH δ hδ
  refine ⟨G, hG, fun x hx => ?_⟩
  rw [← hFf x hx, ← Real.dist_eq]
  exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist _) hdist

end MatedCRT
