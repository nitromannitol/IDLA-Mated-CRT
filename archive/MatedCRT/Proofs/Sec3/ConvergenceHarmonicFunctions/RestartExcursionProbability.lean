import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RestartExcursionOrder
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ExcursionRestartReduction

/-! # Probability of an excursion after a boundary restart -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- The probability of a large post-restart excursion is bounded by a
uniform annulus hit-order estimate at the boundary-cell restart vertex. -/
theorem srwLaw_post_restart_excursion_le
    (m : ℤ → ℤ → ℕ) (D : Set ℤ) (a : ℤ) (c : ℝ≥0∞)
    {ε mε r R d : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hε : 0 < ε) (hm : 0 < mε) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hr : 0 < r) (hd : 0 < d) (hdR : d < R)
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hsmall : ∀ b ∈ cellVertices ε η (sphere z r), diam (cell ε η b) ≤ d)
    (hlarge : ∀ b ∈ cellVertices ε η (sphere z (r + 3 * d)),
      diam (cell ε η b) ≤ d)
    (hbound : ∀ b ∈ cellVertices ε η (sphere z r), srwLaw m b {path |
      vHitTime (cellVertices ε η (sphere (vertexPoint ε η b) R)) path ≤
        vHitTime (cellVertices ε η (sphere z (r + 3 * d))) path} ≤ c) :
    srwLaw m a {x | ∃ k : ℕ, vHitTime D x = k ∧
      x k ∈ cellVertices ε η (sphere z r) ∧
      (k : ℝ) ≤ mε * ((pathExitTime (ball z r)
        (interpolatedWalk ε η mε x)).toNNReal : ℝ) ∧
      R < dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
        (vertexPoint ε η (x k))} ≤ c := by
  apply srwLaw_excursion_le_of_restart_sphere_hit_order m D
    (cellVertices ε η (sphere z r)) ε η z (r + 3 * d) R a c _ hbound
  filter_upwards [srwLaw_ae_restart_outer_hit_le_enlarged_hit m D a hlf hcons hε hm
    hη hp hr hd hdR hadj hsmall hlarge] with x hx hex
  obtain ⟨k, hk, hb, hlo, hfar⟩ := hex
  exact ⟨k, hk, hb, hx k hk hb hlo hfar⟩

end MatedCRT

#print axioms MatedCRT.srwLaw_post_restart_excursion_le
