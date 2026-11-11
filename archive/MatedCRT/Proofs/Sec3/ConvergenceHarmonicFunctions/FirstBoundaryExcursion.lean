import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.FirstBoundaryEdge
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RestartExcursionProbability
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.RateTailReduction

/-! # Excursion probability from the first boundary cell -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- For a walk started in the disk interior, the probability that Euclidean
exit lies far from its first boundary-cell representative is bounded by a
uniform annulus hit-order estimate. -/
theorem srwLaw_first_boundary_excursion_le
    (m : ℤ → ℤ → ℕ) (a : ℤ) (c : ℝ≥0∞)
    {ε mε r R d : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hε : 0 < ε) (hm : 0 < mε) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hr : 0 < r) (hd : 0 < d) (hdR : 2 * d ≤ R)
    (ha : a ∈ interiorCellVertices ε η (ball z r))
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hsmall : ∀ b ∈ interiorCellVertices ε η (ball z r) ∪
      cellVertices ε η (sphere z r), diam (cell ε η b) ≤ d)
    (hlarge : ∀ b ∈ cellVertices ε η (sphere z (r + 3 * d)),
      diam (cell ε η b) ≤ d)
    (hbound : ∀ b ∈ cellVertices ε η (sphere z r), srwLaw m b {path |
      vHitTime (cellVertices ε η (sphere (vertexPoint ε η b) R)) path ≤
        vHitTime (cellVertices ε η (sphere z (r + 3 * d))) path} ≤ c) :
    srwLaw m a {x | ∃ k : ℕ,
      vHitTime (cellVertices ε η (sphere z r)) x = k ∧
      x k ∈ cellVertices ε η (sphere z r) ∧
      R < dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
        (vertexPoint ε η (x k))} ≤ c := by
  let B := cellVertices ε η (sphere z r)
  have hdR' : d < R := by linarith
  have hnb := (disk_dirichlet_decomposition_geometry (z := z) hε hr hη hp hadj hlf hcons).2.2.1
  have hsteps : ∀ᵐ x ∂srwLaw m a, ∀ n,
      x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0 := by
    rw [ae_all_iff]
    intro n
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (WalkSteps.srwLaw_nonadjacent_null m n a)] with x hx
    exact Classical.not_not.1 hx
  calc
    _ ≤ srwLaw m a {x | ∃ k : ℕ, vHitTime B x = k ∧ x k ∈ B ∧
        (k : ℝ) ≤ mε * ((pathExitTime (ball z r)
          (interpolatedWalk ε η mε x)).toNNReal : ℝ) ∧
        R < dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
          (vertexPoint ε η (x k))} := by
      apply measure_mono_ae
      filter_upwards [srwLaw_ae_start m a, hsteps,
        srwLaw_ae_interpolatedWalk_exit_ball_lt_top m hlf hcons hε hm hη hp z r a] with x hstart hs hfin
      rintro ⟨k, hk, hb, hfar⟩
      have hstart' : x 0 ∈ interiorCellVertices ε η (ball z r) := hstart ▸ ha
      cases k with
      | zero =>
        exact False.elim ((Set.disjoint_left.1 (disjoint_interiorCellVertices_sphere ε η z hr)) hstart' hb)
      | succ k =>
        refine ⟨k + 1, hk, hb, ?_, hfar⟩
        exact first_boundary_visit_before_exit_of_large_distance hε.le hm hη hr m x k
          hstart' hs hnb hadj hsmall hk (ne_of_lt hfin) hdR hfar
    _ ≤ c := srwLaw_post_restart_excursion_le m B a c hlf hcons hε hm hη hp hr hd hdR'
      hadj (fun b hb => hsmall b (Or.inr hb)) hlarge hbound

end MatedCRT

#print axioms MatedCRT.srwLaw_first_boundary_excursion_le
