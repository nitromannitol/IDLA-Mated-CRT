import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.EnteringEdgeAlternative
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PrehitInterior

/-! # The edge entering the first boundary cell -/

namespace MatedCRT

open Set Metric _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- For a nearest-neighbour path started in the disk interior, a large exit
location displacement from the first boundary-cell representative forces
that first boundary hit to precede Euclidean exit. -/
theorem first_boundary_visit_before_exit_of_large_distance
    {ε mε d r R : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 ≤ ε) (hm : 0 < mε) (hη : Continuous η) (hr : 0 < r)
    (m : ℤ → ℤ → ℕ) (x : ℕ → ℤ) (k : ℕ)
    (hstart : x 0 ∈ interiorCellVertices ε η (ball z r))
    (hstep : ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)
    (hnb : ∀ v ∈ interiorCellVertices ε η (ball z r), ∀ w,
      m v w ≠ 0 → w ∈ interiorCellVertices ε η (ball z r) ∪
        cellVertices ε η (sphere z r))
    (hadj : ∀ j l, m j l ≠ 0 → (cell ε η j ∩ cell ε η l).Nonempty)
    (hdiam : ∀ b ∈ interiorCellVertices ε η (ball z r) ∪
      cellVertices ε η (sphere z r), diam (cell ε η b) ≤ d)
    (hfirst : vHitTime (cellVertices ε η (sphere z r)) x = ((k + 1 : ℕ) : ℕ∞))
    (hfin : pathExitTime (ball z r) (interpolatedWalk ε η mε x) ≠ ⊤)
    (hR : 2 * d ≤ R)
    (hfar : R < dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
      (vertexPoint ε η (x (k + 1)))) :
    ((k + 1 : ℕ) : ℝ) ≤ mε *
      ((pathExitTime (ball z r) (interpolatedWalk ε η mε x)).toNNReal : ℝ) := by
  have hin : ∀ n < k + 1, x n ∈ interiorCellVertices ε η (ball z r) := by
    intro n hn
    apply mem_before_hit_of_neighbours m _ _ x hstart hstep hnb n
    rw [hfirst]
    exact_mod_cast hn
  have hboundary : x (k + 1) ∈ cellVertices ε η (sphere z r) := by
    have hne : vHitTime (cellVertices ε η (sphere z r)) x ≠ ⊤ := by rw [hfirst]; simp
    have h := apply_vHitTime_mem_of_ne_top hne
    rw [hfirst, ENat.toNat_natCast] at h
    exact h
  have hedge : m (x k) (x (k + 1)) ≠ 0 := by
    rcases hstep k with heq | hedge
    · have hi := hin k (by omega)
      have hdisj := disjoint_interiorCellVertices_sphere ε η z hr
      exact False.elim ((Set.disjoint_left.1 hdisj) (heq ▸ hi) hboundary)
    · exact hedge
  exact boundary_visit_before_exit_of_large_distance hε hm hη x k hin
    (hdiam _ (Or.inl (hin k (by omega)))) (hdiam _ (Or.inr hboundary))
    (hadj _ _ hedge) hfin hR hfar

end MatedCRT

#print axioms MatedCRT.first_boundary_visit_before_exit_of_large_distance
