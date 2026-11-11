import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PrehitInterior

/-! # The restart cell is interior to a larger Euclidean ball -/

namespace MatedCRT

open Set Metric _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- A cell of diameter smaller than the radius is an interior cell of the
ball centered at its representative. -/
theorem restart_cell_mem_interior_ball
    {ε R : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε) (hη : Continuous η)
    (a : ℤ) (hR : 0 < R) (hdiam : diam (cell ε η a) < R) :
    a ∈ interiorCellVertices ε η (ball (vertexPoint ε η a) R) := by
  have hp : vertexPoint ε η a ∈ cell ε η a := Sec7.vertexPoint_mem_cell hε a
  refine ⟨⟨vertexPoint ε η a, hp, mem_ball_self hR⟩, ?_⟩
  rintro ⟨z, hz, hfront⟩
  have hs : dist z (vertexPoint ε η a) = R :=
    mem_sphere.1 (frontier_ball_subset_sphere hfront)
  have hdist := dist_le_diam_of_mem (Sec7.cell_isBounded hη a) hz hp
  linarith

/-- A small restart cell supplies the interior hypothesis in the
large-excursion hit-order implication. -/
theorem outer_hit_le_target_hit_of_large_excursion_of_small_restart_cell
    {ε mε r R d : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 ≤ ε) (hm : 0 < mε) (hd : 0 < d) (hη : Continuous η)
    (m : ℤ → ℤ → ℕ) (x : ℕ → ℤ) (k : ℕ)
    (hR : 0 < R) (hsmall : diam (cell ε η (x k)) < R)
    (hstep : ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)
    (hnb : ∀ v ∈ interiorCellVertices ε η (ball (vertexPoint ε η (x k)) R),
      ∀ w, m v w ≠ 0 → w ∈ interiorCellVertices ε η (ball (vertexPoint ε η (x k)) R) ∪
        cellVertices ε η (sphere (vertexPoint ε η (x k)) R))
    (hlo : (k : ℝ) ≤ mε * ((pathExitTime (ball z r)
      (interpolatedWalk ε η mε x)).toNNReal : ℝ))
    (hdiam : ∀ a ∈ cellVertices ε η (sphere z (r + 3 * d)),
      diam (cell ε η a) ≤ d)
    (hfin : vHitTime (cellVertices ε η (sphere z (r + 3 * d)))
      (pathShift k x) ≠ ⊤)
    (hfar : R < dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
      (vertexPoint ε η (x k))) :
    vHitTime (cellVertices ε η (sphere (vertexPoint ε η (x k)) R)) (pathShift k x) ≤
      vHitTime (cellVertices ε η (sphere z (r + 3 * d))) (pathShift k x) := by
  exact outer_hit_le_target_hit_of_large_excursion_of_neighbours hε hm hd hη m x k
    (restart_cell_mem_interior_ball hε hη (x k) hR hsmall) hstep hnb hlo hdiam hfin hfar

end MatedCRT

#print axioms MatedCRT.restart_cell_mem_interior_ball
#print axioms MatedCRT.outer_hit_le_target_hit_of_large_excursion_of_small_restart_cell
