import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.EnlargedBoundaryExit
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BoundarySurvival

/-! # An excursion forces the outer annulus hit -/

namespace MatedCRT

open Set Metric _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- If the enlarged target boundary is hit first, all preceding vertices
stay in the outer disk, so the Euclidean exit location is within its radius
of the restart point. The target hit must be finite. -/
theorem dist_pathExitPosition_le_of_target_hit_before_outer
    {ε mε r R d : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 ≤ ε) (hm : 0 < mε) (hd : 0 < d) (hη : Continuous η)
    (x : ℕ → ℤ) (k : ℕ)
    (hlo : (k : ℝ) ≤ mε * ((pathExitTime (ball z r)
      (interpolatedWalk ε η mε x)).toNNReal : ℝ))
    (hdiam : ∀ a ∈ cellVertices ε η (sphere z (r + 3 * d)),
      diam (cell ε η a) ≤ d)
    (hfin : vHitTime (cellVertices ε η (sphere z (r + 3 * d)))
      (pathShift k x) ≠ ⊤)
    (horder : vHitTime (cellVertices ε η (sphere z (r + 3 * d)))
      (pathShift k x) < vHitTime
      (cellVertices ε η (sphere (vertexPoint ε η (x k)) R)) (pathShift k x))
    (hstay : ∀ n : ℕ, (n : ℕ∞) < vHitTime
      (cellVertices ε η (sphere (vertexPoint ε η (x k)) R)) (pathShift k x) →
      pathShift k x n ∈ interiorCellVertices ε η (ball (vertexPoint ε η (x k)) R)) :
    dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
      (vertexPoint ε η (x k)) ≤ R := by
  let A := cellVertices ε η (sphere z (r + 3 * d))
  let N := (vHitTime A (pathShift k x)).toNat
  have hN : vHitTime A (pathShift k x) = (N : ℕ∞) :=
    (ENat.natCast_toNat hfin).symm
  have hboundary : x (N + k) ∈ A := by
    have h := apply_vHitTime_mem_of_ne_top hfin
    simpa only [N, pathShift] using h
  apply dist_pathExitPosition_le_of_enlarged_boundary_visit hε hm hd hη x k N
    (hdiam _ hboundary) hboundary hlo
  intro n hn
  have hn' : (n : ℕ∞) < vHitTime
      (cellVertices ε η (sphere (vertexPoint ε η (x k)) R)) (pathShift k x) := by
    rw [hN] at horder
    exact (show (n : ℕ∞) ≤ (N : ℕ∞) by exact_mod_cast hn).trans_lt horder
  have hi := hstay n hn'
  have hp := Sec7.cell_subset_ball_of_mem_interiorCellVertices hη hi
    (Sec7.vertexPoint_mem_cell hε (pathShift k x n))
  exact mem_closedBall.mpr (mem_ball.mp hp).le

/-- A large excursion forces the outer annulus hit no later than the enlarged
boundary hit, provided the latter is finite and the walk remains in the outer
interior before its boundary hit. -/
theorem outer_hit_le_target_hit_of_large_excursion
    {ε mε r R d : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 ≤ ε) (hm : 0 < mε) (hd : 0 < d) (hη : Continuous η)
    (x : ℕ → ℤ) (k : ℕ)
    (hlo : (k : ℝ) ≤ mε * ((pathExitTime (ball z r)
      (interpolatedWalk ε η mε x)).toNNReal : ℝ))
    (hdiam : ∀ a ∈ cellVertices ε η (sphere z (r + 3 * d)),
      diam (cell ε η a) ≤ d)
    (hfin : vHitTime (cellVertices ε η (sphere z (r + 3 * d)))
      (pathShift k x) ≠ ⊤)
    (hstay : ∀ n : ℕ, (n : ℕ∞) < vHitTime
      (cellVertices ε η (sphere (vertexPoint ε η (x k)) R)) (pathShift k x) →
      pathShift k x n ∈ interiorCellVertices ε η (ball (vertexPoint ε η (x k)) R))
    (hfar : R < dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
      (vertexPoint ε η (x k))) :
    vHitTime (cellVertices ε η (sphere (vertexPoint ε η (x k)) R)) (pathShift k x) ≤
      vHitTime (cellVertices ε η (sphere z (r + 3 * d))) (pathShift k x) := by
  by_contra h
  exact (not_le_of_gt hfar) (dist_pathExitPosition_le_of_target_hit_before_outer
    hε hm hd hη x k hlo hdiam hfin (lt_of_not_ge h) hstay)

end MatedCRT

#print axioms MatedCRT.dist_pathExitPosition_le_of_target_hit_before_outer
#print axioms MatedCRT.outer_hit_le_target_hit_of_large_excursion
