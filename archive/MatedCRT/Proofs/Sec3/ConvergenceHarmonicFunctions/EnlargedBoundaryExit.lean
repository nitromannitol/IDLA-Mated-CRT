import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.EnteringEdgeExit
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ShiftInterpolation

/-! # Euclidean exit before the enlarged boundary-cell hit -/

namespace MatedCRT

open Set Metric _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- A cell meeting the boundary of the original disk lies in the disk enlarged
by three cell diameters, and its representative is within four diameters of
that enlarged disk's boundary in the radial sense. -/
theorem boundary_cell_in_enlarged_disk
    {ε r d : ℝ} {η : ℝ → ℂ} {z : ℂ} {a : ℤ}
    (hε : 0 ≤ ε) (hd : 0 < d) (hη : Continuous η)
    (hdiam : diam (cell ε η a) ≤ d)
    (ha : a ∈ cellVertices ε η (sphere z r)) :
    cell ε η a ⊆ ball z (r + 3 * d) ∧
      r - d ≤ dist (vertexPoint ε η a) z ∧
      dist (vertexPoint ε η a) z ≤ r + d := by
  obtain ⟨q, hq, hnear, hsub⟩ :=
    boundary_cell_near_and_subset_enlarged_ball hε hη (show d < 3 * d by linarith)
      hdiam ha
  refine ⟨hsub, boundary_cell_representative_distance_lower hε hη hdiam ha, ?_⟩
  have hqz : dist q z = r := by simpa [dist_comm] using (mem_sphere.mp hq)
  have ht := dist_triangle (vertexPoint ε η a) q z
  linarith

/-- At a visit to a cell meeting the boundary of the disk enlarged by `3d`,
the interpolated walk has already exited the original disk. -/
theorem pathExitTime_le_of_enlarged_boundary_visit
    {ε mε r d : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 ≤ ε) (hm : 0 < mε) (hd : 0 < d) (hη : Continuous η)
    (x : ℕ → ℤ) (n : ℕ)
    (hdiam : diam (cell ε η (x n)) ≤ d)
    (hboundary : x n ∈ cellVertices ε η (sphere z (r + 3 * d))) :
    pathExitTime (ball z r) (interpolatedWalk ε η mε x) ≤
      (((((n : ℕ) : ℝ) / mε).toNNReal : ℝ≥0) : ℝ≥0∞) := by
  have hdist := boundary_cell_representative_distance_lower hε hη hdiam hboundary
  unfold pathExitTime
  apply sInf_le
  refine ⟨_, rfl, ?_⟩
  rw [interpolatedWalk_natCast_div hm]
  intro hin
  have hin' := mem_ball.mp hin
  linarith

/-- Once Euclidean exit occurs between a restart and a later step, bounds on
all intervening representatives bound the displacement of its exit position
from the restart representative. -/
theorem dist_pathExitPosition_le_of_restarted_representatives
    {ε mε r R : ℝ} {η : ℝ → ℂ} {z : ℂ} (hm : 0 < mε)
    (x : ℕ → ℤ) (k N : ℕ)
    (hlo : (k : ℝ) ≤ mε * ((pathExitTime (ball z r)
      (interpolatedWalk ε η mε x)).toNNReal : ℝ))
    (hhi : mε * ((pathExitTime (ball z r)
      (interpolatedWalk ε η mε x)).toNNReal : ℝ) ≤ (k : ℝ) + N)
    (hin : ∀ n ≤ N, vertexPoint ε η (x (n + k)) ∈
      closedBall (vertexPoint ε η (x k)) R) :
    dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
      (vertexPoint ε η (x k)) ≤ R := by
  let τ := (pathExitTime (ball z r) (interpolatedWalk ε η mε x)).toNNReal
  let tk : ℝ≥0 := ((k : ℝ) / mε).toNNReal
  have htk : (tk : ℝ) = (k : ℝ) / mε :=
    Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) hm.le)
  have htkτ : tk ≤ τ := by
    apply NNReal.coe_le_coe.mp
    rw [htk, div_le_iff₀ hm]
    linarith
  have hsub : ((τ - tk : ℝ≥0) : ℝ) = (τ : ℝ) - (tk : ℝ) := by
    exact NNReal.coe_sub htkτ
  have htime : mε * ((τ - tk : ℝ≥0) : ℝ) ≤ (N : ℝ) := by
    rw [hsub, htk]
    have heq : mε * ((k : ℝ) / mε) = k := mul_div_cancel₀ _ hm.ne'
    nlinarith
  have h := interpolatedWalk_mem_closedBall_after_shift hm k N hin htime
  rw [tsub_add_cancel_of_le htkτ] at h
  exact mem_closedBall.mp h

/-- If the enlarged boundary is visited after the restart, then an exit
occurring after the restart remains in any closed disk containing all the
intervening walk representatives. -/
theorem dist_pathExitPosition_le_of_enlarged_boundary_visit
    {ε mε r R d : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 ≤ ε) (hm : 0 < mε) (hd : 0 < d) (hη : Continuous η)
    (x : ℕ → ℤ) (k N : ℕ)
    (hdiam : diam (cell ε η (x (N + k))) ≤ d)
    (hboundary : x (N + k) ∈ cellVertices ε η (sphere z (r + 3 * d)))
    (hlo : (k : ℝ) ≤ mε * ((pathExitTime (ball z r)
      (interpolatedWalk ε η mε x)).toNNReal : ℝ))
    (hin : ∀ n ≤ N, vertexPoint ε η (x (n + k)) ∈
      closedBall (vertexPoint ε η (x k)) R) :
    dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
      (vertexPoint ε η (x k)) ≤ R := by
  have hupper := pathExitTime_le_of_enlarged_boundary_visit hε hm hd hη x (N + k)
    hdiam hboundary
  have hfin : pathExitTime (ball z r) (interpolatedWalk ε η mε x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hupper
  have hτ : (((pathExitTime (ball z r) (interpolatedWalk ε η mε x)).toNNReal : ℝ≥0) : ℝ≥0∞) =
      pathExitTime (ball z r) (interpolatedWalk ε η mε x) := ENNReal.coe_toNNReal hfin
  have ht := ENNReal.coe_le_coe.mp (hτ ▸ hupper)
  have ht' := NNReal.coe_le_coe.mpr ht
  rw [Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) hm.le)] at ht'
  have hhi : mε * ((pathExitTime (ball z r) (interpolatedWalk ε η mε x)).toNNReal : ℝ) ≤
      (k : ℝ) + N := by
    have hh := (le_div_iff₀ hm).mp ht'
    rw [Nat.cast_add] at hh
    linarith
  exact dist_pathExitPosition_le_of_restarted_representatives hm x k N hlo hhi hin

end MatedCRT

#print axioms MatedCRT.boundary_cell_in_enlarged_disk
#print axioms MatedCRT.pathExitTime_le_of_enlarged_boundary_visit
#print axioms MatedCRT.dist_pathExitPosition_le_of_restarted_representatives
#print axioms MatedCRT.dist_pathExitPosition_le_of_enlarged_boundary_visit
