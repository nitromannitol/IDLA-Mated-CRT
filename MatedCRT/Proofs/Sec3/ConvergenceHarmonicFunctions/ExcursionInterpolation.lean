import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellWindow
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BoundaryCellGeometry

/-! # Controlling an interpolated excursion by its vertices -/

namespace MatedCRT

open Set Metric
open scoped NNReal

/-- If all representatives through a step lie in a closed disk, then the
straight-line interpolation stays in that disk through that step. -/
theorem interpolatedWalk_mem_closedBall_of_le
    {ε mε : ℝ} (hm : 0 < mε) {η : ℝ → ℂ} {z : ℂ} {R : ℝ}
    {x : ℕ → ℤ} {N : ℕ}
    (hin : ∀ n ≤ N, vertexPoint ε η (x n) ∈ closedBall z R)
    {t : ℝ≥0} (ht : mε * (t : ℝ) ≤ (N : ℝ)) :
    interpolatedWalk ε η mε x t ∈ closedBall z R := by
  have h0 : 0 ≤ mε * (t : ℝ) := mul_nonneg hm.le t.2
  have hfl := Nat.floor_le h0
  have hnN : ⌊mε * (t : ℝ)⌋₊ ≤ N := by
    exact_mod_cast hfl.trans ht
  simp only [interpolatedWalk]
  rcases eq_or_lt_of_le (sub_nonneg.2 hfl) with hθ | hθ
  · rw [← hθ, sub_zero, Complex.ofReal_zero, Complex.ofReal_one, one_mul, zero_mul, add_zero]
    exact hin _ hnN
  · have hnN' : ⌊mε * (t : ℝ)⌋₊ + 1 ≤ N := by
      have hlt : (⌊mε * (t : ℝ)⌋₊ : ℝ) < (N : ℝ) := by linarith
      have hnat : ⌊mε * (t : ℝ)⌋₊ < N := by exact_mod_cast hlt
      omega
    have hlt := Nat.lt_floor_add_one (mε * (t : ℝ))
    have hc := convex_closedBall z R (hin _ hnN) (hin _ hnN') (by linarith : (0 : ℝ) ≤
      1 - (mε * (t : ℝ) - ⌊mε * (t : ℝ)⌋₊)) hθ.le (by ring)
    simpa only [Complex.real_smul] using hc

/-- Before the first boundary-cell hit, the walk is in interior cells; the
hit cell extends the representative bound by at most its diameter. -/
theorem interpolatedWalk_mem_closedBall_until_boundary_cell
    {ε mε r d : ℝ} (hε : 0 ≤ ε) (hm : 0 < mε) {η : ℝ → ℂ}
    (hη : Continuous η) {z : ℂ} {x : ℕ → ℤ} {N : ℕ}
    (hin : ∀ n < N, x n ∈ interiorCellVertices ε η (ball z r))
    (hboundary : x N ∈ cellVertices ε η (sphere z r))
    (hdiam : diam (cell ε η (x N)) ≤ d)
    {t : ℝ≥0} (ht : mε * (t : ℝ) ≤ (N : ℝ)) :
    interpolatedWalk ε η mε x t ∈ closedBall z (r + d) := by
  apply interpolatedWalk_mem_closedBall_of_le hm (N := N) ?_ ht
  intro n hn
  have hd : 0 ≤ d := (diam_nonneg).trans hdiam
  rcases lt_or_eq_of_le hn with hlt | rfl
  · have hmem := Sec7.cell_subset_ball_of_mem_interiorCellVertices hη (hin n hlt)
      (Sec7.vertexPoint_mem_cell hε (x n))
    exact mem_closedBall.mpr (le_trans (le_of_lt (mem_ball.mp hmem)) (by linarith))
  · obtain ⟨q, hq, hnear, _⟩ :=
      boundary_cell_near_and_subset_enlarged_ball hε hη (show d < d + 1 by linarith)
        hdiam hboundary
    have hqz : dist q z = r := by simpa [dist_comm] using (mem_sphere.mp hq)
    apply mem_closedBall.mpr
    have ht := dist_triangle (vertexPoint ε η (x n)) q z
    linarith

end MatedCRT

#print axioms MatedCRT.interpolatedWalk_mem_closedBall_of_le
#print axioms MatedCRT.interpolatedWalk_mem_closedBall_until_boundary_cell
