import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.EnteringEdgeExit

/-! # The entering-edge alternative for large excursions -/

namespace MatedCRT

open Set Metric _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- If exit is far from the first boundary-cell representative, it occurs
strictly after the walk reaches that cell. The preceding cell and the
boundary cell are assumed to have diameter at most `d`. -/
theorem boundary_visit_before_exit_of_large_distance
    {ε mε d r R : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 ≤ ε) (hm : 0 < mε) (hη : Continuous η)
    (x : ℕ → ℤ) (k : ℕ)
    (hin : ∀ n < k + 1, x n ∈ interiorCellVertices ε η (ball z r))
    (ha : diam (cell ε η (x k)) ≤ d)
    (hb : diam (cell ε η (x (k + 1))) ≤ d)
    (hinter : (cell ε η (x k) ∩ cell ε η (x (k + 1))).Nonempty)
    (hfin : pathExitTime (ball z r) (interpolatedWalk ε η mε x) ≠ ⊤)
    (hR : 2 * d ≤ R)
    (hfar : R < dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
      (vertexPoint ε η (x (k + 1)))) :
    ((k + 1 : ℕ) : ℝ) ≤ mε *
      ((pathExitTime (ball z r) (interpolatedWalk ε η mε x)).toNNReal : ℝ) := by
  by_contra h
  have hτ : ((pathExitTime (ball z r) (interpolatedWalk ε η mε x)).toNNReal : ℝ≥0∞) =
      pathExitTime (ball z r) (interpolatedWalk ε η mε x) := ENNReal.coe_toNNReal hfin
  have hupper : pathExitTime (ball z r) (interpolatedWalk ε η mε x) ≤
      (((((k + 1 : ℕ) : ℝ) / mε).toNNReal : ℝ≥0) : ℝ≥0∞) := by
    rw [← hτ, ENNReal.coe_le_coe]
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) hm.le)]
    apply (le_div_iff₀ hm).2
    linarith
  have hdist := dist_pathExitPosition_le_two_diam_of_exit_on_entering_edge
    hε hm hη x k hin ha hb hinter hupper
  linarith

end MatedCRT

#print axioms MatedCRT.boundary_visit_before_exit_of_large_distance
