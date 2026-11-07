import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.EnteringEdge

/-! # Euclidean exit on the boundary-cell entering edge -/

namespace MatedCRT

open Set Metric _root_.HarmonicBalls
open scoped NNReal ENNReal

/-- If the Euclidean exit happens no later than the first boundary-cell
visit, it lies on the entering edge and is at most twice the cell-diameter
bound from that boundary cell's representative. -/
theorem dist_pathExitPosition_le_two_diam_of_exit_on_entering_edge
    {ε mε d r : ℝ} (hε : 0 ≤ ε) (hm : 0 < mε) {η : ℝ → ℂ}
    (hη : Continuous η) {z : ℂ} (x : ℕ → ℤ) (k : ℕ)
    (hin : ∀ n < k + 1, x n ∈ interiorCellVertices ε η (ball z r))
    (ha : diam (cell ε η (x k)) ≤ d)
    (hb : diam (cell ε η (x (k + 1))) ≤ d)
    (hinter : (cell ε η (x k) ∩ cell ε η (x (k + 1))).Nonempty)
    (hupper : pathExitTime (ball z r) (interpolatedWalk ε η mε x) ≤
      (((((k + 1 : ℕ) : ℝ) / mε).toNNReal : ℝ≥0) : ℝ≥0∞)) :
    dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
      (vertexPoint ε η (x (k + 1))) ≤ 2 * d := by
  let τ := pathExitTime (ball z r) (interpolatedWalk ε η mε x)
  have hfin : τ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hupper
  have hτ : (τ.toNNReal : ℝ≥0∞) = τ := ENNReal.coe_toNNReal hfin
  have hlow := le_pathExitTime_interpolatedWalk hε hm hη (N := k + 1)
    (by omega) hin (z := z) (r := r)
  have hlo' : (((k : ℝ) / mε).toNNReal : ℝ≥0) ≤ τ.toNNReal := by
    apply ENNReal.coe_le_coe.mp
    simpa only [Nat.add_sub_cancel, hτ] using hlow
  have hhi' : τ.toNNReal ≤ ((((k + 1 : ℕ) : ℝ) / mε).toNNReal : ℝ≥0) := by
    apply ENNReal.coe_le_coe.mp
    simpa only [hτ] using hupper
  have hlo : (k : ℝ) ≤ mε * (τ.toNNReal : ℝ) := by
    have h := NNReal.coe_le_coe.mpr hlo'
    rw [Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) hm.le)] at h
    exact (div_le_iff₀ hm).mp h |>.trans_eq (mul_comm _ _)
  have hhi : mε * (τ.toNNReal : ℝ) ≤ (k + 1 : ℕ) := by
    have h := NNReal.coe_le_coe.mpr hhi'
    rw [Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) hm.le)] at h
    have h' := (le_div_iff₀ hm).mp h
    linarith
  change dist (interpolatedWalk ε η mε x τ.toNNReal) _ ≤ _
  exact dist_interpolatedWalk_le_two_diam_on_edge hε hm hη x k ha hb hinter hlo hhi

/-- In particular, the entering-edge estimate applies when the first
boundary-cell representative has already left the disk. -/
theorem dist_pathExitPosition_le_two_diam_of_boundary_representative_outside
    {ε mε d r : ℝ} (hε : 0 ≤ ε) (hm : 0 < mε) {η : ℝ → ℂ}
    (hη : Continuous η) {z : ℂ} (x : ℕ → ℤ) (k : ℕ)
    (hin : ∀ n < k + 1, x n ∈ interiorCellVertices ε η (ball z r))
    (ha : diam (cell ε η (x k)) ≤ d)
    (hb : diam (cell ε η (x (k + 1))) ≤ d)
    (hinter : (cell ε η (x k) ∩ cell ε η (x (k + 1))).Nonempty)
    (hout : vertexPoint ε η (x (k + 1)) ∉ ball z r) :
    dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x))
      (vertexPoint ε η (x (k + 1))) ≤ 2 * d := by
  apply dist_pathExitPosition_le_two_diam_of_exit_on_entering_edge
    hε hm hη x k hin ha hb hinter
  unfold pathExitTime
  apply sInf_le
  refine ⟨_, rfl, ?_⟩
  rw [interpolatedWalk_natCast_div hm]
  exact hout

end MatedCRT

#print axioms MatedCRT.dist_pathExitPosition_le_two_diam_of_exit_on_entering_edge
#print axioms MatedCRT.dist_pathExitPosition_le_two_diam_of_boundary_representative_outside
