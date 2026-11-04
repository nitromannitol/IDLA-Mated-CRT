import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.GreenSumBump

/-! # Rescaled near-pole comparison -/

namespace MatedCRT

open Set Metric Filter Topology

/-- The difference between the rescaled normalized exit time and its
truncated Green sum is nonnegative and bounded by the rescaled solution of
the buffered bump Dirichlet problem. -/
theorem rescaledExitTime_sub_truncated_le_bump
    {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {ε M : ℝ} (hε : 0 < ε)
    (hM : 0 ≤ M) (z y : ℂ) (r δ d : ℝ) (m : ℤ → ℤ → ℕ)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (φ : ℂ → ℝ) (u : ℤ → ℝ)
    (hdiam : ∀ b ∈ interiorCellVertices ε η (ball z r) ∩
      cellVertices ε η (ball y δ), diam (cell ε η b) ≤ d)
    (hone : ∀ x ∈ ball y (δ + d), φ x = 1)
    (hφ0 : ∀ b ∈ interiorCellVertices ε η (ball z r),
      0 ≤ φ (vertexPoint ε η b))
    (hu0 : ∀ b ∉ interiorCellVertices ε η (ball z r), u b = 0)
    (hu : ∀ b ∈ interiorCellVertices ε η (ball z r),
      mLaplacian m u b = -φ (vertexPoint ε η b)) :
    0 ≤ rescale M ε η (normExitTime m (interiorCellVertices ε η (ball z r))) y -
      M⁻¹ * ∑ b ∈ truncatedGreenCells ε η z y r δ,
        greenKernel m (interiorCellVertices ε η (ball z r)) (vertexOf ε η y) b ∧
    rescale M ε η (normExitTime m (interiorCellVertices ε η (ball z r))) y -
      M⁻¹ * ∑ b ∈ truncatedGreenCells ε η z y r δ,
        greenKernel m (interiorCellVertices ε η (ball z r)) (vertexOf ε η y) b ≤
      rescale M ε η u y := by
  classical
  let A := interiorCellVertices ε η (ball z r)
  have hA : A.Finite := (Tightness.cellVertices_finite hη hp hε isBounded_ball).subset
    (by intro b hb; exact hb.1)
  obtain ⟨N, hN, hsplit⟩ := normExitTime_eq_truncated_add_near hη hp hε z y r δ m
    (vertexOf ε η y)
  have hNA : N ⊆ hA.toFinset := by
    intro b hb
    exact hA.mem_toFinset.mpr ((Set.ext_iff.mp hN b).mp hb).1
  have hnear : ∀ b ∈ N, b ∈ cellVertices ε η (ball y δ) := by
    intro b hb
    exact ((Set.ext_iff.mp hN b).mp hb).2
  have hdiam' : ∀ b ∈ N, diam (cell ε η b) ≤ d := by
    intro b hb
    exact hdiam b ((Set.ext_iff.mp hN b).mp hb)
  have hbound := greenSum_near_le_dirichlet_solution hη hε.le m hlf hcons A hA
    N (vertexOf ε η y) φ u hNA hnear hdiam' hone
    (fun b hb => hφ0 b (hA.mem_toFinset.mp hb)) hu0 hu
  have hnonneg : 0 ≤ ∑ b ∈ N, greenKernel m A (vertexOf ε η y) b := by
    exact Finset.sum_nonneg (fun b _ => Sec7.greenKernel_nonneg m A _ b)
  have hmul := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hM)
  have hmul0 := mul_nonneg (inv_nonneg.mpr hM) hnonneg
  unfold rescale
  rw [hsplit]
  constructor <;> nlinarith

end MatedCRT
