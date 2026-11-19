import MatedCRT.FirstPass.Derived.BlockExitGridCellFrozenBridge
import MatedCRT.FirstPass.Derived.BlockExitWalkCloseDiagonal

/-!
# The frozen set of cells missing a ball, and one-step closeness from the diagonal estimate

Two deterministic ingredients of the walk-side block-exit estimates for the frozen set of closed
grid cells missing `ball 0 ρ₀`:

* `norm_le_of_notMem_ballFrozenSet`: the complement of the frozen set lies in the closed ball of
  radius `ρ₀ + 2 s`, hence has diameter at most `2 (ρ₀ + 2 s)`;
* `hclose_theta_of_hdiag`: if the walk restarted at a vertex `u` is `(δ, δ / 2)`-close to Brownian
  motion started at `v u`, exiting the block of the cell of `y`, for all `y` off `F` and vertices `u`
  within `θ` of `y`, with `24 θ / s ≤ δ / 2`, then the one-step closeness of the walk against the
  frozen block-exit kernel at tolerance `(δ, δ)` holds from the vertices within `θ` of points off `F`;
* `exists_theta_close`: such a `θ ∈ (0, s / 2]` exists for every `δ > 0`.
-/

open MeasureTheory Set Metric
open LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- **The complement of the union of closed cells missing `ball 0 ρ₀` lies in the closed ball of
radius `ρ₀ + 2 s`.** -/
theorem norm_le_of_notMem_ballFrozenSet {s : ℝ} (hs : 0 < s) (ρ₀ : ℝ) {y : ℂ}
    (hy : y ∉ ballFrozenSet s ρ₀) : ‖y‖ ≤ ρ₀ + 2 * s := by
  have hyc := mem_gridCellSet_cellIndex hs y
  have hnd : ¬ Disjoint (gridCellSet s (cellIndex s y)) (ball (0 : ℂ) ρ₀) := fun hd =>
    hy (by simp only [ballFrozenSet, mem_iUnion, exists_prop]; exact ⟨_, hd, hyc⟩)
  obtain ⟨p, hpc, hpb⟩ := Set.not_disjoint_iff.1 hnd
  rw [mem_ball_zero_iff] at hpb
  rcases hyc with ⟨h1, h2, h3, h4⟩
  rcases hpc with ⟨h5, h6, h7, h8⟩
  push_cast at h2 h4 h6 h8
  have hre : |y.re - p.re| ≤ s := by
    rw [abs_le]; constructor <;> nlinarith
  have him : |y.im - p.im| ≤ s := by
    rw [abs_le]; constructor <;> nlinarith
  have hyp : ‖y - p‖ ≤ 2 * s := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im]
    linarith
  have : ‖y‖ ≤ ‖p‖ + ‖y - p‖ := by
    have := norm_le_insert' y p
    linarith [norm_sub_rev y p]
  linarith

/-- **The complement of the frozen set of cells missing `ball 0 ρ₀` has diameter at most
`2 (ρ₀ + 2 s)`.** -/
theorem norm_sub_le_of_notMem_ballFrozenSet {s : ℝ} (hs : 0 < s) (ρ₀ : ℝ) {y z : ℂ}
    (hy : y ∉ ballFrozenSet s ρ₀) (hz : z ∉ ballFrozenSet s ρ₀) :
    ‖y - z‖ ≤ 2 * (ρ₀ + 2 * s) :=
  (norm_sub_le y z).trans (by
    linarith [norm_le_of_notMem_ballFrozenSet hs ρ₀ hy, norm_le_of_notMem_ballFrozenSet hs ρ₀ hz])

/-- **One-step closeness from the diagonal estimate.** If the next block-exit position of the walk
restarted at `u` is `(δ, δ / 2)`-close to the exit point, from the block of the cell of `y`, of
Brownian motion started at `v u`, for all `y ∉ F` and `u` with `dist (v u) y ≤ θ`, and
`24 θ / s ≤ δ / 2`, then it is `(δ, δ)`-close to the block-exit kernel frozen on `F` at `y`. -/
theorem hclose_theta_of_hdiag (m : ℤ → ℤ → ℕ) (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) {s : ℝ}
    (hs : 0 < s) {F : Set ℂ} (hF : MeasurableSet F) {δ θ : ℝ} (hδ : 0 ≤ δ)
    (hθ : 24 * θ / s ≤ δ / 2)
    (hdiag : ∀ y ∉ F, ∀ u : ℤ, dist (v u) y ≤ θ →
      LatticeProb.ProkhorovLE (walkNextBlockExitKernel m v hc s F (y, u))
        (blockExitKernel s (cellIndex s y) (v u)) δ (δ / 2)) :
    ∀ y ∉ F, ∀ u : ℤ, dist (v u) y ≤ θ →
      LatticeProb.ProkhorovLE (walkNextBlockExitKernel m v hc s F (y, u))
        (frozenBlockExitKernel s hF y) δ δ := by
  intro y hy u hu A hA
  have h := prokhorovLE_walkNextBlockExitKernel_of_diagonal m v hc hs hF (by linarith : 0 ≤ δ / 2) hdiag
    y hy u hu A hA
  exact h.trans (add_le_add_right (by gcongr; linarith) _)

/-- **A scale `θ ∈ (0, s / 2]` with `24 θ / s ≤ δ / 2` exists for every `δ > 0`.** -/
theorem exists_theta_close {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ s / 2 ∧ 24 * θ / s ≤ δ / 2 := by
  refine ⟨min (s / 2) (δ * s / 48), lt_min (by positivity) (by positivity), min_le_left _ _, ?_⟩
  have h : min (s / 2) (δ * s / 48) ≤ δ * s / 48 := min_le_right _ _
  rw [div_le_iff₀ hs]
  linarith

end BlockExit

end MatedCRT
