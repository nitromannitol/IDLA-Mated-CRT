import MatedCRT.FirstPass.S6j.ExitTailUpperWalk

/-!
# Walk side of the upper tail of the exit time, for the full cell sets (BG20 Lemma 6.10, estimate (6.50))

The variant of `ExitTailUpperWalk.chain_of_not_exit_le` for the exit time from the cells meeting `B_{r₁}(0)`,
`V^ε(B_{r₁}(0))`, and the successive exits `σ_k` from the cells meeting the balls `B_δ(η(ε w_{σ_{k-1}}))`,
`V^ε(B_δ(η(ε w_{σ_{k-1}})))` (not the interior cells).  On the event that the walk makes `K` successive exits
before leaving `V^ε(B_{r₁}(0))`, the interpolated walk stays in `B_{r₁ + c}(0)` up to `σ_K`, agrees there with the
walk stopped at its exit from `B_R(0)`, and the chain of exit times is nondecreasing with
`|f(τ_{k+1}) - f(τ_k)| ≥ δ`: the vertex reached at the `(k+1)`-st exit has a cell that misses the ball, so it is
embedded outside the ball.
-/

set_option autoImplicit false

namespace MatedCRT.ExitTailUpperWalkV

open Set Metric SuccessiveExitGaps WalkDisplacementBlocks MatedCRT.ExitTailUpperWalk
open scoped ENNReal NNReal

variable {ε : ℝ} {η : ℝ → ℂ}

/-- A vertex which is not a cell vertex of `B_δ(v)` (its cell misses the ball) is embedded at distance at least `δ`
from `v`. -/
theorem le_dist_of_notMem_cellVertices (hε : 0 ≤ ε) {v : ℂ} {δ : ℝ} {y : ℤ}
    (hy : y ∉ cellVertices ε η (ball v δ)) : δ ≤ dist (vertexPoint ε η y) v := by
  have hvp : vertexPoint ε η y ∈ cell ε η y := TruncatedLaws.vertexPoint_mem_cell_of_nonneg hε y
  by_contra hlt
  rw [not_le] at hlt
  exact hy (show (cell ε η y ∩ ball v δ).Nonempty from ⟨_, hvp, mem_ball.2 hlt⟩)

/-- **Walk side of Berestycki-Gwynne Lemma 6.10, full cell sets.** On the event that the walk makes `K` successive
exits from the regions `V^ε(B_δ(η(ε ·)))` before leaving `V^ε(B_{r₁}(0))`, the interpolated walk `f` (i) stays in
`B_{r₁ + c}(0)` up to `σ_K`, (ii) agrees there with the walk stopped at its exit from `B_R(0)`, and (iii) the chain
`τ_k` is nondecreasing with `|f(τ_{k+1}) - f(τ_k)| ≥ δ`. -/
theorem chain_of_not_exit_le_V (hε : 0 ≤ ε) (hη : Continuous η) {R r₁ c δ : ℝ} (hr₁ : r₁ ≤ R)
    (hrc : r₁ + c ≤ R)
    (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) R).Nonempty → diam (cell ε η k) ≤ c) {w : ℕ → ℤ} {K : ℕ}
    (hbad : ¬ vExitTime (cellVertices ε η (ball (0 : ℂ) r₁)) w ≤
      succExit (fun z => cellVertices ε η (ball (vertexPoint ε η z) δ)) K w) :
    let A : ℤ → Set ℤ := fun z => cellVertices ε η (ball (vertexPoint ε η z) δ)
    (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ chainTime A K w K → ‖interpolatedWalk ε η 1 w t‖ < r₁ + c) ∧
    (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ chainTime A K w K →
      stopAtExit (ball (0 : ℂ) R) (interpolatedWalk ε η 1 w) t = interpolatedWalk ε η 1 w t) ∧
    (∀ k, chainTime A K w k ≤ chainTime A K w (k + 1)) ∧
    (∀ (k : ℕ) (s t : ℝ≥0), chainTime A K w k = s → chainTime A K w (k + 1) = t →
      δ ≤ ‖interpolatedWalk ε η 1 w t - interpolatedWalk ε η 1 w s‖) := by
  intro A
  have hlt : succExit A K w < vExitTime (cellVertices ε η (ball (0 : ℂ) r₁)) w := not_le.1 hbad
  have hne : succExit A K w ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hne
  have hmem : ∀ j ≤ N, w j ∈ cellVertices ε η (ball (0 : ℂ) r₁) := fun j hj =>
    WindowStop68.mem_of_lt_vExitTime
      (lt_of_le_of_lt (by rw [← hN]; exact_mod_cast hj : (j : ℕ∞) ≤ succExit A K w) hlt)
  have hdiam : ∀ j ≤ N, ‖vertexPoint ε η (w j)‖ < r₁ + c := by
    intro j hj
    obtain ⟨y, hyc, hyb⟩ := hmem j hj
    have hd : diam (cell ε η (w j)) ≤ c := hcell _ ⟨y, hyc, ball_subset_ball hr₁ hyb⟩
    have := dist_vertexPoint_lt_of_mem_cellVertices hε hη (z := (0 : ℂ)) (hmem j hj) hd
    rwa [dist_zero_right] at this
  have hvball : ∀ j ≤ N, vertexPoint ε η (w j) ∈ ball (0 : ℂ) (r₁ + c) := fun j hj => by
    rw [mem_ball_zero_iff]
    exact hdiam j hj
  have hcT : chainTime A K w K = (N : ℝ≥0∞) := by
    simp only [chainTime, le_refl, ↓reduceIte]
    rw [← hN, ENat.toENNReal_coe]
  have hstay : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ chainTime A K w K →
      interpolatedWalk ε η 1 w t ∈ ball (0 : ℂ) (r₁ + c) := by
    intro t ht
    rw [hcT] at ht
    have : (t : ℝ) ≤ N := by exact_mod_cast ht
    exact interpolatedWalk_mem_of_vertices_mem (convex_ball _ _) hvball this
  refine ⟨fun t ht => mem_ball_zero_iff.1 (hstay t ht), ?_, chainTime_mono A K w, ?_⟩
  · intro t ht
    refine stopAtExit_of_coe_le ?_
    refine le_sInf ?_
    rintro s ⟨t', rfl, hout⟩
    by_contra hlt'
    have hlt'' : t' < t := by exact_mod_cast not_le.1 hlt'
    exact hout (ball_subset_ball hrc (hstay t' ((ENNReal.coe_le_coe.2 hlt''.le).trans ht)))
  · intro k s t hs ht
    have hk1 : k + 1 ≤ K := by
      by_contra hk1
      simp only [chainTime, hk1, ↓reduceIte] at ht
      exact ENNReal.top_ne_coe ht
    obtain ⟨j, hj, hjs⟩ := exists_succExit_eq_of_chainTime_eq (by omega) hs
    obtain ⟨m, hm, hmt⟩ := exists_succExit_eq_of_chainTime_eq hk1 ht
    have hfs : interpolatedWalk ε η 1 w s = vertexPoint ε η (w j) := interpolatedWalk_one_of_coe_eq w hjs
    have hft : interpolatedWalk ε η 1 w t = vertexPoint ε η (w m) := interpolatedWalk_one_of_coe_eq w hmt
    have hout : w m ∉ A (w j) := notMem_of_succExit_succ hj hm
    have := le_dist_of_notMem_cellVertices hε hout
    rw [hfs, hft, ← dist_eq_norm]
    exact this

end MatedCRT.ExitTailUpperWalkV
