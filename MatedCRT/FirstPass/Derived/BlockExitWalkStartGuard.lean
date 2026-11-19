import MatedCRT.FirstPass.Derived.BlockExitWalkCompProd
import MatedCRT.FirstPass.Derived.BlockExitSkeletonPath

/-!
# The start of the exit edge is near the complement of the frozen set

For the linear interpolation of a walk, the `n`-th block-exit position `Y_n = X(σ_n)` lies on the edge
segment between `v x_k` and `v x_{k+1}`, `k = ⌊c σ_n⌋`. If `Fᶜ` lies in the ball of radius `B₀` and
`Y_n ∉ F`, the starting vertex of this edge satisfies `‖v x_k‖ ≤ B₀ + 4 s`: before the `n`-th block
exit the path is within `4 s` of an earlier block-exit position, and these are off `F` by freezing.
Hence the exit-position estimate of the walk needs the edge-length bound only for edges
**starting** at vertices in the ball of radius `B₀ + 4 s`.

## Main results

* `norm_vertex_walkBlockExitStepStart_le`: `‖v x_k‖ ≤ B₀ + 4 s`.
* `dist_walkBlockExitStepPos_le_of_localEdges`: the pathwise bound of
  `dist_walkBlockExitStepPos_le`, with the edge-length hypothesis only for edges starting in the ball.
-/

open MeasureTheory Set Metric MarkovProcess Filter
open scoped ENNReal NNReal Topology
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open WalkPotential

/-- **The starting vertex of the exit edge lies in the ball of radius `B₀ + 4 s`.** -/
theorem norm_vertex_walkBlockExitStepStart_le (v : ℤ → ℂ) {c : ℝ} (hc : 0 < c) {s : ℝ}
    (hs : 0 < s) {F : Set ℂ} {B₀ : ℝ} (hFB : ∀ y ∉ F, ‖y‖ ≤ B₀) (n : ℕ) (x : ℕ → ℤ)
    (hYF : interpPathCM v hc.le x (blockExitTimes s F n (interpPathCM v hc.le x)) ∉ F) :
    ‖v (x ⌊c * (blockExitTimes s F n (interpPathCM v hc.le x) : ℝ)⌋₊)‖ ≤ B₀ + 4 * s := by
  set ω := interpPathCM v hc.le x with hω
  set k := ⌊c * (blockExitTimes s F n ω : ℝ)⌋₊ with hk
  have hnn : 0 ≤ c * (blockExitTimes s F n ω : ℝ) := mul_nonneg hc.le (NNReal.coe_nonneg _)
  have hvk : v (x k) = ω ((k : ℝ≥0) / c.toNNReal) := (interpPathCM_natCast_div hc x k).symm
  have hle : ((k : ℝ≥0) / c.toNNReal) ≤ blockExitTimes s F n ω := by
    have hpos : 0 < c.toNNReal := Real.toNNReal_pos.2 hc
    rw [div_le_iff₀ hpos, ← NNReal.coe_le_coe]
    push_cast
    rw [Real.coe_toNNReal _ hc.le]
    linarith [Nat.floor_le hnn]
  have hs4 : 0 ≤ 4 * s := by positivity
  rw [hvk]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have ht0 : ((k : ℝ≥0) / c.toNNReal) = 0 :=
      le_antisymm (by simpa [blockExitTimes_zero] using hle) zero_le
    rw [ht0]
    have hY0 : ω 0 ∉ F := by simpa [blockExitTimes_zero] using hYF
    linarith [hFB _ hY0]
  · obtain ⟨j, hjn, hj⟩ := exists_norm_sub_le_of_le_blockExitTimes hs F n ω hle hpos
    have hjF : ω (blockExitTimes s F j ω) ∉ F := fun hmem =>
      hYF (by rw [blockExitTimes_eq_of_mem s hmem n hjn.le]; exact hmem)
    calc ‖ω ((k : ℝ≥0) / c.toNNReal)‖
        ≤ ‖ω (blockExitTimes s F j ω)‖ + ‖ω ((k : ℝ≥0) / c.toNNReal) - ω (blockExitTimes s F j ω)‖ := by
          have := norm_add_le (ω (blockExitTimes s F j ω))
            (ω ((k : ℝ≥0) / c.toNNReal) - ω (blockExitTimes s F j ω))
          simpa using this
      _ ≤ B₀ + 4 * s := add_le_add (hFB _ hjF) hj

/-- **Pathwise: the walk position after the `n`-th block exit is within `θ` of `Y_n`, with the
edge-length bound only for edges starting in the ball of radius `B₀ + 4 s`.** If `τ_n < ∞`, every
step of `x` is a loop or an edge of `m`, `Y_n ∉ F`, `Fᶜ ⊆ closedBall 0 B₀`, and every edge that starts at a
vertex of norm at most `B₀ + 4 s` and whose segment meets `Fᶜ` has length at most `θ`, then
`dist (v x_{τ_n}) Y_n ≤ θ`. -/
theorem dist_walkBlockExitStepPos_le_of_localEdges (m : ℤ → ℤ → ℕ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 < c) {s : ℝ} (hs : 0 < s) {θ : ℝ} (hθ : 0 ≤ θ) {F : Set ℂ} {B₀ : ℝ}
    (hFB : ∀ y ∉ F, ‖y‖ ≤ B₀)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 → ‖v b‖ ≤ B₀ + 4 * s →
      (∃ z ∈ segment ℝ (v b) (v b'), z ∉ F) → dist (v b) (v b') ≤ θ)
    (n : ℕ) {x : ℕ → ℤ} (hτ : walkBlockExitStepTime v hc.le s F n x ≠ ⊤)
    (hadj : ∀ k : ℕ, x (k + 1) = x k ∨ m (x k) (x (k + 1)) ≠ 0)
    (hYF : walkBlockExitHistory v hc.le s F n x (Fin.last n) ∉ F) :
    dist (v (walkBlockExitStepPos v hc.le s F n x))
      (walkBlockExitHistory v hc.le s F n x (Fin.last n)) ≤ θ := by
  have hA : BlockExitsAttained s F n (interpPathCM v hc.le x) := by
    by_contra h
    exact hτ (by simp only [walkBlockExitStepTime, h, ↓reduceIte])
  have hpos : walkBlockExitStepPos v hc.le s F n x =
      x (⌊c * (blockExitTimes s F n (interpPathCM v hc.le x) : ℝ)⌋₊ + 1) := by
    simp only [walkBlockExitStepPos, walkBlockExitStepTime, hA, ↓reduceIte, ENat.toNat_natCast]
  have hY : walkBlockExitHistory v hc.le s F n x (Fin.last n) =
      interpPathCM v hc.le x (blockExitTimes s F n (interpPathCM v hc.le x)) := by
    simp only [walkBlockExitHistory, blockExitPositions_apply, Fin.val_last]
  rw [hpos, hY]
  rw [hY] at hYF
  have hguard := norm_vertex_walkBlockExitStepStart_le v hc hs hFB n x hYF
  have hnn : 0 ≤ c * (blockExitTimes s F n (interpPathCM v hc.le x) : ℝ) :=
    mul_nonneg hc.le (NNReal.coe_nonneg _)
  have hseg := interpPathCM_mem_segment v hc.le x (Nat.floor_le hnn) (Nat.lt_floor_add_one _).le
  rcases hadj ⌊c * (blockExitTimes s F n (interpPathCM v hc.le x) : ℝ)⌋₊ with heq | hm
  · rw [heq, segment_same, mem_singleton_iff] at hseg
    rw [heq, hseg, dist_self]
    exact hθ
  · have hlen := hM _ _ hm hguard ⟨_, hseg, hYF⟩
    have hball := segment_subset_closedBall_of_mem hseg (right_mem_segment ℝ _ _)
    rw [mem_closedBall] at hball
    exact hball.trans hlen

end BlockExit

end MatedCRT
