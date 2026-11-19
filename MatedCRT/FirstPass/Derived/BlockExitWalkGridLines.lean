import MatedCRT.FirstPass.Derived.BlockExitWalkStepKernelClose
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# The walk's block-exit positions lie on the grid lines

A block exit of a continuous path from the open block around the grid cell of a point off the
frozen set `F` is a point of the frontier of that block, hence of the grid lines, as soon as the
exit happens at a finite time. Along a path started off `F` whose block exits are attained, every
block-exit position after time `0` therefore lies on the grid lines: either it is a new exit
position, or the path is frozen at an earlier exit position, which lies on the grid lines.

For the linear interpolation of the simple random walk on a locally finite multigraph with
consecutive vertices adjacent, embedded by a continuous proper curve, the block exits are almost
surely attained, so almost surely all its block-exit positions `Y_{n+1}` lie on the grid lines
when the walk starts off `F`. Through the composition-product identity
`P^a ∘ (H_n, Y_{n+1})⁻¹ = (P^a ∘ H_n⁻¹) ⊗ₘ κ_n`, the one-step kernel `κ_n g` charges only the
grid lines for almost every history `g`.

## Main results

* `blockExitTimes_succ_mem_gridLines`: an attained exit from a point off `F` is on the grid lines.
* `blockExitTimes_mem_gridLines_of_attained`: from a start off `F`, all attained block-exit
  positions after time `0` are on the grid lines.
* `ae_blockExitPositions_succ_mem_gridLines`: the same, almost surely for the interpolated walk.
* `ae_walkBlockExitStepKernel_gridLines_compl`: for almost every history `g`,
  `κ_n g (gridLines s)ᶜ = 0`.
-/

open MeasureTheory Set Metric MarkovProcess Filter ProbabilityTheory
open scoped ENNReal NNReal Topology
open Function
open HarmonicBalls HarmonicBalls.Section6 LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

open WalkPotential

/-- **An attained block exit lies on the grid lines.** If the path is off `F` at its `n`-th
block-exit time and its `(n + 1)`-th block exit is attained, the `(n + 1)`-th block-exit position
is a frontier point of the open block around the grid cell of the `n`-th one. -/
theorem blockExitTimes_succ_mem_gridLines {s : ℝ} (hs : 0 < s) {F : Set ℂ}
    {ω : ContinuousPath ℂ} {n : ℕ} (hA : BlockExitsAttained s F (n + 1) ω)
    (hnF : ω (blockExitTimes s F n ω) ∉ F) :
    ω (blockExitTimes s F (n + 1) ω) ∈ gridLines s := by
  have h0 : ContinuousPath.shift (blockExitTimes s F n ω) ω 0 = ω (blockExitTimes s F n ω) :=
    shift_apply_zero _ ω
  have hnF' : ContinuousPath.shift (blockExitTimes s F n ω) ω 0 ∉ F := by
    rw [h0]
    exact hnF
  have hfin : ContinuousPath.exitTime
      (openBlock s (cellIndex s (ContinuousPath.shift (blockExitTimes s F n ω) ω 0)).1
        (cellIndex s (ContinuousPath.shift (blockExitTimes s F n ω) ω 0)).2)
      (ContinuousPath.shift (blockExitTimes s F n ω) ω) < ⊤ := by
    rcases hA n (Nat.lt_succ_self n) with h | h
    · exact absurd h hnF
    · rw [h0]
      exact h
  have hcoe := coe_firstBlockExitTime_of_not_mem (s := s) hnF' hfin
  have hfr := ContinuousPath.coordinate_exitTime_mem_frontier _ (isOpen_openBlock _ _ _)
    (ContinuousPath.shift (blockExitTimes s F n ω) ω) (mem_openBlock_cellIndex hs _) hfin.ne
  rw [← hcoe, ENNReal.toNNReal_coe, ContinuousPath.shift_apply] at hfr
  rw [blockExitTimes_succ' s F n ω]
  exact frontier_openBlock_subset_gridLines hs _ _ hfr

/-- **Attained block-exit positions lie on the grid lines.** For a path started off `F` whose
first `n + 1` block exits are attained, the `(n + 1)`-th block-exit position lies on the grid
lines. -/
theorem blockExitTimes_mem_gridLines_of_attained {s : ℝ} (hs : 0 < s) {F : Set ℂ}
    {ω : ContinuousPath ℂ} (h0 : ω 0 ∉ F) :
    ∀ n : ℕ, BlockExitsAttained s F (n + 1) ω →
      ω (blockExitTimes s F (n + 1) ω) ∈ gridLines s
  | 0, hA => blockExitTimes_succ_mem_gridLines hs hA (by rw [blockExitTimes_zero]; exact h0)
  | n + 1, hA => by
    by_cases hF : ω (blockExitTimes s F (n + 1) ω) ∈ F
    · have hfz : firstBlockExitTime s F
          (ContinuousPath.shift (blockExitTimes s F (n + 1) ω) ω) = 0 := by
        have h0' : ContinuousPath.shift (blockExitTimes s F (n + 1) ω) ω 0 ∈ F := by
          rw [shift_apply_zero]
          exact hF
        simp only [firstBlockExitTime, h0', ↓reduceIte]
      rw [blockExitTimes_succ' s F (n + 1) ω, hfz, add_zero]
      exact blockExitTimes_mem_gridLines_of_attained hs h0 n fun j hj => hA j (by omega)
    · exact blockExitTimes_succ_mem_gridLines hs hA hF

theorem interpPathCM_apply_zero (v : ℤ → ℂ) {c : ℝ} (hc : 0 ≤ c) (x : ℕ → ℤ) :
    interpPathCM v hc x 0 = v (x 0) := by
  simp [interpPathFn, linInterp]

/-- **Almost surely the walk's block-exit positions lie on the grid lines.** For a locally finite
multigraph whose consecutive vertices are adjacent, `ε > 0`, a continuous proper curve `η`, a speed
`c > 0` and a start `a` embedded off `F`, almost surely every block-exit position `Y_{n+1}` of the
interpolated walk lies on the grid lines. -/
theorem ae_blockExitPositions_succ_mem_gridLines {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ} (hc : 0 < c) (a : ℤ) {s : ℝ}
    (hs : 0 < s) {F : Set ℂ} (ha : vertexPoint ε η a ∉ F) :
    ∀ᵐ x ∂srwLaw m a, ∀ n : ℕ, interpPathCM (vertexPoint ε η) hc.le x
      (blockExitTimes s F (n + 1) (interpPathCM (vertexPoint ε η) hc.le x)) ∈ gridLines s := by
  filter_upwards [ae_not_isBounded_range_interpPathCM hlf hcons hε hη hp hc a,
    srwLaw_ae_start m a] with x hx hx0 n
  refine blockExitTimes_mem_gridLines_of_attained hs ?_ n
    (blockExitsAttained_of_not_isBounded hx _)
  rw [interpPathCM_apply_zero, hx0]
  exact ha

/-- **The walk's one-step block-exit kernel charges only the grid lines.** Under the hypotheses of
`map_walkBlockExitHistory_next_eq_compProd_of_proper` and a start `a` embedded off `F`, for almost
every block-exit history `g` of length `n + 1`, `κ_n g (gridLines s)ᶜ = 0`. -/
theorem ae_walkBlockExitStepKernel_gridLines_compl {m : ℤ → ℤ → ℕ}
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {η : ℝ → ℂ} (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {c : ℝ}
    (hc : 0 < c) (a : ℤ) {s : ℝ} (hs : 0 < s) {F : Set ℂ} (hF : MeasurableSet F)
    (ha : vertexPoint ε η a ∉ F)
    (hM : ∀ b b' : ℤ, m b b' ≠ 0 →
      (∃ z ∈ segment ℝ (vertexPoint ε η b) (vertexPoint ε η b'), z ∉ F) →
      dist (vertexPoint ε η b) (vertexPoint ε η b') ≤ s / 2)
    (n : ℕ) :
    ∀ᵐ g ∂(srwLaw m a).map (walkBlockExitHistory (vertexPoint ε η) hc.le s F n),
      walkBlockExitStepKernel m a (vertexPoint ε η) hc.le s F n g (gridLines s)ᶜ = 0 := by
  have hH : Measurable (walkBlockExitHistory (vertexPoint ε η) hc.le s F n) :=
    measurable_walkBlockExitHistory _ hc.le s hF n
  have hY : Measurable fun x : ℕ → ℤ => interpPathCM (vertexPoint ε η) hc.le x
      (blockExitTimes s F (n + 1) (interpPathCM (vertexPoint ε η) hc.le x)) := by
    have heq : (fun x : ℕ → ℤ => interpPathCM (vertexPoint ε η) hc.le x
        (blockExitTimes s F (n + 1) (interpPathCM (vertexPoint ε η) hc.le x))) =
        fun x => blockExitPositions s F (n + 1) (interpPathCM (vertexPoint ε η) hc.le x)
          (Fin.last (n + 1)) := by
      funext x
      rw [blockExitPositions_apply, Fin.val_last]
    rw [heq]
    exact (measurable_pi_apply _).comp
      ((measurable_blockExitPositions s hF (n + 1)).comp (measurable_interpPathCM _ hc.le))
  have hjoint : ∀ᵐ q ∂(srwLaw m a).map (fun x => (walkBlockExitHistory (vertexPoint ε η) hc.le
      s F n x, interpPathCM (vertexPoint ε η) hc.le x
        (blockExitTimes s F (n + 1) (interpPathCM (vertexPoint ε η) hc.le x)))),
      q.2 ∈ gridLines s := by
    rw [ae_map_iff (hH.prodMk hY).aemeasurable
      (measurable_snd (measurableSet_gridLines s))]
    filter_upwards [ae_blockExitPositions_succ_mem_gridLines hlf hcons hε hη hp hc a hs ha]
      with x hx using hx n
  rw [map_walkBlockExitHistory_next_eq_compProd_of_proper hlf hcons hε hη hp hc a hs hF hM n]
    at hjoint
  have := isMarkovKernel_walkBlockExitStepKernel m a (vertexPoint ε η) hc.le s hF n
  filter_upwards [Measure.ae_ae_of_ae_compProd hjoint] with g hg
  exact ae_iff.1 hg

end BlockExit

end MatedCRT
