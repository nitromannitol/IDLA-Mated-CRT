import MatedCRT.FirstPass.Derived.BlockExitWalkCompProd
import MatedCRT.FirstPass.Derived.BrownianBlockExitKernel

/-!
# One-step closeness of the walk from a comparison started at the walk vertex

The one-step closeness of the interpolated walk to the Brownian block-exit kernel compares the
walk restarted at a vertex `u` with Brownian motion started at the current block-exit position
`y`, where `y` is only known to lie within a distance `θ` of the embedded vertex `v u`. The
invariance principle compares the walk with Brownian motion started at the vertex `v u` itself,
exiting the same open block. The two Brownian laws differ by at most `24 θ / s` on every Borel
set (the Lipschitz bound of the exit law of a block in its starting point), so the closeness at
the vertex gives the closeness at `y`, with the error increased by `24 θ / s`.

## Main results

* `blockExitKernel_apply_exitPoint`: the exit law of a block as the law of the exit point.
* `prokhorovLE_cellBlockExitKernel_of_fixedBlock`: moving the Brownian start from a point `p`
  to a point `y` costs `24 |p - y| / s` in the error, for the block of the cell of `y`.
* `prokhorovLE_walkNextBlockExitKernel_of_diagonal`: closeness of the walk restarted at `u` to
  the Brownian block-exit kernel at every `y ∉ F` within `θ` of `v u`, from closeness to the
  Brownian motion started at `v u` exiting the block of the cell of `y`.
-/

open MeasureTheory ProbabilityTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- The exit law of the block with index `c` evaluated on a Borel set, in the exit-point form. -/
theorem blockExitKernel_apply_exitPoint (s : ℝ) (c : ℤ × ℤ) (x : ℂ) {A : Set ℂ}
    (hA : MeasurableSet A) :
    blockExitKernel s c x A = planarBrownianMotion x {ω | ω ((ContinuousPath.exitTime
      (openBlock s c.1 c.2) ω).toNNReal) ∈ A} := by
  rw [blockExitKernel_apply, Measure.map_apply (measurable_exitPosition (isOpen_openBlock _ _ _)) hA,
    ← exitPoint_eq_exitPosition]
  rfl

/-- **Moving the Brownian start inside the block of a cell.** If a law is `(r, e)`-close to the
exit law, from the block around the cell of `y`, of Brownian motion started at any point `p`, then
it is `(r, e + 24 |p - y| / s)`-close to the block-exit kernel at `y`. -/
theorem prokhorovLE_cellBlockExitKernel_of_fixedBlock {s : ℝ} (hs : 0 < s) {y p : ℂ}
    {μ : Measure ℂ} {r e : ℝ} (he : 0 ≤ e)
    (h : LatticeProb.ProkhorovLE μ (blockExitKernel s (cellIndex s y) p) r e) :
    LatticeProb.ProkhorovLE μ (cellBlockExitKernel s y) r (e + 24 * dist p y / s) := by
  intro A hA
  refine (h A hA).trans ?_
  have hT : MeasurableSet (thickening r A) := isOpen_thickening.measurableSet
  have hb := abs_planarBrownian_exitPoint_openBlock_sub_le hs (mem_closedCell_cellIndex hs y) p hT
  rw [cellBlockExitKernel_apply_set s y hT, blockExitKernel_apply_exitPoint s _ p hT]
  have hd : 0 ≤ 24 * dist p y / s := by positivity
  obtain ⟨P, hP⟩ : ∃ P, P = planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime
    (openBlock s (cellIndex s y).1 (cellIndex s y).2) ω).toNNReal) ∈ thickening r A} :=
    ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = planarBrownianMotion p {ω | ω ((ContinuousPath.exitTime
    (openBlock s (cellIndex s y).1 (cellIndex s y).2) ω).toNNReal) ∈ thickening r A} :=
    ⟨_, rfl⟩
  rw [← hP, ← hQ] at hb ⊢
  have hPtop : P ≠ ⊤ := hP ▸ measure_ne_top _ _
  have hQtop : Q ≠ ⊤ := hQ ▸ measure_ne_top _ _
  have hle : Q.toReal ≤ P.toReal + 24 * dist p y / s := by
    have := (abs_le.1 hb).1
    linarith
  calc Q + ENNReal.ofReal e
      ≤ (P + ENNReal.ofReal (24 * dist p y / s)) + ENNReal.ofReal e := by
        gcongr
        calc Q = ENNReal.ofReal Q.toReal := (ENNReal.ofReal_toReal hQtop).symm
          _ ≤ ENNReal.ofReal (P.toReal + 24 * dist p y / s) := ENNReal.ofReal_le_ofReal hle
          _ ≤ ENNReal.ofReal P.toReal + ENNReal.ofReal (24 * dist p y / s) :=
            ENNReal.ofReal_add_le
          _ = P + ENNReal.ofReal (24 * dist p y / s) := by rw [ENNReal.ofReal_toReal hPtop]
    _ = P + ENNReal.ofReal (e + 24 * dist p y / s) := by
        rw [add_assoc, add_comm (ENNReal.ofReal (24 * dist p y / s)),
          ← ENNReal.ofReal_add he hd]

/-- **Closeness of the restarted walk at every position near the vertex.** Let `v u` be the
embedded vertex `u`. Suppose that for every `y ∉ F` and vertex `u` with `dist (v u) y ≤ θ`, the
next block-exit position of the walk restarted at `u` is `(r, e)`-close to the exit point, from
the block around the cell of `y`, of Brownian motion started at `v u`. Then it is
`(r, e + 24 θ / s)`-close to the block-exit kernel frozen on `F` at `y`. -/
theorem prokhorovLE_walkNextBlockExitKernel_of_diagonal (m : ℤ → ℤ → ℕ) (v : ℤ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) {s : ℝ} (hs : 0 < s) {F : Set ℂ} (hF : MeasurableSet F) {θ r e : ℝ}
    (he : 0 ≤ e)
    (hdiag : ∀ y ∉ F, ∀ u : ℤ, dist (v u) y ≤ θ →
      LatticeProb.ProkhorovLE (walkNextBlockExitKernel m v hc s F (y, u))
        (blockExitKernel s (cellIndex s y) (v u)) r e) :
    ∀ y ∉ F, ∀ u : ℤ, dist (v u) y ≤ θ →
      LatticeProb.ProkhorovLE (walkNextBlockExitKernel m v hc s F (y, u))
        (frozenBlockExitKernel s hF y) r (e + 24 * θ / s) := by
  intro y hy u hu A hA
  rw [frozenBlockExitKernel_of_notMem s hF hy]
  refine ((prokhorovLE_cellBlockExitKernel_of_fixedBlock hs he (hdiag y hy u hu)) A hA).trans ?_
  gcongr

end BlockExit

end MatedCRT
