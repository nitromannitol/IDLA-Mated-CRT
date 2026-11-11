import LatticeProb.Analysis.ThickeningGeometry
import MatedCRT.Steps.Sec6.ConstantOrderLowerBoundDiv

/-!
# Lemma 6.8: geometry of the cover by good annuli (lines 2509-2524; scale fix at line 2506)

* `exists_half_pow_mem`: dyadic scales `2^{-n} ∈ (x/2, x]` (the choice of `δ` with `√δ ∈ (r/(8√2), r/8]`).
* `exists_grid_near`: every point is within `δ/100` of the grid `(δ/100) ℤ²` (the centre `z`).
* The safe region: if `p ∈ ∂(Θ̄ + B_{r/2})` then `dist(p, Θ̄) = r/2`, so every `w` with `|w - p| < 3r/8` lies in
  `(Θ̄ + B_r) \ cl Θ̄` at distance more than `r/8` from `∂(Θ̄ + B_r)`. The balls of Steps 1-4 (`B_{(4/3)𝐫_z}(z)`,
  `B_{𝐫_z/4}(η(b))` and its `ε^α`-neighbourhood, `B_{2𝐫_z}(z)`) all lie in this region.
* Cells: `η(a)` lies in the cell of `a`; cells are bounded.
-/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

namespace ConstantOrderDiv

/-- Dyadic scales: for `x ∈ (0, 1]` there is `n` with `x/2 < 2^{-n} ≤ x`. -/
theorem exists_half_pow_mem {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ∃ n : ℕ, x / 2 < (1 / 2 : ℝ) ^ n ∧ (1 / 2 : ℝ) ^ n ≤ x :=
  LatticeProb.ThickeningGeometry.exists_half_pow_mem hx hx1

/-- Every point is within `δ/100` of the grid `(δ/100) ℤ²`. -/
theorem exists_grid_near {δ : ℝ} (hδ : 0 < δ) (p : ℂ) :
    ∃ m n : ℤ, ‖p - ((δ / 100 : ℝ) : ℂ) * (m + n * Complex.I)‖ ≤ δ / 100 :=
  LatticeProb.ThickeningGeometry.exists_grid_near hδ p

/-- A point of `∂(E + B_δ)` is at distance `δ` from `E`. -/
theorem infDist_eq_of_mem_frontier_thickening {E : Set ℂ} {δ : ℝ} (hδ : 0 ≤ δ) {p : ℂ}
    (hp : p ∈ frontier (thickening δ E)) : infDist p E = δ :=
  LatticeProb.ThickeningGeometry.infDist_eq_of_mem_frontier_thickening hδ hp

theorem lt_infDist_of_near {E : Set ℂ} {p w : ℂ} {r : ℝ} (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) : r / 8 < infDist w E :=
  LatticeProb.ThickeningGeometry.lt_infDist_of_near hp hw

theorem infDist_lt_of_near {E : Set ℂ} {p w : ℂ} {r : ℝ} (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) : infDist w E < 7 * r / 8 :=
  LatticeProb.ThickeningGeometry.infDist_lt_of_near hp hw

/-- The safe region misses `cl E`. -/
theorem notMem_closure_of_near {E : Set ℂ} {p w : ℂ} {r : ℝ} (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) : w ∉ closure E :=
  LatticeProb.ThickeningGeometry.notMem_closure_of_near hp hw

/-- The safe region lies in `E + B_r`. -/
theorem mem_thickening_of_near {E : Set ℂ} (hE : E.Nonempty) {p w : ℂ} {r : ℝ} (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) : w ∈ thickening r E :=
  LatticeProb.ThickeningGeometry.mem_thickening_of_near hE hp hw

/-- The safe region is at distance more than `r/8` from `∂(E + B_r)`. -/
theorem lt_dist_of_mem_frontier {E : Set ℂ} {p w w₁ : ℂ} {r : ℝ} (hr : 0 ≤ r) (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) (hw₁ : w₁ ∈ frontier (thickening r E)) : r / 8 < dist w₁ w :=
  LatticeProb.ThickeningGeometry.lt_dist_of_mem_frontier hr hp hw hw₁

/-- `η(a)` lies in the cell of `a`. -/
theorem vertexPoint_mem_cell {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (k : ℤ) : vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩

theorem cell_isBounded {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) : Bornology.IsBounded (cell ε η k) :=
  (isCompact_Icc.image hη).isBounded

/-- Two points of a cell of diameter at most `d` are at distance at most `d`. -/
theorem dist_le_of_mem_cell {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {k : ℤ} {d : ℝ}
    (hd : diam (cell ε η k) ≤ d) {x y : ℂ} (hx : x ∈ cell ε η k) (hy : y ∈ cell ε η k) : dist x y ≤ d :=
  (dist_le_diam_of_mem (cell_isBounded hη k) hx hy).trans hd

end ConstantOrderDiv

end MatedCRT
