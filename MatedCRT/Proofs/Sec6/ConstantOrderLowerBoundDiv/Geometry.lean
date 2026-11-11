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
    ∃ n : ℕ, x / 2 < (1 / 2 : ℝ) ^ n ∧ (1 / 2 : ℝ) ^ n ≤ x := by
  classical
  have hex : ∃ n : ℕ, (1 / 2 : ℝ) ^ n ≤ x := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, hn.le⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero]
    linarith
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
    rw [not_le] at hmin
    rw [hk, pow_succ]
    linarith

/-- Every point is within `δ/100` of the grid `(δ/100) ℤ²`. -/
theorem exists_grid_near {δ : ℝ} (hδ : 0 < δ) (p : ℂ) :
    ∃ m n : ℤ, ‖p - ((δ / 100 : ℝ) : ℂ) * (m + n * Complex.I)‖ ≤ δ / 100 := by
  set h : ℝ := δ / 100
  have hpos : 0 < h := by positivity
  refine ⟨round (p.re / h), round (p.im / h), ?_⟩
  have hre : |p.re / h - round (p.re / h)| ≤ 1 / 2 := abs_sub_round _
  have him : |p.im / h - round (p.im / h)| ≤ 1 / 2 := abs_sub_round _
  set w := p - (h : ℂ) * (round (p.re / h) + round (p.im / h) * Complex.I)
  have hwre : w.re = h * (p.re / h - round (p.re / h)) := by
    have : w.re = p.re - h * round (p.re / h) := by simp [w]
    rw [this]
    field_simp
  have hwim : w.im = h * (p.im / h - round (p.im / h)) := by
    have : w.im = p.im - h * round (p.im / h) := by simp [w]
    rw [this]
    field_simp
  calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
    _ = h * |p.re / h - round (p.re / h)| + h * |p.im / h - round (p.im / h)| := by
        rw [hwre, hwim, abs_mul, abs_mul, abs_of_pos hpos]
    _ ≤ h * (1 / 2) + h * (1 / 2) := by gcongr
    _ = h := by ring

/-- A point of `∂(E + B_δ)` is at distance `δ` from `E`. -/
theorem infDist_eq_of_mem_frontier_thickening {E : Set ℂ} {δ : ℝ} (hδ : 0 ≤ δ) {p : ℂ}
    (hp : p ∈ frontier (thickening δ E)) : infDist p E = δ := by
  have h := frontier_thickening_subset E hp
  simp only [mem_ofPred_eq] at h
  unfold infDist
  rw [h, ENNReal.toReal_ofReal hδ]

theorem lt_infDist_of_near {E : Set ℂ} {p w : ℂ} {r : ℝ} (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) : r / 8 < infDist w E := by
  have h := infDist_le_infDist_add_dist (x := p) (y := w) (s := E)
  rw [dist_eq_norm, norm_sub_rev] at h
  linarith

theorem infDist_lt_of_near {E : Set ℂ} {p w : ℂ} {r : ℝ} (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) : infDist w E < 7 * r / 8 := by
  have h := infDist_le_infDist_add_dist (x := w) (y := p) (s := E)
  rw [dist_eq_norm] at h
  linarith

/-- The safe region misses `cl E`. -/
theorem notMem_closure_of_near {E : Set ℂ} {p w : ℂ} {r : ℝ} (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) : w ∉ closure E := fun h => by
  have h1 := infDist_zero_of_mem_closure h
  have h2 : r / 8 < infDist w E := lt_infDist_of_near hp hw
  have h3 := norm_nonneg (w - p)
  linarith

/-- The safe region lies in `E + B_r`. -/
theorem mem_thickening_of_near {E : Set ℂ} (hE : E.Nonempty) {p w : ℂ} {r : ℝ} (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) : w ∈ thickening r E := by
  rw [mem_thickening_iff_infDist_lt hE]
  have h := infDist_lt_of_near hp hw
  have h0 : 0 ≤ ‖w - p‖ := norm_nonneg _
  linarith

/-- The safe region is at distance more than `r/8` from `∂(E + B_r)`. -/
theorem lt_dist_of_mem_frontier {E : Set ℂ} {p w w₁ : ℂ} {r : ℝ} (hr : 0 ≤ r) (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) (hw₁ : w₁ ∈ frontier (thickening r E)) : r / 8 < dist w₁ w := by
  have h1 := infDist_eq_of_mem_frontier_thickening hr hw₁
  have h2 := infDist_lt_of_near hp hw
  have h3 := infDist_le_infDist_add_dist (x := w₁) (y := w) (s := E)
  linarith

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
