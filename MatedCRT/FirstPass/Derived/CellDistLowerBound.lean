import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Complex.Basic

/-!
# Distance from a point to a bounded set, in terms of its diameter

Two elementary metric facts used to translate between the Euclidean distance from a point `z` to a
cell `H` of small diameter and the distance from `z` to a reference point `a ∈ H`:

* `infDist_ge_dist_sub_diam`: `dist a z - diam H ≤ infDist z H` for `a ∈ H`;
* `sq_diam_div_infDist_le`: if `diam H ≤ δ` and `2 δ ≤ dist a z`, then
  `(diam H / infDist z H)² ≤ 4 (diam H)² / dist a z ²`.
-/

namespace MatedCRT

/-- A point `a` of a bounded set `H` is at distance at most `diam H` from every other point of `H`,
so `infDist z H ≥ dist a z - diam H`. -/
theorem infDist_ge_dist_sub_diam {H : Set ℂ} (hb : Bornology.IsBounded H) {a : ℂ} (ha : a ∈ H)
    (z : ℂ) : dist a z - Metric.diam H ≤ Metric.infDist z H := by
  refine (Metric.le_infDist ⟨a, ha⟩).2 ?_
  intro b hb'
  have h1 : dist a b ≤ Metric.diam H := Metric.dist_le_diam_of_mem hb ha hb'
  have h2 : dist a z ≤ dist a b + dist z b := dist_triangle_right a z b
  linarith

/-- If `diam H ≤ δ` and `2 δ ≤ dist a z` for some `a ∈ H`, then
`(diam H / infDist z H)² ≤ 4 (diam H)² / dist a z ²`. -/
theorem sq_diam_div_infDist_le {H : Set ℂ} (hb : Bornology.IsBounded H) {a : ℂ} (ha : a ∈ H)
    {z : ℂ} {δ : ℝ} (hδ : Metric.diam H ≤ δ) (hz : 2 * δ ≤ dist a z) :
    (Metric.diam H / Metric.infDist z H) ^ 2 ≤ 4 * Metric.diam H ^ 2 / dist a z ^ 2 := by
  have hd := infDist_ge_dist_sub_diam hb ha z
  have hdiam0 : 0 ≤ Metric.diam H := Metric.diam_nonneg
  rcases eq_or_lt_of_le (dist_nonneg : 0 ≤ dist a z) with h0 | hpos
  · have hdiam : Metric.diam H = 0 := by linarith
    simp [hdiam]
  · have hinf : dist a z / 2 ≤ Metric.infDist z H := by linarith
    have hhalf : 0 < dist a z / 2 := by positivity
    calc (Metric.diam H / Metric.infDist z H) ^ 2
        ≤ (Metric.diam H / (dist a z / 2)) ^ 2 := by
          apply pow_le_pow_left₀ (div_nonneg hdiam0 (hhalf.le.trans hinf))
          exact div_le_div_of_nonneg_left hdiam0 hhalf hinf
      _ = 4 * Metric.diam H ^ 2 / dist a z ^ 2 := by
          field_simp
          ring

end MatedCRT
