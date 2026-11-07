import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSSafeSurvival

/-! # Boundary hitting and survival in interior cells -/

namespace MatedCRT

open MeasureTheory Set

/-- Before the boundary is hit, a walk started in the interior remains
there when every interior edge leads either to the interior or to the
boundary. No finiteness assumption on the exit time is needed. -/
theorem ae_mem_before_boundary_hit_of_neighbours
    {m : ℤ → ℤ → ℕ} {I B : Set ℤ} {a : ℤ} (ha : a ∈ I)
    (hdisj : Disjoint I B)
    (hnb : ∀ v ∈ I, ∀ w, m v w ≠ 0 → w ∈ I ∪ B) :
    ∀ᵐ path ∂srwLaw m a, ∀ j : ℕ, (j : ℕ∞) < vHitTime B path → path j ∈ I := by
  filter_upwards [ae_vHitTime_eq_vExitTime_of_neighbours ha hdisj hnb] with path heq
  intro j hj
  apply mem_of_lt_vExitTime
  by_cases hfin : vExitTime I path ≠ ⊤
  · simpa only [heq hfin] using hj
  · have htop : vExitTime I path = ⊤ := not_ne_iff.mp hfin
    rw [htop]
    exact ENat.natCast_lt_top j

/-- Reaching each of a family of targets before the boundary implies the
nested interior-cell survival event, almost surely. -/
theorem srwLaw_boundary_hit_order_le_nested_survival
    {m : ℤ → ℤ → ℕ} {I B : Set ℤ} {a : ℤ} (ha : a ∈ I)
    (hdisj : Disjoint I B)
    (hnb : ∀ v ∈ I, ∀ w, m v w ≠ 0 → w ∈ I ∪ B)
    (A : ℕ → Set ℤ) (n : ℕ) :
    srwLaw m a {path | ∀ i ≤ n, vHitTime (A i) path ≤ vHitTime B path} ≤
      srwLaw m a {path | ∀ i ≤ n, ∀ j : ℕ, (j : ℕ∞) < vHitTime (A i) path →
        path j ∈ I} := by
  apply measure_mono_ae
  filter_upwards [ae_mem_before_boundary_hit_of_neighbours ha hdisj hnb] with path hstay
  intro horder i hi j hj
  exact hstay j (lt_of_lt_of_le hj (horder i hi))

/-- The preceding comparison specialized to the cells of a disk. -/
theorem srwLaw_sphere_hit_order_le_nested_interior_survival
    {m : ℤ → ℤ → ℕ} {ε R : ℝ} {η : ℝ → ℂ} {x : ℂ} {a : ℤ}
    (hR : 0 < R) (ha : a ∈ interiorCellVertices ε η (Metric.ball x R))
    (hnb : ∀ v ∈ interiorCellVertices ε η (Metric.ball x R), ∀ w,
      m v w ≠ 0 → w ∈ interiorCellVertices ε η (Metric.ball x R) ∪
        cellVertices ε η (Metric.sphere x R))
    (A : ℕ → Set ℤ) (n : ℕ) :
    srwLaw m a {path | ∀ i ≤ n,
      vHitTime (A i) path ≤ vHitTime (cellVertices ε η (Metric.sphere x R)) path} ≤
    srwLaw m a {path | ∀ i ≤ n, ∀ j : ℕ, (j : ℕ∞) < vHitTime (A i) path →
      path j ∈ interiorCellVertices ε η (Metric.ball x R)} :=
  srwLaw_boundary_hit_order_le_nested_survival ha
    (disjoint_interiorCellVertices_sphere ε η x hR) hnb A n

end MatedCRT

#print axioms MatedCRT.ae_mem_before_boundary_hit_of_neighbours
#print axioms MatedCRT.srwLaw_boundary_hit_order_le_nested_survival
#print axioms MatedCRT.srwLaw_sphere_hit_order_le_nested_interior_survival
