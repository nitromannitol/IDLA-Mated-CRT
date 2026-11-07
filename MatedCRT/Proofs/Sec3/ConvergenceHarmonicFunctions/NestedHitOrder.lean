import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.BoundarySurvival

/-! # Comparing an outer annulus crossing with nested-disk survival -/

namespace MatedCRT

open MeasureTheory Set Metric

/-- If the outer boundary of nested disks is hit before a target disk's
boundary, the walk survives in the target disk until every nested boundary
is hit. The comparison is almost sure under the random-walk law. -/
theorem srwLaw_outer_hit_order_le_nested_interior_survival
    {m : ℤ → ℤ → ℕ} {ε R : ℝ} {η : ℝ → ℂ} {x z : ℂ} {a : ℤ}
    (hη : Continuous η) (r : ℕ → ℝ) (hr : Antitone r) (n : ℕ)
    (hpos : ∀ i ≤ n, 0 < r i)
    (ha : a ∈ interiorCellVertices ε η (ball z (r n)))
    (hnb : ∀ i ≤ n, ∀ v ∈ interiorCellVertices ε η (ball z (r i)), ∀ w,
      m v w ≠ 0 → w ∈ interiorCellVertices ε η (ball z (r i)) ∪
        cellVertices ε η (sphere z (r i)))
    (hfin : ∀ᵐ path ∂srwLaw m a,
      vExitTime (interiorCellVertices ε η (ball z (r 0))) path ≠ ⊤)
    (hR : 0 < R) (haR : a ∈ interiorCellVertices ε η (ball x R))
    (hnbR : ∀ v ∈ interiorCellVertices ε η (ball x R), ∀ w,
      m v w ≠ 0 → w ∈ interiorCellVertices ε η (ball x R) ∪
        cellVertices ε η (sphere x R)) :
    srwLaw m a {path | vHitTime (cellVertices ε η (sphere z (r 0))) path ≤
      vHitTime (cellVertices ε η (sphere x R)) path} ≤
    srwLaw m a {path | ∀ i ≤ n, ∀ j : ℕ, (j : ℕ∞) <
      vHitTime (cellVertices ε η (sphere z (r i))) path →
      path j ∈ interiorCellVertices ε η (ball x R)} := by
  calc
    _ ≤ srwLaw m a {path | ∀ i ≤ n,
        vHitTime (cellVertices ε η (sphere z (r i))) path ≤
        vHitTime (cellVertices ε η (sphere x R)) path} := by
      apply measure_mono_ae
      filter_upwards [ae_nestedSphereCellHit_data hη r hr n hpos ha hnb hfin] with path hdata
      intro horder i hi
      exact (hdata.2 0 i (Nat.zero_le i) hi).trans horder
    _ ≤ _ := srwLaw_sphere_hit_order_le_nested_interior_survival hR haR hnbR
      (fun i => cellVertices ε η (sphere z (r i))) n

end MatedCRT

#print axioms MatedCRT.srwLaw_outer_hit_order_le_nested_interior_survival
