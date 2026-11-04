import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellGeometry
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellStep
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! Ball bounds for the shells from their cumulative radius budget. -/

namespace MatedCRT.Sec7

open Set Metric

/-- The filled graph closure of an iterated shell lies in the requested open
ball when its initial ball and cumulative growth have a strict margin. -/
theorem fill_iterated_shells_closure_subset_ball
    {m : ℤ → ℤ → ℕ} {ε D R₀ R : ℝ} {η : ℝ → ℂ}
    (Θ : ℕ → Set ℤ) (r : ℕ → ℝ) (n : ℕ)
    (hη : Continuous η) (hD : 0 ≤ D) (hR₀ : 0 ≤ R₀)
    (hr : ∀ k < n, 0 ≤ r k)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (h0 : Θ 0 ⊆ cellVertices ε η (closedBall 0 R₀))
    (hstep : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (r k) (fillCells ε η (Θ k))))
    (hdiam : ∀ k ≤ n, ∀ a ∈ vClosure m (Θ k), diam (cell ε η a) ≤ D)
    (hmargin : ((∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D)) + R₀ < R) :
    fillCells ε η (vClosure m (Θ n)) ⊆ ball 0 R := by
  have hstep' : ∀ k < n, Θ (k + 1) ⊆ cellVertices ε η
      (thickening (r k) (fillCells ε η (vClosure m (Θ k)))) := by
    intro k hk
    rw [hstep k hk]
    apply cellVertices_mono
    apply thickening_subset_of_subset
    intro z hz
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨a, Or.inl ha, hza⟩
  have hfill := fill_iterated_shells_subset_cthickening Θ r n hη hD hr hadj h0 hstep' hdiam
  have hnonneg : 0 ≤ (∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D) := by
    apply add_nonneg
    · exact Finset.sum_nonneg fun k hk => hr k (Finset.mem_range.mp hk)
    · positivity
  rw [cthickening_closedBall hnonneg hR₀] at hfill
  exact hfill.trans (closedBall_subset_ball hmargin)

/-- The next shell is finite when its own radius also fits within the
cumulative ambient margin. -/
theorem iterated_shell_next_finite
    {m : ℤ → ℤ → ℕ} {ε D R₀ ρ : ℝ} {η : ℝ → ℂ}
    (Θ : ℕ → Set ℤ) (r : ℕ → ℝ) (n : ℕ)
    (hη : Continuous η) (hD : 0 ≤ D) (hR₀ : 0 ≤ R₀)
    (hr : ∀ k < n, 0 ≤ r k)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (h0 : Θ 0 ⊆ cellVertices ε η (closedBall 0 R₀))
    (hstep : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (r k) (fillCells ε η (Θ k))))
    (hdiam : ∀ k ≤ n, ∀ a ∈ vClosure m (Θ k), diam (cell ε η a) ≤ D)
    (hmargin : ((∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D)) + R₀ + r n < ρ)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite) :
    (cellVertices ε η (thickening (r n) (fillCells ε η (Θ n)))).Finite := by
  have hclosure := fill_iterated_shells_closure_subset_ball Θ r n hη hD hR₀ hr hadj h0
    hstep hdiam (R := ρ - r n) (by linarith)
  have hfill : fillCells ε η (Θ n) ⊆ ball 0 (ρ - r n) := by
    intro z hz
    apply hclosure
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨a, Or.inl ha, hza⟩
  exact finite_cellVertices_thickening_fill_of_ball hfill (by linarith) hfin

end MatedCRT.Sec7
