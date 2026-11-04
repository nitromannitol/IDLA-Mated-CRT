import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellEvents

/-! Admissibility of a finite sequence of shells. -/

namespace MatedCRT.Sec7

open Set Metric

/-- Every shell up to a finite horizon contains the initial shell. -/
theorem initial_subset_iterated_shell_prefix
    {ε : ℝ} {η : ℝ → ℂ} (Θ : ℕ → Set ℤ) (r : ℕ → ℝ) (n : ℕ)
    (hε : 0 ≤ ε) (hr : ∀ k < n, 0 < r k)
    (hstep : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (r k) (fillCells ε η (Θ k)))) :
    ∀ k ≤ n, Θ 0 ⊆ Θ k := by
  intro k hk
  induction k with
  | zero => exact Subset.rfl
  | succ k ih =>
    rw [hstep k (by omega)]
    exact (ih (by omega)).trans (subset_cellVertices_thickening_fill hε (hr k (by omega)))

/-- The common radius budget propagates the ambient bound, diameter bound,
origin, and inner ball through every shell up to the finite horizon. -/
theorem iterated_shell_admissibility_of_total_budget
    {m : ℤ → ℤ → ℕ} {ε ρ D R₀ s₀ : ℝ} {η : ℝ → ℂ}
    (Θ : ℕ → Set ℤ) (r : ℕ → ℝ) (n : ℕ)
    (hε : 0 ≤ ε) (hη : Continuous η) (hD : 0 ≤ D) (hR₀ : 0 ≤ R₀)
    (hr : ∀ k < n, 0 < r k)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (h0 : Θ 0 ⊆ cellVertices ε η (closedBall 0 R₀))
    (hzero : (0 : ℤ) ∈ Θ 0) (hball : ball 0 s₀ ⊆ fillCells ε η (Θ 0))
    (hstep : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (r k) (fillCells ε η (Θ k))))
    (hbudget : ((∑ j ∈ Finset.range n, r j) + ((n : ℝ) + 1) * (2 * D)) + R₀ < ρ)
    (hsize : ∀ a ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η a) ≤ D) :
    ∀ k ≤ n, fillCells ε η (Θ k) ⊆ ball 0 ρ ∧
      (∀ a ∈ vClosure m (Θ k), diam (cell ε η a) ≤ D) ∧
      (0 : ℤ) ∈ Θ k ∧ ball 0 s₀ ⊆ fillCells ε η (Θ k) := by
  obtain ⟨hfill, hdiam⟩ := iterated_shell_geometry_of_total_budget Θ r n hε hη hD hR₀
    (fun k hk => (hr k hk).le) hadj h0 hstep hbudget hsize
  have hsub := initial_subset_iterated_shell_prefix Θ r n hε hr hstep
  intro k hk
  refine ⟨hfill k hk, hdiam k hk, hsub k hk hzero, ?_⟩
  intro z hz
  obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp (hball hz)
  exact mem_iUnion₂.mpr ⟨a, hsub k hk ha, hza⟩

end MatedCRT.Sec7
