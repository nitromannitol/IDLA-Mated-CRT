import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ConcentricBoundaryLimit

/-! Enlarging a disk inside a slightly larger ambient disk. -/

namespace MatedCRT

open Set Metric Filter Topology

/-- A disk contained in an ambient disk admits a sequence of strictly larger
concentric disks in any strictly larger ambient disk, with radii decreasing
to the original radius. -/
theorem exists_concentric_radii {z : ℂ} {r ρ ρ' : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (hball : ball z r ⊆ ball 0 ρ) :
    ∃ R : ℕ → ℝ, (∀ j, r < R j) ∧ Tendsto R atTop (𝓝 r) ∧
      ∃ Rmax, (∀ j, R j ≤ Rmax) ∧ ball z Rmax ⊆ ball 0 ρ' := by
  have hcl : closedBall z r ⊆ ball (0 : ℂ) ρ' := by
    have h := closure_mono hball
    rw [closure_ball z hr.ne', closure_ball (0 : ℂ) hρ.ne'] at h
    exact h.trans (closedBall_subset_ball hρρ')
  obtain ⟨d, hd, hsub⟩ := (isCompact_closedBall z r).exists_thickening_subset_open
    isOpen_ball hcl
  rw [thickening_closedBall hd hr.le] at hsub
  let R : ℕ → ℝ := fun j => r + d * (1 / ((j : ℝ) + 1))
  refine ⟨R, ?_, ?_, d + r, ?_, hsub⟩
  · intro j
    have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    dsimp [R]
    nlinarith
  · have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul d).const_add r
    simpa [R] using hlim
  · intro j
    have hden : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
    have hone : 1 / ((j : ℝ) + 1) ≤ 1 := (div_le_one₀ (by positivity)).2 hden
    dsimp [R]
    nlinarith

end MatedCRT

#print axioms MatedCRT.exists_concentric_radii
