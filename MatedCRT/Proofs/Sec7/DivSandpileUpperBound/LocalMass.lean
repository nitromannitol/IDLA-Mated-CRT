import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellContraction

/-! Local counting bounds for the shell iteration. -/

namespace MatedCRT.Sec7

open Set Metric

/-- To control cells in an arbitrary ball, one may recenter at a point of a
cell of `A` and double the radius. The larger-ball count must be available at
every point of the filled cells of `A`. -/
theorem local_count_le_of_recentered_ball_bound
    {ε r M : ℝ} {η : ℝ → ℂ} {A Λ : Set ℤ}
    (hΛ : Λ.Finite) (hA : A ⊆ Λ) (hM : 0 ≤ M)
    (hcount : ∀ w ∈ fillCells ε η A,
      ((cellVertices ε η (ball w (2 * r)) ∩ Λ).ncard : ℝ) ≤ M)
    (z : ℂ) : ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) ≤ M := by
  by_cases hempty : A ∩ cellVertices ε η (ball z r) = ∅
  · simp only [hempty, ncard_empty, Nat.cast_zero]
    exact hM
  · obtain ⟨a, haA, w, hwa, hwz⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    have hwfill : w ∈ fillCells ε η A := mem_iUnion₂.mpr ⟨a, haA, hwa⟩
    have hball : ball z r ⊆ ball w (2 * r) := by
      apply ball_subset_ball'
      have := hwz
      rw [mem_ball, dist_comm] at this
      linarith
    have hsub : A ∩ cellVertices ε η (ball z r) ⊆
        cellVertices ε η (ball w (2 * r)) ∩ Λ := by
      intro b hb
      exact ⟨cellVertices_mono hball hb.2, hA hb.1⟩
    have hfinite : (cellVertices ε η (ball w (2 * r)) ∩ Λ).Finite :=
      hΛ.subset inter_subset_right
    exact (Nat.cast_le.mpr (Set.ncard_le_ncard hsub hfinite)).trans (hcount w hwfill)

/-- A strict margin in the larger-ball bound supplies the strict local-mass
hypothesis required by Lemma 6.8. -/
theorem local_count_lt_of_recentered_ball_bound
    {ε r M T : ℝ} {η : ℝ → ℂ} {A Λ : Set ℤ}
    (hΛ : Λ.Finite) (hA : A ⊆ Λ) (hM : 0 ≤ M) (hMT : M < T)
    (hcount : ∀ w ∈ fillCells ε η A,
      ((cellVertices ε η (ball w (2 * r)) ∩ Λ).ncard : ℝ) ≤ M) :
    ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < T := by
  intro z
  exact lt_of_le_of_lt (local_count_le_of_recentered_ball_bound hΛ hA hM hcount z) hMT

/-- A ball contained in the ambient domain and disjoint from the filled
previous shell has no vertices in the previous shell. -/
theorem cellVertices_ball_subset_ambient_sdiff
    {ε ρ s : ℝ} {η : ℝ → ℂ} {Θ : Set ℤ} {w : ℂ}
    (hball : ball w s ⊆ ball 0 ρ \ fillCells ε η Θ) :
    cellVertices ε η (ball w s) ⊆ cellVertices ε η (ball 0 ρ) \ Θ := by
  intro a ha
  obtain ⟨x, hxa, hxball⟩ := ha
  refine ⟨⟨x, hxa, (hball hxball).1⟩, ?_⟩
  intro haΘ
  exact (hball hxball).2 (mem_iUnion₂.mpr ⟨a, haΘ, hxa⟩)

/-- Cells outside the inner thickening are far enough from the previous
filled shell to serve as centers for admissible mass-bound balls. -/
theorem admissible_balls_of_shell_separation
    {ε ρ s : ℝ} {η : ℝ → ℂ} {A Θ : Set ℤ}
    (hinner : A ⊆ (cellVertices ε η (thickening s (fillCells ε η Θ)))ᶜ)
    (houter : fillCells ε η A ⊆ ball 0 (ρ - s)) :
    ∀ w ∈ fillCells ε η A, ball w s ⊆ ball 0 ρ \ fillCells ε η Θ := by
  intro w hw x hx
  have hwρ := houter hw
  have hxρ : x ∈ ball 0 ρ := by
    apply ball_subset_ball' (x := w) (y := (0 : ℂ)) (ε₁ := s) (ε₂ := ρ) ?_ hx
    rw [mem_ball] at hwρ
    linarith
  refine ⟨hxρ, ?_⟩
  intro hxΘ
  obtain ⟨a, haA, hwa⟩ := mem_iUnion₂.mp hw
  apply hinner haA
  refine ⟨w, hwa, Metric.mem_thickening_iff.mpr ⟨x, hxΘ, ?_⟩⟩
  simpa [dist_comm] using hx

/-- A mass bound for admissible balls yields the strict local-count
condition after doubling the test radius. The geometric inclusion is needed
only at points of occupied cells in `A`. -/
theorem local_count_lt_of_admissible_mass_bound
    {ε ρ r s c M T : ℝ} {η : ℝ → ℂ} {A Λ Θ : Set ℤ}
    (hΛ : Λ.Finite) (hA : A ⊆ Λ) (hM : 0 ≤ M) (hMT : M < T)
    (hradius : 2 * r = c * s)
    (hgeom : ∀ w ∈ fillCells ε η A,
      ball w s ⊆ ball 0 ρ \ fillCells ε η Θ)
    (hmass : ∀ w : ℂ,
      cellVertices ε η (ball w s) ⊆ cellVertices ε η (ball 0 ρ) \ Θ →
      ((cellVertices ε η (ball w (c * s)) ∩ Λ).ncard : ℝ) ≤ M) :
    ∀ z : ℂ, ((A ∩ cellVertices ε η (ball z r)).ncard : ℝ) < T := by
  apply local_count_lt_of_recentered_ball_bound hΛ hA hM hMT
  intro w hw
  rw [hradius]
  exact hmass w (cellVertices_ball_subset_ambient_sdiff (hgeom w hw))

end MatedCRT.Sec7
