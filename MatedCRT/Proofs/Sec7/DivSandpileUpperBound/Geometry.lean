import MatedCRT.Defs.Sandpile
import Mathlib.Tactic

/-! Cell geometry used to compare the stopped and global sandpiles. -/

namespace MatedCRT.Sec7

open Set Metric

/-- A continuous cell which meets a ball but misses its frontier is contained in the ball. -/
theorem interior_cell_subset_ball {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    {c : ℂ} {r : ℝ} {k : ℤ}
    (hk : k ∈ interiorCellVertices ε η (ball c r)) : cell ε η k ⊆ ball c r := by
  intro z hz
  obtain ⟨⟨y, hyc, hyb⟩, hkf⟩ : (cell ε η k ∩ ball c r).Nonempty ∧
      ¬ (cell ε η k ∩ frontier (ball c r)).Nonempty := hk
  have hr : r ≠ 0 := by
    rintro rfl
    simp at hyb
  rw [frontier_ball c hr] at hkf
  by_contra hzb
  obtain ⟨s, hs, rfl⟩ : ∃ s ∈ Icc (ε * (k - 1)) (ε * k), η s = z := hz
  obtain ⟨s', hs', rfl⟩ : ∃ s ∈ Icc (ε * (k - 1)) (ε * k), η s = y := hyc
  have hcont : ContinuousOn (fun τ => dist (η τ) c) (uIcc s' s) :=
    (hη.dist continuous_const).continuousOn
  have hmem : r ∈ uIcc (dist (η s') c) (dist (η s) c) := by
    rw [mem_ball] at hyb
    rw [mem_ball, not_lt] at hzb
    exact Set.mem_uIcc.2 (Or.inl ⟨hyb.le, hzb⟩)
  obtain ⟨τ, hτ, hτr⟩ := intermediate_value_uIcc hcont hmem
  exact hkf ⟨η τ, ⟨τ, Set.uIcc_subset_Icc hs' hs hτ, rfl⟩, mem_sphere.2 hτr⟩

/-- If adjacent cells meet, the graph closure of the interior cell vertices lies in the
vertices whose cells meet the closed ball. -/
theorem closure_ballInterior_subset {m : ℤ → ℤ → ℕ} {ε ρ : ℝ} {η : ℝ → ℂ}
    (hη : Continuous η)
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) :
    vClosure m (ballInterior ε η ρ) ⊆ cellVertices ε η (closedBall 0 ρ) := by
  intro b hb
  rcases hb with hb | ⟨_, a, ha, hab⟩
  · obtain ⟨z, hz, hzball⟩ := hb.1
    exact ⟨z, hz, ball_subset_closedBall hzball⟩
  · obtain ⟨z, hza, hzb⟩ := hadj a b hab
    exact ⟨z, hzb, ball_subset_closedBall (interior_cell_subset_ball hη ha hza)⟩

end MatedCRT.Sec7
