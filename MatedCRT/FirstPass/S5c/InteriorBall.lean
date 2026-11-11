import MatedCRT.Defs.Map

/-!
# FIRST PASS, interior-ball repair: cell geometry of the killing domains

The repair of the stopped surplus lower bound, IDLA Lemma 5.4 extended to `I_ε`. If every cell meeting the ball `B_{r/2}(z)` has diameter at most `d < r/2`, then every such cell lies in
`B_r(z)`, so its vertex is an interior vertex of `B_r(z)` in the IDLA convention `K_ε(B) = V^ε(B) \ V^ε(∂B)`
(`interiorCellVertices`, Defs/Map.lean:191). Hence `V^ε(B_{r/2}(z)) ⊆ K_ε(B_r(z))`, which is the inclusion (9) of §1.4 Step 2
(there with the sharper `d ≤ ε^θ ≤ c r`).
-/

namespace MatedCRT.S5c

open Metric Set

/-- **Cells of the half ball lie in the full ball** (§1.4 Step 2, eq. (9)): if the cells meeting `B_{r/2}(z)` have diameter at most
`d < r/2`, then `V^ε(B_{r/2}(z)) ⊆ K_ε(B_r(z))`. -/
theorem cellVertices_half_ball_subset_interior {ε : ℝ} {η : ℝ → ℂ} {z : ℂ} {r d : ℝ} (hr : 0 < r) (hd : d < r / 2)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball z (r / 2)).Nonempty → ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ d) :
    cellVertices ε η (ball z (r / 2)) ⊆ interiorCellVertices ε η (ball z r) := by
  intro k hk
  obtain ⟨y, hyc, hyb⟩ := hk
  have hsub : cell ε η k ⊆ ball z r := by
    intro x hx
    rw [mem_ball] at hyb ⊢
    have h1 := hdiam k ⟨y, hyc, hyb⟩ x hx y hyc
    calc dist x z ≤ dist x y + dist y z := dist_triangle x y z
      _ ≤ d + dist y z := by linarith
      _ < d + r / 2 := by linarith
      _ < r := by linarith
  refine ⟨⟨y, hyc, hsub hyc⟩, ?_⟩
  rintro ⟨x, hxc, hxf⟩
  rw [frontier_ball z hr.ne', mem_sphere_iff_norm] at hxf
  have hx := hsub hxc
  rw [mem_ball] at hx
  have : dist x z = r := by simpa [dist_eq_norm] using hxf
  linarith

end MatedCRT.S5c
