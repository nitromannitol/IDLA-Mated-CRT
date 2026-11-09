import MatedCRT.FirstPass.S4S6c.CellBoundary
import MatedCRT.FirstPass.S4S6c.FrontierSeparation

/-!
# Window containment of the test windows of the printed Lemma 6.8 (q2, task fp-S4S6c-envscaling-6-7-6-8; LEMMA68 C3)

A test started at a vertex `y` of the walk uses the window `Wt y = I(B_{2R}(z))` (LEMMA68 eq (C3)), where `z` is the test
centre and `R` the good radius at `z`. This file proves the deterministic containment `Wt y ⊆ V(U₂) \ Θ` of
`ConfigBound68.trace_half` (hypothesis `hWU`), for a window whose closed disk lies in the `r`-thickening of the cluster
`F` at a positive distance from `F`:

* `innerWindow_subset_meetVerts`: every cell of `I(B_{2R}(z))` lies in `B_{2R}(z)` (`CellBoundary`), hence in
  `thickening r F`, and misses `Θ` (since cells of `Θ` lie in `F`, which the disk misses).

No probability input is used.
-/

open Set Metric

namespace MatedCRT

namespace ConfigGeometry68

/-- **Window containment (LEMMA68 `Wt y ⊆ V(U₂) \ Θ`, C3).** Let `H v` be the connected, nonempty cells, `F` the cluster
(`H k ⊆ F` for `k ∈ Θ`), and suppose the open disk `B_{2R}(z)` lies in `thickening r F` (witnessed by a point `f ∈ F`
with `dist z f < r - 2R`) and misses `F` (`2R ≤ dist z f` for `f ∈ F`). Then the window `I(B_{2R}(z))` is contained in
`V(U₂) \ Θ`, `U₂ = thickening r F`. -/
theorem innerWindow_subset_meetVerts {H : ℤ → Set ℂ} {F : Set ℂ} {Θ : Set ℤ} {z : ℂ} {r R : ℝ}
    (hconn : ∀ v, IsPreconnected (H v)) (hne : ∀ v, (H v).Nonempty)
    (hF : ∀ k ∈ Θ, H k ⊆ F)
    (hnear : ∃ f ∈ F, dist z f < r - 2 * R) (hfar : ∀ f ∈ F, 2 * R ≤ dist z f) :
    innerVertices H (ball z (2 * R)) ⊆ FrontierSeparation.meetVerts H (thickening r F) \ Θ := by
  intro v hv
  have hsub : H v ⊆ ball z (2 * R) := cell_subset_of_mem_innerVertices hconn isOpen_ball hv
  obtain ⟨f, hfF, hfd⟩ := hnear
  have hball : ball z (2 * R) ⊆ thickening r F := by
    intro p hp
    rw [Metric.mem_thickening_iff]
    refine ⟨f, hfF, ?_⟩
    have hpz : dist p z < 2 * R := Metric.mem_ball.mp hp
    calc dist p f ≤ dist p z + dist z f := dist_triangle _ _ _
      _ < 2 * R + (r - 2 * R) := by linarith
      _ = r := by ring
  obtain ⟨p, hp⟩ := hne v
  refine ⟨⟨p, subset_closure hp, hball (hsub hp)⟩, ?_⟩
  intro hvΘ
  have hpF : p ∈ F := hF v hvΘ hp
  have h1 : 2 * R ≤ dist p z := by
    have := hfar p hpF
    rwa [dist_comm] at this
  have h2 : dist p z < 2 * R := Metric.mem_ball.mp (hsub hp)
  linarith

end ConfigGeometry68

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.ConfigGeometry68.innerWindow_subset_meetVerts
