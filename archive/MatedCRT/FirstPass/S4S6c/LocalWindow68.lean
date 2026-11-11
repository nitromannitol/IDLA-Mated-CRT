import MatedCRT.FirstPass.S4S6c.CellBoundary

/-!
# Local test windows lie in the outer test window

In the printed proof of Lemma 6.8 a walk leaving the outer test disk `B_{4R/3}(z)` at a cell `b` meeting its sphere
starts a local test in the disk `B_ρ(p)` with `p ∈ H b` (the local test disk `B_{R/4}(η b)`). The local test window
`I(B_ρ(p))` (Armitage-Gardiner style inner vertices, `CellBoundary.innerVertices`) and its exit cells lie in the
outer window `I(B_{2R}(z))`. This file proves that deterministic containment (`4R/3 + d + R/4 + 2d < 2R`):

* `local_window_mem_outer`: every cell of `I(B_ρ(p))`, and every cell adjacent to one of them, is a cell of
  `I(B_{2R}(z))`. Cells are connected, `d`-small in their closures (`hsm`), and adjacent cells have intersecting closures
  (`hadj`); no probability input is used.
-/

open Set Metric

namespace MatedCRT

namespace LocalWindow68

/-- **Local window inside the outer window.** Let `H v` be connected cells with `d`-small closures and
`hadj`-adjacent cells meeting. Let `p ∈ H b` where the cell `H b` meets the sphere `∂B_{4R/3}(z)`, and suppose
`4R/3 + d + ρ + d < 2R`. Then every cell of the local window `I(B_ρ(p))`, and every cell `k` with a step `k' → k`
from `k' ∈ I(B_ρ(p))`, lies in the outer window `I(B_{2R}(z))`. -/
theorem local_window_mem_outer {H : ℤ → Set ℂ} {m : ℤ → ℤ → ℕ} {d R ρ : ℝ} {z p : ℂ} {b k : ℤ}
    (hconn : ∀ v, IsPreconnected (H v)) (hne : ∀ v, (H v).Nonempty) (hd : 0 ≤ d)
    (hsm : ∀ v, (closure (H v) ∩ closedBall z (2 * R)).Nonempty →
      ∀ x ∈ closure (H v), ∀ y ∈ closure (H v), dist x y ≤ d)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (H u) ∩ closure (H v)).Nonempty)
    (hpb : p ∈ H b) (hsph : (H b ∩ Metric.sphere z (4 * R / 3)).Nonempty)
    (hgeo : 4 * R / 3 + d + ρ + d < 2 * R)
    (hk : k ∈ innerVertices H (ball p ρ) ∨ ∃ k', k' ∈ innerVertices H (ball p ρ) ∧ m k' k ≠ 0) :
    k ∈ innerVertices H (ball z (2 * R)) := by
  have hpz : dist p z ≤ 4 * R / 3 + d := by
    obtain ⟨q, hqb, hqs⟩ := hsph
    have h2 : dist q z = 4 * R / 3 := Metric.mem_sphere.mp hqs
    have hR0 : 0 ≤ 4 * R / 3 := by rw [← h2]; exact dist_nonneg
    have hqz : q ∈ closedBall z (2 * R) := Metric.mem_closedBall.mpr (by rw [h2]; linarith)
    have h1 := hsm b ⟨q, subset_closure hqb, hqz⟩ p (subset_closure hpb) q (subset_closure hqb)
    have h3 := dist_triangle p q z
    linarith
  have hnear : ∀ x ∈ H k, dist x p ≤ ρ + d := by
    rcases hk with hk | ⟨k', hk', hmk⟩
    · intro x hx
      have hsub := cell_subset_of_mem_innerVertices hconn isOpen_ball hk
      have hxb := Metric.mem_ball.mp (hsub hx)
      linarith
    · intro x hx
      have hsub' := cell_subset_of_mem_innerVertices hconn isOpen_ball hk'
      obtain ⟨q, hq1, hq2⟩ := hadj k' k hmk
      have hcl : closure (H k') ⊆ closedBall p ρ :=
        closure_minimal (fun y hy => ball_subset_closedBall (hsub' hy)) isClosed_closedBall
      have hqp : dist q p ≤ ρ := Metric.mem_closedBall.mp (hcl hq1)
      have hqz : q ∈ closedBall z (2 * R) := Metric.mem_closedBall.mpr (by linarith [dist_triangle q p z])
      have hxq : dist x q ≤ d := hsm k ⟨q, hq2, hqz⟩ x (subset_closure hx) q hq2
      have h4 := dist_triangle x q p
      linarith
  have hsubz : ∀ x ∈ H k, x ∈ ball z (2 * R) := by
    intro x hx
    rw [Metric.mem_ball]
    have h1 := dist_triangle x p z
    have h2 := hnear x hx
    linarith
  obtain ⟨x0, hx0⟩ := hne k
  refine ⟨⟨x0, hx0, hsubz x0 hx0⟩, ?_⟩
  rintro ⟨x, hxH, hxf⟩
  have hxball := hsubz x hxH
  rw [isOpen_ball.frontier_eq] at hxf
  exact hxf.2 hxball

end LocalWindow68

end MatedCRT

/-! ## Axioms -/
#print axioms MatedCRT.LocalWindow68.local_window_mem_outer
