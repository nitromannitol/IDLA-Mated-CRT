import MatedCRT.FirstPass.S4S6c.CellBoundary
import MatedCRT.FirstPass.S4S6c.WindowStop68
import MatedCRT.FirstPass.S4S6c.NextExitStop
import MatedCRT.FirstPass.S4S6c.TestBound68

/-!
# Path lemma for the per-test bound of the printed Lemma 6.8

For a walk `w` of cells, with `τ = vExitTime I(B_{4R/3}(z))` finite and equal to `k₀ + 1`, the exit cell `w (k₀+1)` is
adjacent to an inner cell of `B_{4R/3}(z)`, and its closure meets the sphere `∂B_{4R/3}(z)` (`exit_closure_meets_sphere`).
If the walk stays in the outer window `I(B_{2R}(z))` until its outer exit, then the shifted walk from `τ` stays in the local
window `I(B_ρ(P b))`, `b = w (k₀+1)`, until the local exit: `stayIn_shift_of_outer`. This is the path-level input of the
one-test bound `TestBound68.stayIn` at a random time (`RandomTimeTestBound.srwLaw_test_bound_random_time`).

No probability input is used. Terminology: inner vertices `I(D)` (Armitage-Gardiner), outer and local
test windows as in the printed proof.
-/

open Set Metric

namespace MatedCRT

namespace ExitPath68

/-- **Exit cell meets the sphere.** If an inner cell `H k'` of `B_ρ(c)` is adjacent to `H k` and `H k` is not inner, then
the closure of `H k` meets the sphere `∂B_ρ(c)` (`X_{S_j}` is on the sphere). -/
theorem exit_closure_meets_sphere {H : ℤ → Set ℂ} {m : ℤ → ℤ → ℕ} {c : ℂ} {ρ : ℝ} {k' k : ℤ}
    (hconn : ∀ v, IsPreconnected (H v))
    (hadj : ∀ u v, m u v ≠ 0 → (closure (H u) ∩ closure (H v)).Nonempty)
    (hk' : k' ∈ innerVertices H (ball c ρ)) (hmk : m k' k ≠ 0) (hnot : k ∉ innerVertices H (ball c ρ)) :
    (closure (H k) ∩ Metric.sphere c ρ).Nonempty := by
  by_cases hmeet : (H k ∩ ball c ρ).Nonempty
  · have hfr : (H k ∩ frontier (ball c ρ)).Nonempty := by
      by_contra hno
      exact hnot ⟨hmeet, hno⟩
    obtain ⟨x, hxH, hxf⟩ := hfr
    refine ⟨x, subset_closure hxH, ?_⟩
    rw [isOpen_ball.frontier_eq] at hxf
    have h1 : dist x c ≤ ρ := Metric.mem_closedBall.mp (closure_ball_subset_closedBall hxf.1)
    have h2 : ρ ≤ dist x c := not_lt.mp (fun h => hxf.2 (Metric.mem_ball.mpr h))
    exact Metric.mem_sphere.mpr (le_antisymm h1 h2)
  · have hsub' := cell_subset_of_mem_innerVertices hconn isOpen_ball hk'
    obtain ⟨q, hq1, hq2⟩ := hadj k' k hmk
    have hcl : closure (H k') ⊆ closedBall c ρ :=
      closure_minimal (fun y hy => ball_subset_closedBall (hsub' hy)) isClosed_closedBall
    have hqc : dist q c ≤ ρ := Metric.mem_closedBall.mp (hcl hq1)
    have hqn : ρ ≤ dist q c := by
      by_contra hlt
      have hlt' : dist q c < ρ := not_le.mp hlt
      obtain ⟨y, hyball, hyH⟩ := mem_closure_iff.mp hq2 (ball c ρ) isOpen_ball (Metric.mem_ball.mpr hlt')
      exact hmeet ⟨y, hyH, hyball⟩
    exact ⟨q, hq2, Metric.mem_sphere.mpr (le_antisymm hqc hqn)⟩

/-- **Inner window from nearness.** A cell all of whose points are within `ρ` of `c`, with `ρ < R'`, lies in
`I(B_{R'}(c))`. -/
theorem inner_of_near {H : ℤ → Set ℂ} {c : ℂ} {ρ R' : ℝ} {k : ℤ} (hne : (H k).Nonempty)
    (hnear : ∀ x ∈ H k, dist x c ≤ ρ) (hρ : ρ < R') : k ∈ innerVertices H (ball c R') := by
  obtain ⟨x0, hx0⟩ := hne
  have hsub : ∀ x ∈ H k, x ∈ ball c R' := fun x hx => by
    rw [Metric.mem_ball]
    linarith [hnear x hx]
  refine ⟨⟨x0, hx0, hsub x0 hx0⟩, ?_⟩
  rintro ⟨x, hxH, hxf⟩
  rw [isOpen_ball.frontier_eq] at hxf
  exact hxf.2 (hsub x hxH)

/-- **Nearness of the local window and its exit cells.** Every cell of `I(B_ρ(c))`, and every cell `k` with a step
`k' → k` from `k' ∈ I(B_ρ(c))`, has all its points within `ρ + d` of `c` (cells are `d`-small in their closures). -/
theorem near_of_inner_or_adj {H : ℤ → Set ℂ} {m : ℤ → ℤ → ℕ} {c : ℂ} {d ρ : ℝ} {k : ℤ}
    (hconn : ∀ v, IsPreconnected (H v)) (hd : 0 ≤ d)
    (hsm : ∀ v, (closure (H v) ∩ closedBall c ρ).Nonempty →
      ∀ x ∈ closure (H v), ∀ y ∈ closure (H v), dist x y ≤ d)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (H u) ∩ closure (H v)).Nonempty)
    (hk : k ∈ innerVertices H (ball c ρ) ∨ ∃ k', k' ∈ innerVertices H (ball c ρ) ∧ m k' k ≠ 0) :
    ∀ x ∈ H k, dist x c ≤ ρ + d := by
  rcases hk with hk | ⟨k', hk', hmk⟩
  · intro x hx
    have hxb := Metric.mem_ball.mp (cell_subset_of_mem_innerVertices hconn isOpen_ball hk hx)
    linarith
  · intro x hx
    have hsub' := cell_subset_of_mem_innerVertices hconn isOpen_ball hk'
    obtain ⟨q, hq1, hq2⟩ := hadj k' k hmk
    have hcl : closure (H k') ⊆ closedBall c ρ :=
      closure_minimal (fun y hy => ball_subset_closedBall (hsub' hy)) isClosed_closedBall
    have hqc : dist q c ≤ ρ := Metric.mem_closedBall.mp (hcl hq1)
    have hxq : dist x q ≤ d := hsm k ⟨q, hq2, Metric.mem_closedBall.mpr hqc⟩ x (subset_closure hx) q hq2
    have h4 := dist_triangle x q c
    linarith

/-- **Path lemma.** Let `τ = vExitTime I(B_{4R/3}(z)) w = k₀ + 1` (the walk leaves the sphere window
at step `k₀ + 1`), let `w` stay in the outer window `I(B_{2R}(z))` until its outer exit (`hstay`), and let the local disks
`B_ρ(P b)` (with `P b ∈ H b`) satisfy `4R/3 + d + ρ + d < 2R`. Then the shifted walk from `τ` stays in the local window
`I(B_ρ(P b))` of its start `b = w (k₀+1)` until the local exit. -/
theorem stayIn_shift_of_outer {H : ℤ → Set ℂ} {m : ℤ → ℤ → ℕ} {A : Set ℤ} {d R ρ : ℝ} {z : ℂ}
    {P : ℤ → ℂ} {w : ℕ → ℤ} {k₀ : ℕ}
    (hconn : ∀ v, IsPreconnected (H v)) (hne : ∀ v, (H v).Nonempty) (hd : 0 ≤ d)
    (hsm : ∀ v, (closure (H v) ∩ closedBall z (2 * R)).Nonempty →
      ∀ x ∈ closure (H v), ∀ y ∈ closure (H v), dist x y ≤ d)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (H u) ∩ closure (H v)).Nonempty)
    (hPb : ∀ b, P b ∈ H b) (hgeo : 4 * R / 3 + d + ρ + d < 2 * R) (hρ : d < ρ)
    (hleg : w (k₀ + 1) = w k₀ ∨ m (w k₀) (w (k₀ + 1)) ≠ 0)
    (hτ : vExitTime (innerVertices H (ball z (4 * R / 3))) w = ((k₀ + 1 : ℕ) : ℕ∞))
    (hstay : ∀ n : ℕ, (n : ℕ∞) < vExitTime (innerVertices H (ball z (2 * R))) w → w n ∈ A) :
    WalkPotential.pathShift (k₀ + 1) w ∈
      TestBound68.stayIn (fun b => innerVertices H (ball (P b) ρ)) A (w (k₀ + 1)) := by
  obtain ⟨hpre, hexit⟩ := (NextExitStop.vExitTime_eq_coe_iff _ w (k₀ + 1)).mp hτ
  have hmk : m (w k₀) (w (k₀ + 1)) ≠ 0 := by
    rcases hleg with h | h
    · exact absurd (by rw [h]; exact hpre k₀ (by omega)) hexit
    · exact h
  have hsphB : (closure (H (w (k₀ + 1))) ∩ Metric.sphere z (4 * R / 3)).Nonempty :=
    exit_closure_meets_sphere hconn hadj (hpre k₀ (by omega)) hmk hexit
  have hPz : dist (P (w (k₀ + 1))) z ≤ 4 * R / 3 + d := by
    obtain ⟨q, hqb, hqs⟩ := hsphB
    have h2 : dist q z = 4 * R / 3 := Metric.mem_sphere.mp hqs
    have hR0 : 0 ≤ 4 * R / 3 := by rw [← h2]; exact dist_nonneg
    have hqz : q ∈ closedBall z (2 * R) := Metric.mem_closedBall.mpr (by rw [h2]; linarith)
    have h1 := hsm (w (k₀ + 1)) ⟨q, hqb, hqz⟩ (P (w (k₀ + 1))) (subset_closure (hPb _)) q hqb
    have h3 := dist_triangle (P (w (k₀ + 1))) q z
    linarith
  have hLoc : ∀ t : ℕ, (t : ℕ∞) < vExitTime (innerVertices H (ball (P (w (k₀ + 1))) ρ))
      (WalkPotential.pathShift (k₀ + 1) w) → w (k₀ + 1 + t) ∈ innerVertices H (ball z (2 * R)) := by
    intro t ht
    have hmem : w (k₀ + 1 + t) ∈ innerVertices H (ball (P (w (k₀ + 1))) ρ) :=
      WindowStop68.mem_of_lt_vExitTime (w := WalkPotential.pathShift (k₀ + 1) w) (n := t) ht
    refine inner_of_near (ρ := ρ + (4 * R / 3 + d)) (c := z) (R' := 2 * R) (hne _) (fun x hx => ?_) (by linarith)
    have hxb := Metric.mem_ball.mp (cell_subset_of_mem_innerVertices hconn isOpen_ball hmem hx)
    have h4 := dist_triangle x (P (w (k₀ + 1))) z
    linarith
  intro j hj
  have hall : ∀ i : ℕ, i ≤ k₀ + 1 + j → w i ∈ innerVertices H (ball z (2 * R)) := by
    intro i hi
    by_cases hik : i < k₀ + 1
    · have hVi := hpre i hik
      refine inner_of_near (ρ := 4 * R / 3) (c := z) (R' := 2 * R) (hne _) (fun x hx => ?_) (by linarith)
      exact (Metric.mem_ball.mp (cell_subset_of_mem_innerVertices hconn isOpen_ball hVi hx)).le
    · obtain ⟨t, rfl⟩ : ∃ t, i = k₀ + 1 + t := ⟨i - (k₀ + 1), by omega⟩
      have htj : (t : ℕ∞) ≤ (j : ℕ∞) := by exact_mod_cast (show t ≤ j by omega)
      exact hLoc t (lt_of_le_of_lt htj hj)
  have hlt := WindowStop68.lt_vExitTime_of_forall (V := innerVertices H (ball z (2 * R))) (w := w) (M := k₀ + 1 + j) hall
  exact hstay _ hlt

end ExitPath68

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.ExitPath68.stayIn_shift_of_outer
