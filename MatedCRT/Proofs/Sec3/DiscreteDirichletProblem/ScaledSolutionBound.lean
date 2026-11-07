import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExitTimeSolutionBound

/-! Scaled size bounds for the discrete Dirichlet problem. -/

namespace MatedCRT

open Set Metric Filter Topology

/-- The exit-time barrier gives the size estimate used in Lemma 3.5, Step 2.
The hypotheses are scaled so the right-hand side is independent of the mesh. -/
theorem scaled_abs_solution_le_of_exit_bound
    {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 < ε) (hr : 0 < r) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hsucc : ∀ k, m k (k + 1) ≠ 0)
    (u : ℤ → ℝ) {C A B : ℝ} (hC : 0 ≤ C)
    (hlap : ∀ a ∈ interiorCellVertices ε η (ball z r), |matedLaplacian m u a| ≤ C)
    (hbd : ∀ b ∈ cellVertices ε η (sphere z r), ε * |u b| ≤ A)
    (hQfin : ∀ a ∈ interiorCellVertices ε η (ball z r),
      expectedExitTime m (interiorCellVertices ε η (ball z r)) a ≠ ⊤)
    (hQ : ∀ a ∈ cellVertices ε η (ball z r),
      ε * (expectedExitTime m (interiorCellVertices ε η (ball z r)) a).toReal ≤ B) :
    ∀ a ∈ cellVertices ε η (ball z r), ε * |u a| ≤ A + C * B := by
  have hbd' : ∀ b ∈ cellVertices ε η (sphere z r), |u b| ≤ A / ε := by
    intro b hb
    exact (le_div_iff₀ hε).2 (by simpa [mul_comm] using hbd b hb)
  have hb := abs_solution_le_boundary_add_expectedExitTime hε hr hη hp hadj hsucc u hlap hbd' hQfin
  intro a ha
  have h1 := mul_le_mul_of_nonneg_left (hb a ha) hε.le
  have h2 := mul_le_mul_of_nonneg_left (hQ a ha) hC
  have he : ε * (A / ε) = A := by field_simp
  nlinarith

/-- Eventual boundary and exit-time bounds give an eventual size bound along
the same deterministic mesh sequence. -/
theorem eventually_scaled_abs_solution_le_of_exit_bound
    {e : ℕ → ℝ} {m : ℕ → ℤ → ℤ → ℕ} {η : ℝ → ℂ} {z : ℂ} {r : ℝ}
    (he : ∀ n, 0 < e n) (hr : 0 < r) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hadj : ∀ n j k, m n j k ≠ 0 → (cell (e n) η j ∩ cell (e n) η k).Nonempty)
    (hsucc : ∀ n k, m n k (k + 1) ≠ 0)
    (u : ℕ → ℤ → ℝ) {C A B : ℝ} (hC : 0 ≤ C)
    (hgood : ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) η (ball z r), |matedLaplacian (m n) (u n) a| ≤ C) ∧
      (∀ b ∈ cellVertices (e n) η (sphere z r), e n * |u n b| ≤ A) ∧
      (∀ a ∈ interiorCellVertices (e n) η (ball z r),
        expectedExitTime (m n) (interiorCellVertices (e n) η (ball z r)) a ≠ ⊤) ∧
      (∀ a ∈ cellVertices (e n) η (ball z r),
        e n * (expectedExitTime (m n) (interiorCellVertices (e n) η (ball z r)) a).toReal ≤ B)) :
    ∀ᶠ n in atTop, ∀ a ∈ cellVertices (e n) η (ball z r), e n * |u n a| ≤ A + C * B := by
  filter_upwards [hgood] with n hn
  exact scaled_abs_solution_le_of_exit_bound (he n) hr hη hp (hadj n) (hsucc n)
    (u n) hC hn.1 hn.2.1 hn.2.2.1 hn.2.2.2

end MatedCRT
