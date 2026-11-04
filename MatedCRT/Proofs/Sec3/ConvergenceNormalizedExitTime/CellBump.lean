import MatedCRT.Draft.Section3

/-!
# The bump-function comparison in Lemma 3.7

A cell meeting the singularity ball can have its marked point outside that
ball. A buffer at least as large as the cell diameter places the marked point
inside the enlarged ball on which the comparison bump equals one.
-/

namespace MatedCRT

open Set Metric

/-- A marked point lies in the radius-enlarged ball whenever its cell meets
the original ball and its diameter is bounded by the enlargement. -/
theorem vertexPoint_mem_enlarged_ball_of_cell_meets
    {η : ℝ → ℂ} {ε r d : ℝ} {x : ℂ} {a : ℤ}
    (hη : Continuous η) (hε : 0 ≤ ε)
    (ha : a ∈ cellVertices ε η (ball x r))
    (hdiam : diam (cell ε η a) ≤ d) :
    vertexPoint ε η a ∈ ball x (r + d) := by
  have hpoint : vertexPoint ε η a ∈ cell ε η a :=
    ⟨ε * a, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩
  obtain ⟨w, hwcell, hwball⟩ := ha
  have hdist := dist_le_diam_of_mem (isCompact_Icc.image hη).isBounded hpoint hwcell
  change dist (vertexPoint ε η a) w ≤ diam (cell ε η a) at hdist
  have htri := dist_triangle (vertexPoint ε η a) w x
  rw [mem_ball] at hwball ⊢
  linarith

/-- A bump equal to one on the enlarged ball dominates the indicator of
cells meeting the smaller ball. -/
theorem bump_eq_one_of_cell_meets {η : ℝ → ℂ} {ε r d : ℝ} {x : ℂ}
    {a : ℤ} {φ : ℂ → ℝ} (hη : Continuous η) (hε : 0 ≤ ε)
    (ha : a ∈ cellVertices ε η (ball x r))
    (hdiam : diam (cell ε η a) ≤ d)
    (hφ : ∀ y ∈ ball x (r + d), φ y = 1) :
    φ (vertexPoint ε η a) = 1 :=
  hφ _ (vertexPoint_mem_enlarged_ball_of_cell_meets hη hε ha hdiam)

end MatedCRT
