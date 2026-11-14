import MatedCRT.Defs.RandomWalk

/-!
# Transitions of an induced multigraph

An induced multigraph has the same walk transition as the ambient multigraph
at a vertex with no incident edge leaving the vertex set.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace MatedCRT

/-- The walk transition depends only on the multiplicity row at the current vertex. -/
theorem srwStep_eq_of_row_eq (m m' : ℤ → ℤ → ℕ) (x : ℤ)
    (h : ∀ y, m x y = m' x y) : srwStep m x = srwStep m' x := by
  have he : edgeMeasure m x = edgeMeasure m' x := by
    unfold edgeMeasure
    congr 1
    funext y
    rw [h y]
  simp only [srwStep, he]

open Classical in
/-- The induced and ambient kernels agree at a vertex without edges to the complement. -/
theorem srwKernel_induced_eq (m : ℤ → ℤ → ℕ) (A : Set ℤ) (x : ℤ)
    (hx : x ∈ A) (hinside : ∀ y ∉ A, m x y = 0) :
    srwKernel (fun u v => if u ∈ A ∧ v ∈ A then m u v else 0) x = srwKernel m x := by
  classical
  change srwStep (fun u v => if u ∈ A ∧ v ∈ A then m u v else 0) x = srwStep m x
  apply srwStep_eq_of_row_eq
  intro y
  by_cases hy : y ∈ A
  · simp only [hx, hy, and_self, ite_true]
  · simp only [hy, and_false, ite_false, hinside y hy]

end MatedCRT
