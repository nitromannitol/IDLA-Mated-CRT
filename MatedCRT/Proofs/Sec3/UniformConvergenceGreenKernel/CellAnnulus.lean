import MatedCRT.Proofs.Sec5.MeanValueInequality.CellRepresentative
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.BoundaryMaximum

/-!
# Cell representatives near an annular boundary

Adjacent cells on opposite sides of a ball have a representative near its sphere.
This transfers uniform convergence of the rescaled function to the graph boundary.
-/

namespace MatedCRT

open Filter Topology Set Metric MeasureTheory

/-- Cells meeting a bounded set have uniformly small diameter when the mesh is
small, for every continuous proper parametrization. -/
theorem exists_cell_diameter_lt {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {K : Set ℂ}
    (hK : Bornology.IsBounded K) {d : ℝ} (hd : 0 < d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ b ∈ cellVertices ε η K, ∀ x ∈ cell ε η b, ∀ y ∈ cell ε η b, dist x y < d := by
  obtain ⟨ε₀, hε₀, hnear⟩ := Tightness.exists_cell_near_vertexPoint hη hp hK (half_pos hd)
  refine ⟨ε₀, hε₀, fun ε hε hεlt b hb x hx y hy => ?_⟩
  have hx' : dist x (vertexPoint ε η b) < d / 2 := by
    simpa only [dist_eq_norm] using hnear ε hε hεlt b hb x hx
  have hy' : dist (vertexPoint ε η b) y < d / 2 := by
    rw [dist_comm, dist_eq_norm]
    exact hnear ε hε hεlt b hb y hy
  have htri := dist_triangle x (vertexPoint ε η b) y
  linarith

/-- If one cell misses a ball and an adjacent cell meets it, a representative of
the latter lies within one cell diameter of the ball's boundary. -/
theorem exists_vertexOf_eq_near_sphere_of_cells_inter
    {μ : Measure ℂ} {η : ℝ → ℂ} {ε : ℝ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) {a b : ℤ} {z : ℂ} {r d : ℝ}
    (ha : a ∉ cellVertices ε η (ball z r))
    (hb : b ∈ cellVertices ε η (ball z r))
    (hab : (cell ε η a ∩ cell ε η b).Nonempty)
    (hdiam : ∀ x ∈ cell ε η b, ∀ y ∈ cell ε η b, dist x y ≤ d) :
    ∃ x ∈ cell ε η b, vertexOf ε η x = b ∧
      r - d ≤ dist x z ∧ dist x z < r + d := by
  obtain ⟨x, hxb, hx⟩ := exists_vertexOf_eq_of_area_parametrized hη hp hε b
  obtain ⟨w, hwa, hwb⟩ := hab
  obtain ⟨y, hyb, hyball⟩ := hb
  have hw : r ≤ dist w z := by
    have : w ∉ ball z r := fun hw => ha ⟨w, hwa, hw⟩
    exact le_of_not_gt this
  have hy : dist y z < r := hyball
  have hlow := dist_triangle w x z
  have hupp := dist_triangle x y z
  have hwx := hdiam w hwb x hxb
  have hxy := hdiam x hxb y hyb
  exact ⟨x, hxb, hx, by linarith, by linarith⟩

/-- A Green-kernel bound on a thin continuum annulus propagates to all vertices
whose cells miss its inner ball. -/
theorem scaled_greenKernel_le_of_annulus_le
    {μ : Measure ℂ} {η : ℝ → ℂ} {ε : ℝ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : A.Finite)
    (hcell : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    {o : ℤ} (ho : o ∈ A) {z : ℂ} {r d c M : ℝ}
    (hoinner : o ∈ cellVertices ε η (ball z r)) (hM : 0 ≤ M)
    (hdiam : ∀ b ∈ cellVertices ε η (ball z r),
      ∀ x ∈ cell ε η b, ∀ y ∈ cell ε η b, dist x y ≤ d)
    (hbound : ∀ x : ℂ, r - d ≤ dist x z → dist x z < r + d →
      c * greenKernel m A o (vertexOf ε η x) ≤ M) :
    ∀ b ∈ A \ cellVertices ε η (ball z r), c * greenKernel m A o b ≤ M := by
  apply scaled_greenKernel_le_of_boundary_le hsymm hlf hcons hA sdiff_subset ho
    (show o ∉ A \ cellVertices ε η (ball z r) from fun h => h.2 hoinner) c M
  intro a ha b hab hb
  by_cases hbA : b ∈ A
  · have hbinner : b ∈ cellVertices ε η (ball z r) := by simpa [hbA] using hb
    obtain ⟨x, -, hxb, hxlo, hxhi⟩ :=
      exists_vertexOf_eq_near_sphere_of_cells_inter hη hp hε ha.2 hbinner
        (hcell a b hab) (hdiam b hbinner)
    simpa only [hxb] using hbound x hxlo hxhi
  · simpa [greenKernel_eq_zero_of_not_mem_right m o hbA] using hM

/-- The preceding bound applies at every continuum point outside a slightly
larger ball, including points whose representative lies outside the graph domain. -/
theorem scaled_greenKernel_vertexOf_le_of_annulus_le
    {μ : Measure ℂ} {η : ℝ → ℂ} {ε : ℝ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) {m : ℤ → ℤ → ℕ} {A : Set ℤ}
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : A.Finite)
    (hcell : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    {o : ℤ} (ho : o ∈ A) {z : ℂ} {r d c M : ℝ}
    (hoinner : o ∈ cellVertices ε η (ball z r)) (hM : 0 ≤ M)
    (hdiam : ∀ b ∈ cellVertices ε η (ball z r),
      ∀ x ∈ cell ε η b, ∀ y ∈ cell ε η b, dist x y ≤ d)
    (hbound : ∀ x : ℂ, r - d ≤ dist x z → dist x z < r + d →
      c * greenKernel m A o (vertexOf ε η x) ≤ M) :
    ∀ x : ℂ, r + d ≤ dist x z → c * greenKernel m A o (vertexOf ε η x) ≤ M := by
  intro x hx
  by_cases hxA : vertexOf ε η x ∈ A
  · have hxcell := Tightness.mem_cell_vertexOf hη.1 hp hη.2.2.1 hε x
    have hxout : vertexOf ε η x ∉ cellVertices ε η (ball z r) := by
      intro hin
      have hdist := hdiam _ hin x hxcell
      obtain ⟨y, hycell, hyball⟩ := hin
      have hdist' := hdist y hycell
      have htri := dist_triangle x y z
      have hy : dist y z < r := hyball
      linarith
    exact scaled_greenKernel_le_of_annulus_le hη hp hε hsymm hlf hcons hA hcell ho
      hoinner hM hdiam hbound _ ⟨hxA, hxout⟩
  · simpa [greenKernel_eq_zero_of_not_mem_right m o hxA] using hM

end MatedCRT
