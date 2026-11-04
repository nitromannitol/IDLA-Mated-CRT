import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.CellAnnulus

/-! # The discrete pole lies in the interior vertex domain -/

namespace MatedCRT

open Filter Topology Set Metric MeasureTheory

/-- If the cell containing an interior point is smaller than its distance to the
boundary, its representative is an interior vertex of the ball. -/
theorem vertexOf_mem_interiorCellVertices_ball
    {μ : Measure ℂ} {η : ℝ → ℂ} {ε : ℝ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) {z y : ℂ} {r d : ℝ}
    (hy : dist y z + d < r)
    (hdiam : ∀ x ∈ cell ε η (vertexOf ε η y),
      ∀ w ∈ cell ε η (vertexOf ε η y), dist x w ≤ d) :
    vertexOf ε η y ∈ interiorCellVertices ε η (ball z r) := by
  have hycell := Tightness.mem_cell_vertexOf hη.1 hp hη.2.2.1 hε y
  have hinside : cell ε η (vertexOf ε η y) ⊆ ball z r := by
    intro x hx
    have hxy := hdiam x hx y hycell
    have htri := dist_triangle x y z
    change dist x z < r
    linarith
  constructor
  · exact ⟨y, hycell, hinside hycell⟩
  · rintro ⟨x, hx, hfront⟩
    rw [isOpen_ball.frontier_eq] at hfront
    exact hfront.2 (hinside hx)

/-- An annulus bound for the Green kernel controls the outer layer of the
ball when all cells meeting the enclosing ball have small diameter. -/
theorem scaled_greenKernel_vertexOf_le_of_small_cells
    {μ : Measure ℂ} {η : ℝ → ℂ} {ε : ℝ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) {m : ℤ → ℤ → ℕ}
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hcell : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    {z y : ℂ} {r ρ q d c M : ℝ} (hball : ball z r ⊆ ball 0 ρ)
    (hd : 0 ≤ d) (hyq : dist y z + d < q) (hqr : q + d < r) (hM : 0 ≤ M)
    (hdiam : ∀ b ∈ cellVertices ε η (ball 0 ρ),
      ∀ x ∈ cell ε η b, ∀ w ∈ cell ε η b, dist x w ≤ d)
    (hbound : ∀ x : ℂ, q - d ≤ dist x z → dist x z < q + d →
      c * greenKernel m (interiorCellVertices ε η (ball z r))
        (vertexOf ε η y) (vertexOf ε η x) ≤ M) :
    ∀ x : ℂ, q + d ≤ dist x z →
      c * greenKernel m (interiorCellVertices ε η (ball z r))
        (vertexOf ε η y) (vertexOf ε η x) ≤ M := by
  have hycell := Tightness.mem_cell_vertexOf hη.1 hp hη.2.2.1 hε y
  have hyball : y ∈ ball z r := by
    change dist y z < r
    linarith
  have hylarge : vertexOf ε η y ∈ cellVertices ε η (ball 0 ρ) :=
    ⟨y, hycell, hball hyball⟩
  have ho : vertexOf ε η y ∈ interiorCellVertices ε η (ball z r) :=
    vertexOf_mem_interiorCellVertices_ball hη hp hε (by linarith) (hdiam _ hylarge)
  have hq : ball z q ⊆ ball z r := by
    intro x hx
    change dist x z < q at hx
    change dist x z < r
    linarith
  have hqρ : ball z q ⊆ ball 0 ρ := hq.trans hball
  have hsmall : ∀ b ∈ cellVertices ε η (ball z q),
      ∀ x ∈ cell ε η b, ∀ w ∈ cell ε η b, dist x w ≤ d := by
    intro b hb
    exact hdiam b (by obtain ⟨x, hxc, hx⟩ := hb; exact ⟨x, hxc, hqρ hx⟩)
  have hfinite : (interiorCellVertices ε η (ball z r)).Finite := by
    apply (Tightness.cellVertices_finite hη.1 hp hε (isBounded_ball : Bornology.IsBounded (ball z r))).subset
    exact sdiff_subset
  have hoinner : vertexOf ε η y ∈ cellVertices ε η (ball z q) := by
    refine ⟨y, hycell, ?_⟩
    change dist y z < q
    linarith
  exact scaled_greenKernel_vertexOf_le_of_annulus_le hη hp hε hsymm hlf hcons hfinite
    hcell ho hoinner hM hsmall hbound

end MatedCRT
