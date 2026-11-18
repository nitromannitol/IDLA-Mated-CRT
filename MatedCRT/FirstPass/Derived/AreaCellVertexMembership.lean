import MatedCRT.FirstPass.Derived.AreaCellRepresentative
import MatedCRT.FirstPass.Derived.AreaCellDiameter

/-!
# Membership of a vertex cell in a finite set of cells closed under the conductances

The cell labelled by `x` is adjacent (positive conductance) to the cell labelled by `x - 1`. If a set
`R` of cells contains every neighbour of every cell satisfying a predicate `P` (conductance to
the complement of `R` vanishes) and the predecessor cell satisfies `P`, then the cell of `x` lies in
`R`. Together with the diameter bound of cells, this places the cell of every embedded vertex near a
bounded set inside the finite set of cells of a network, and bounds the distance from any point of
that cell to the embedded vertex.
-/

set_option autoImplicit false

open MeasureTheory Set ReflectedGMS.GMS

namespace MatedCRT.AreaCellVertexMembership

/-- The embedded vertex `k - 1` is the left endpoint of the curve cell `k`. -/
theorem vertexPoint_pred_mem_cell (ε : ℝ) (hε : 0 ≤ ε) (η : ℝ → ℂ) (k : ℤ) :
    vertexPoint ε η (k - 1) ∈ cell ε η k :=
  ⟨ε * ((k - 1 : ℤ) : ℝ), ⟨le_of_eq (by push_cast; ring),
    mul_le_mul_of_nonneg_left (by push_cast; linarith) hε⟩, rfl⟩

/-- The embedded vertex `k` is the right endpoint of the curve cell `k`. -/
theorem vertexPoint_mem_cell_right (ε : ℝ) (hε : 0 ≤ ε) (η : ℝ → ℂ) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨by rw [mul_sub, mul_one]; linarith, le_rfl⟩, rfl⟩

/-- Consecutive embedded vertices are at distance at most the diameter of the cell between them. -/
theorem dist_vertexPoint_pred_le {ε : ℝ} (hε : 0 ≤ ε) {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ)
    {d : ℝ} (hd : Metric.diam (cell ε η k) ≤ d) :
    dist (vertexPoint ε η (k - 1)) (vertexPoint ε η k) ≤ d := by
  have hb : Bornology.IsBounded (cell ε η k) := (isCompact_Icc.image hη).isBounded
  exact (Metric.dist_le_diam_of_mem hb (vertexPoint_pred_mem_cell ε hε η k)
    (vertexPoint_mem_cell_right ε hε η k)).trans hd

/-- **A cell adjacent to a cell with property `P` lies in every set of cells closed under the
conductances of `P`-cells.** If the predecessor of `x` satisfies `P` and `R` contains every
conductance neighbour of every `P`-cell, then the cell of `x` belongs to `R`. -/
theorem euclideanCellEquiv_mem_of_pred {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) (hsucc : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (R : Set (areaCellConfig h hε m).cells) (P : (areaCellConfig h hε m).cells → Prop)
    (hclose : ∀ v, P v → ∀ w, w ∉ R → (areaCellConfig h hε m).c v w = 0)
    (x : ℤ) (hP : P (euclideanCellEquiv h hε (x - 1))) :
    (euclideanCellEquiv h hε x : (areaCellConfig h hε m).cells) ∈ R := by
  by_contra hx
  have h0 := hclose _ hP _ hx
  rw [areaCellConfig_conductance] at h0
  have h1 : m (x - 1) x = 0 := by exact_mod_cast h0
  exact hsucc (x - 1) (by rwa [sub_add_cancel])

/-- Every point of the cell of `k` is at distance at most the cell diameter from the embedded
vertex `k`. -/
theorem dist_le_vertexPoint_of_mem_cell {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) (k : ℤ) {d : ℝ} (hd : Metric.diam (cell ε η k) ≤ d)
    {z : ReflectedGMS.Plane}
    (hz : z ∈ (((euclideanCellEquiv h hε k : (areaCellConfig h hε m).cells).1 : Cell) :
      Set ReflectedGMS.Plane)) :
    dist z (Complex.orthonormalBasisOneI.repr (vertexPoint ε η k)) ≤ d := by
  have hmem := areaCellRepresentative_mem h hε m (euclideanCellEquiv h hε k)
  rw [areaCellRepresentative_equiv] at hmem
  calc dist z (Complex.orthonormalBasisOneI.repr (vertexPoint ε η k))
      ≤ Metric.diam (((euclideanCellEquiv h hε k : (areaCellConfig h hε m).cells).1 : Cell) :
        Set ReflectedGMS.Plane) :=
        Metric.dist_le_diam_of_mem (euclideanCellEquiv h hε k : (areaCellConfig h hε m).cells).1.isCompact.isBounded hz hmem
    _ = Metric.diam (cell ε η k) := euclideanCellEquiv_diam h hε m k
    _ ≤ d := hd

end MatedCRT.AreaCellVertexMembership
