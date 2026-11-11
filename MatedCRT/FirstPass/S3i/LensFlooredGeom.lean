import MatedCRT.FirstPass.S3i.BoundaryCell
import MatedCRT.FirstPass.S3i.LensFloored

/-!
# Boundary-vertex geometry for the floored good environment

Floored copies (for `FP36GoodEnvFloored`, S3i/LensFloored.lean) of the two H4 lemmas of S3i/BoundaryCell.lean that take the
good environment: `boundaryVertex_mem_sphere_cells_fp36` (line 99) and `boundaryVertexGeometry_fp36_of_ball` (line 123).
The bodies are those of the originals; only the environment type changes. The helper lemmas they use do not take the
environment and are imported unchanged.
-/

namespace MatedCRT
namespace FirstPass36
namespace H4

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- First conjunct of Lemma 4 for the floored good environment (copy of `boundaryVertex_mem_sphere_cells_fp36`). -/
lemma boundaryVertex_mem_sphere_cells_fp36_floored
    {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω}
    {ρ₀ ρ₁ b ν A β r ε : ℝ} {z y : ℂ} {ω : Ω} {v : ℤ}
    (hε : 0 < ε) (hr : 0 < r)
    (hgood : FP36GoodEnvFloored S ρ₀ ρ₁ b ν A β r z y ε ω)
    (hv : v ∈ vBoundary (S.mult ε ω)
      (interiorCellVertices ε (S.η ω) (ball z r))) :
    v ∈ cellVertices ε (S.η ω) (frontier (ball z r)) := by
  obtain ⟨hA, hadj, -, -, -, -⟩ := hgood
  have hη : Continuous (S.η ω) := hA.1
  obtain ⟨hvI, u₀, hu₀, hmu₀⟩ := hv
  obtain ⟨x₀, hx₀u, hx₀v⟩ := hadj u₀ v hmu₀
  have hint : cell ε (S.η ω) u₀ ⊆ ball z r :=
    cell_subset_ball_of_not_frontier hε hη hr hu₀.1 hu₀.2
  have hmeet : (cell ε (S.η ω) v ∩ ball z r).Nonempty := ⟨x₀, hx₀v, hint hx₀u⟩
  have hmem : v ∈ cellVertices ε (S.η ω) (ball z r) := hmeet
  by_contra hnot
  exact hvI (Set.mem_sdiff_of_mem hmem hnot)

/-- **Lemma 4 (plan §4, H4) with the lens hypothesis `hball`, floored good environment** (copy of
`boundaryVertexGeometry_fp36_of_ball`). -/
lemma boundaryVertexGeometry_fp36_of_ball_floored
    {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω}
    {ρ₀ ρ₁ b ν A β r ε : ℝ} {z y : ℂ} {ω : Ω} {v : ℤ}
    (hε : 0 < ε) (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ₁)
    (hgood : FP36GoodEnvFloored S ρ₀ ρ₁ b ν A β r z y ε ω)
    (hv : v ∈ vBoundary (S.mult ε ω)
      (interiorCellVertices ε (S.η ω) (ball z r))) :
    let δ := ε ^ b
    let η := S.η ω
    let m := S.mult ε ω
    let I := interiorCellVertices ε η (ball z r)
    let q := vertexPoint ε η v
    let P := ballRetraction z r q
    v ∈ cellVertices ε η (frontier (ball z r)) ∧
    infDist q (frontier (ball z r)) ≤ δ ∧
    dist q P ≤ δ ∧
    ∀ u ∈ I, m u v ≠ 0 →
      dist (vertexPoint ε η u) P ≤ 3 * δ := by
  intro δ η m I q P
  have hvF : v ∈ cellVertices ε η (frontier (ball z r)) :=
    boundaryVertex_mem_sphere_cells_fp36_floored hε hr hgood hv
  obtain ⟨hA, hadj, hmesh, -, -, -⟩ := hgood
  have hη : Continuous η := hA.1
  -- every interior cell lies in the disk
  have hint : ∀ u ∈ I, cell ε η u ⊆ ball z r := fun u hu =>
    cell_subset_ball_of_not_frontier hε hη hr hu.1 hu.2
  -- the mesh bound, on the cells meeting the disk
  have hmeshI : ∀ k : ℤ, (cell ε η k ∩ ball z r).Nonempty → diam (cell ε η k) ≤ δ := by
    intro k hk
    obtain ⟨x, hx1, hx2⟩ := hk
    exact hmesh k ⟨x, hx1, hball hx2⟩
  obtain ⟨-, u₀, hu₀, hmu₀⟩ := hv
  obtain ⟨x₀, hx₀u, hx₀v⟩ := hadj u₀ v hmu₀
  have hmeetv : (cell ε η v ∩ ball z r).Nonempty := ⟨x₀, hx₀v, hint u₀ hu₀ hx₀u⟩
  have hwex : ∃ w, w ∈ cell ε η v ∧ w ∈ frontier (ball z r) := hvF
  obtain ⟨w, hwv, hwF⟩ := hwex
  have hwsph : dist w z = r := by
    rw [frontier_ball z hr.ne'] at hwF
    exact mem_sphere.1 hwF
  have hq : q ∈ cell ε η v := vertexPoint_mem_cell hε v
  have hdiam_v : dist q w ≤ δ :=
    le_trans (dist_le_diam_of_mem (cell_isCompact hη v).isBounded hq hwv) (hmeshI v hmeetv)
  have hqP : dist q P ≤ δ :=
    le_trans (dist_ballRetraction_le hr hwsph) hdiam_v
  refine ⟨hvF, le_trans (infDist_le_dist_of_mem hwF) hdiam_v, hqP, ?_⟩
  intro u hu hmuv
  obtain ⟨x, hxu, hxv⟩ := hadj u v hmuv
  have hdu : dist (vertexPoint ε η u) x ≤ δ :=
    le_trans (dist_le_diam_of_mem (cell_isCompact hη u).isBounded (vertexPoint_mem_cell hε u) hxu)
      (hmeshI u hu.1)
  have hdx : dist x q ≤ δ :=
    le_trans (dist_le_diam_of_mem (cell_isCompact hη v).isBounded hxv hq) (hmeshI v hmeetv)
  have h1 := dist_triangle (vertexPoint ε η u) x q
  have h2 := dist_triangle (vertexPoint ε η u) q P
  linarith

end H4
end FirstPass36
end MatedCRT
