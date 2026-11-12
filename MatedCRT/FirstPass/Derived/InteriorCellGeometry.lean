import MatedCRT.FirstPass.S6r.ShellWiring
import MatedCRT.FirstPass.S5c.GreenUpper
import MatedCRT.FirstPass.S6n

/-!
# Cells of interior vertices (BG20 Lemma 5.8, domain inclusions)

For a continuous space-filling curve `η`, a cell `H^ε_k = η([ε(k-1), εk])` is connected. If `k` is an interior
vertex of `D` (its cell meets `D` but not `∂D`), the cell lies in `D` (`Lemma68Window.cell_subset_of_mem_interior`).
Consequences used in the proof of Berestycki-Gwynne (arXiv:2003.10320) Lemma 5.8:

* `interiorCellVertices_subset_of_subset_isOpen`: if `D ⊆ U` with `U` open, the interior vertices of `D` are interior
  vertices of `U`; in particular `V^ε(D) \ V^ε(∂D) ⊆ V^ε(B_ρ) \ V^ε(∂B_ρ)` for `D ⊆ B_ρ`, which is the domain
  inclusion behind the monotonicity (5.39) of the Green function;
* `vertexPoint_mem_of_mem_interiorCellVertices`: the embedded position `η(εk)` of an interior vertex lies in `D`
  (so `η(x)` is an admissible centre `z ∈ D` in (5.1), and `w^ε_y = η(y)` is a point of `H^ε_y ∩ D` in Lemma A.5);
* `interiorCellVertices_finite_of_subset_ball`: for a proper continuous `η`, the interior vertices of a subset of a
  ball form a finite set.
-/

namespace MatedCRT

open Set Metric Filter

namespace InteriorCellGeometry

variable {ε : ℝ} {η : ℝ → ℂ}

/-- Interior vertices of `D` are interior vertices of every open `U ⊇ D`. -/
theorem interiorCellVertices_subset_of_subset_isOpen (hη : Continuous η) {D U : Set ℂ} (hU : IsOpen U)
    (hDU : D ⊆ U) : interiorCellVertices ε η D ⊆ interiorCellVertices ε η U := by
  intro k hk
  have hsub : cell ε η k ⊆ U := (Lemma68Window.cell_subset_of_mem_interior hη k hk).trans hDU
  obtain ⟨z, hz⟩ := hk.1
  refine ⟨⟨z, hz.1, hsub hz.1⟩, ?_⟩
  rintro ⟨w, hwc, hwf⟩
  have hw : w ∈ U ∩ frontier U := ⟨hsub hwc, hwf⟩
  rw [hU.inter_frontier_eq] at hw
  exact hw

/-- The embedded position `η(εk)` of an interior vertex `k` of `D` lies in `D` (`ε ≥ 0`). -/
theorem vertexPoint_mem_of_mem_interiorCellVertices (hε : 0 ≤ ε) (hη : Continuous η) {D : Set ℂ} {k : ℤ}
    (hk : k ∈ interiorCellVertices ε η D) : vertexPoint ε η k ∈ D :=
  Lemma68Window.cell_subset_of_mem_interior hη k hk (Lemma68C12Geom.vertexPoint_mem_cell hε k)

/-- For a proper continuous `η` and `ε > 0`, the interior vertices of a subset of a ball form a finite set. -/
theorem interiorCellVertices_finite_of_subset_ball (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) {D : Set ℂ} {z : ℂ} {r : ℝ}
    (hD : D ⊆ ball z r) : (interiorCellVertices ε η D).Finite :=
  (S5c.cellVertices_ball_finite hη hp hε z r).subset fun _ hk =>
    (interiorCellVertices_subset_of_subset_isOpen hη isOpen_ball hD hk).1

end InteriorCellGeometry

end MatedCRT
