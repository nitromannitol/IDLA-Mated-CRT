import MatedCRT.FirstPass.S5d.FloorCells
import MatedCRT.Defs.Map

/-!
# Deterministic cell geometry for the floor of Proposition 5.1 (task fp-S5d-5-1, floor note Part I, Sections 6-8)

Deterministic facts about one mesh `ε` and one outcome of the mated-CRT map `η`:
* an exclusive point `x` of a cell (lying in no other cell, `S5c.exists_exclusive_mem_cell`) has `a^ε_x = a`
  (`vertexOf_eq_of_exclusive`, floor note (14));
* a cell of diameter `< δ/4` meeting `B⁻_{δ/2}(Λ)` lies in `B⁻_{δ/4}(Λ)` (`cell_subset_innerNbhd_quarter`; reuses
  `subset_innerNbhd_quarter_of_small`, FloorCells.lean:55), and, when `Λ ⊆ B_{ρ/3}`, in `B_{ρ/2}` (`cell_subset_ball_half`);
* a connected cell meeting `B_R` and missing the circle `∂B_R` lies in `B_R` (`cell_subset_ball_of_not_sphere`); the
  vertices of such cells form a subset of the interior vertices `ballInterior ε η ρ` when `R < ρ` (`cellVertices_sub_interior`),
  which is the set `A^ε` of floor note Step 8.2.
Inner neighbourhoods are `innerNbhd δ X = B⁻_δ(X)` (Defs/Notation.lean:30).
-/

open MeasureTheory Set Metric Filter Topology

namespace MatedCRT

namespace FloorProof

/-- Floor note (14): the exclusive point `x` of the cell `H^ε_k` (lying in no other cell) has `a^ε_x = k`. -/
theorem vertexOf_eq_of_exclusive {ε : ℝ} {η : ℝ → ℂ} {k : ℤ} {x : ℂ} (hx : x ∈ cell ε η k)
    (hex : ∀ b : ℤ, x ∈ cell ε η b → b = k) : vertexOf ε η x = k := by
  have hset : {j : ℤ | x ∈ cell ε η j} = {k} := by
    ext j
    constructor
    · intro hj
      exact hex j hj
    · intro hj
      rw [Set.mem_singleton_iff.1 hj]
      exact hx
  unfold vertexOf
  rw [hset, csInf_singleton]

/-- Two points of a bounded set of diameter `< d` are at distance `< d`. -/
theorem dist_lt_of_diam_lt {K : Set ℂ} (hb : Bornology.IsBounded K) {d : ℝ} (hd : diam K < d) {x z : ℂ}
    (hx : x ∈ K) (hz : z ∈ K) : dist x z < d :=
  lt_of_le_of_lt (dist_le_diam_of_mem hb hx hz) hd

/-- Cells of diameter `< δ/4` meeting `B⁻_{δ/2}(X)` lie in `B⁻_{δ/4}(X)` (floor note, Step 8, "its entire cell lies at
distance at least `δ/4` from `Λ_t^c`"). -/
theorem cell_subset_innerNbhd_quarter {δ : ℝ} (hδ : 0 < δ) {X K : Set ℂ} (hb : Bornology.IsBounded K)
    (hdiam : diam K < δ / 4) (hmeet : (K ∩ innerNbhd (δ / 2) X).Nonempty) : K ⊆ innerNbhd (δ / 4) X := by
  obtain ⟨y, hyK, hy⟩ := hmeet
  exact subset_innerNbhd_quarter_of_small hδ (fun x hx z hz => dist_lt_of_diam_lt hb hdiam hx hz) ⟨y, hyK, hy⟩

/-- Cells of diameter `< δ/8` meeting `B⁻_{δ/2}(X)`, for `X ⊆ B_{ρ/3}` and `δ < ρ`, lie in `B_{ρ/2}`. -/
theorem cell_subset_ball_half {ρ δ : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ) {X K : Set ℂ} (hX : X ⊆ ball (0 : ℂ) (ρ / 3))
    (hb : Bornology.IsBounded K) (hdiam : diam K < δ / 8) (hmeet : (K ∩ innerNbhd (δ / 2) X).Nonempty) :
    K ⊆ ball (0 : ℂ) (ρ / 2) := by
  obtain ⟨y, hyK, hy⟩ := hmeet
  intro x hx
  have h1 : dist x y < δ / 8 := dist_lt_of_diam_lt hb hdiam hx hyK
  have h2 : dist y 0 < ρ / 3 := by
    have := hX hy.1
    simpa [Metric.mem_ball] using this
  rw [Metric.mem_ball]
  have h3 : dist x 0 ≤ dist x y + dist y 0 := dist_triangle _ _ _
  have h4 : δ / 8 < ρ / 6 := by linarith
  linarith

/-- A connected set meeting the open ball `B_R` and missing the circle `∂B_R` lies in `B_R`. -/
theorem cell_subset_ball_of_not_sphere {R : ℝ} {K : Set ℂ} (hK : IsPreconnected K)
    (hmeet : (K ∩ ball (0 : ℂ) R).Nonempty) (hsph : ∀ x ∈ K, ‖x‖ ≠ R) : K ⊆ ball (0 : ℂ) R := by
  have hcov : K ⊆ ball (0 : ℂ) R ∪ {x : ℂ | R < ‖x‖} := by
    intro x hx
    rcases lt_or_gt_of_ne (hsph x hx) with h | h
    · left
      rw [mem_ball_zero_iff]
      exact h
    · right
      exact h
  have hdisj : Disjoint (ball (0 : ℂ) R) {x : ℂ | R < ‖x‖} := by
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    rw [mem_ball_zero_iff] at hx
    exact absurd hx (not_lt.2 (le_of_lt hx'))
  exact hK.subset_left_of_subset_union isOpen_ball (isOpen_lt continuous_const continuous_norm) hdisj hcov hmeet

/-- The vertices whose cells meet `B_R` but not `∂B_R` (the set `A^ε` of floor note Step 8.2) are interior vertices of
`B_ρ` when `R < ρ`, provided the cells are connected (the image of an interval under the continuous `η`). -/
theorem cellVertices_sub_interior {ε ρ R : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hR : R < ρ) (hRpos : 0 < R) :
    {k : ℤ | (cell ε η k ∩ ball (0 : ℂ) R).Nonempty ∧ ¬ (cell ε η k ∩ sphere (0 : ℂ) R).Nonempty} ⊆
      interiorCellVertices ε η (ball (0 : ℂ) ρ) := by
  intro k hk
  obtain ⟨hmeet, hnot⟩ := hk
  have hK : IsPreconnected (cell ε η k) :=
    (isPreconnected_Icc).image η hη.continuousOn
  have hsph : ∀ x ∈ cell ε η k, ‖x‖ ≠ R := by
    intro x hx hxR
    exact hnot ⟨x, hx, by rw [mem_sphere_zero_iff_norm]; exact hxR⟩
  have hsub := cell_subset_ball_of_not_sphere hK hmeet hsph
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx, hxB⟩ := hmeet
    exact ⟨x, hx, ball_subset_ball hR.le hxB⟩
  · rintro ⟨x, hx, hxF⟩
    rw [frontier_ball (0 : ℂ) (lt_trans hRpos hR).ne'] at hxF
    have hxB := hsub hx
    rw [mem_sphere_zero_iff_norm] at hxF
    rw [mem_ball_zero_iff] at hxB
    have hlt : ‖x‖ < ρ := lt_trans hxB hR
    rw [hxF] at hlt
    exact lt_irrefl _ hlt

end FloorProof

end MatedCRT
