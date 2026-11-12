import MatedCRT.FirstPass.Derived.CellInballDisjoint
import MatedCRT.FirstPass.S4S6c.TraceInputs68

/-!
# Location of the cells meeting a domain

Deterministic facts about the cells `H^ε_k = η([ε(k-1), εk])` (`MatedCRT.cell`) of a continuous
curve `η`, for the hypotheses `hsub` and `hS` of the Green function bound through segment paths
(`MatedCRT.greenFn_le_of_segmentPaths_of_inballs`) with `H = cell ε η`:

* a cell meeting `B_ρ(z)` lies in the closed disc `B̄_{ρ + diam H}(z)`; on the event of the upper
  bound of the cell size estimate (Lemma 2.8, BG20 Lemma 2.4: `diam H ≤ ε^{2/(2+γ)² - ζ}`) with
  `0 ≤ ε ≤ 1` and a nonnegative exponent, it lies in `B̄_{ρ+1}(z)`;
* the cell of an interior vertex of `D` (`interiorCellVertices ε η D`: the cell meets `D` but not
  `∂D`) lies in the interior of `D`, since cells are connected;
* hence a cell meeting the cell of an interior vertex of `D` meets `D`. For an edge multiplicity
  whose edges join intersecting cells, the neighbours of the interior vertices are vertices of
  `𝒢^ε(D)`. Almost surely the mated-CRT map has this property (`MatedCRT.adjacentCellsMeetAeStep`,
  from the mating-of-trees coupling), so the neighbours of the interior vertices of `D` lie in
  `𝒢^ε(D)` for all `ε > 0` and all `D` at once.

## Main statements

* `MatedCRT.isPreconnected_cell`
* `MatedCRT.cell_subset_closedBall_of_inter_ball`
* `MatedCRT.cell_subset_closedBall_add_one_of_diam_le`
* `MatedCRT.cell_subset_interior_of_mem_interiorCellVertices`
* `MatedCRT.mem_cellVertices_of_inter_cell`
* `MatedCRT.mem_cellVertices_of_mult_ne_zero`
* `MatedCRT.MatedCRTEnv.IsValid.ae_mem_cellVertices_of_mult_ne_zero`
-/

open MeasureTheory Set Metric

namespace MatedCRT

/-- The cells of a continuous curve are preconnected. -/
theorem isPreconnected_cell {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) :
    IsPreconnected (cell ε η k) :=
  isPreconnected_Icc.image η hη.continuousOn

/-- A cell of a continuous curve meeting `B_ρ(z)` lies in the closed disc `B̄_{ρ + diam H}(z)`. -/
theorem cell_subset_closedBall_of_inter_ball {ε ρ : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {k : ℤ}
    {z : ℂ} (hk : (cell ε η k ∩ ball z ρ).Nonempty) :
    cell ε η k ⊆ closedBall z (ρ + diam (cell ε η k)) := by
  obtain ⟨x, hxH, hxB⟩ := hk
  intro y hy
  rw [mem_closedBall]
  calc dist y z ≤ dist y x + dist x z := dist_triangle y x z
    _ ≤ diam (cell ε η k) + ρ :=
        add_le_add (dist_le_diam_of_mem (isBounded_cell hη k) hy hxH) (mem_ball.1 hxB).le
    _ = ρ + diam (cell ε η k) := add_comm _ _

/-- On the event of the upper bound of the cell size estimate, `diam H ≤ ε ^ e` with `0 ≤ ε ≤ 1`
and `0 ≤ e`, a cell meeting `B_ρ(z)` lies in `B̄_{ρ+1}(z)`. -/
theorem cell_subset_closedBall_add_one_of_diam_le {ε ρ e : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (he : 0 ≤ e) {k : ℤ} {z : ℂ}
    (hk : (cell ε η k ∩ ball z ρ).Nonempty) (hd : diam (cell ε η k) ≤ ε ^ e) :
    cell ε η k ⊆ closedBall z (ρ + 1) :=
  (cell_subset_closedBall_of_inter_ball hη hk).trans <| closedBall_subset_closedBall <| by
    have := Real.rpow_le_one hε0 hε1 he
    linarith

/-- The cell of an interior vertex of `D` (its cell meets `D` but not `∂D`) lies in the interior
of `D`. -/
theorem cell_subset_interior_of_mem_interiorCellVertices {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    {D : Set ℂ} {k : ℤ} (hk : k ∈ interiorCellVertices ε η D) : cell ε η k ⊆ interior D := by
  simp only [interiorCellVertices, cellVertices, mem_sdiff, mem_ofPred_eq] at hk
  obtain ⟨⟨x, hxH, hxD⟩, hfr⟩ := hk
  have hfr' : ∀ y ∈ cell ε η k, y ∈ closure D → y ∈ interior D := fun y hy hyc =>
    by_contra fun hyi => hfr ⟨y, hy, show y ∈ closure D \ interior D from ⟨hyc, hyi⟩⟩
  refine (isPreconnected_cell hη k).subset_left_of_subset_union isOpen_interior
    isClosed_closure.isOpen_compl (Disjoint.mono_left interior_subset_closure disjoint_compl_right)
    ?_ ⟨x, hxH, hfr' x hxH (subset_closure hxD)⟩
  intro y hy
  by_cases hyc : y ∈ closure D
  · exact Or.inl (hfr' y hy hyc)
  · exact Or.inr hyc

/-- A cell meeting the cell of an interior vertex of `D` meets `D`. -/
theorem mem_cellVertices_of_inter_cell {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {D : Set ℂ}
    {j k : ℤ} (hk : k ∈ interiorCellVertices ε η D) (hjk : (cell ε η j ∩ cell ε η k).Nonempty) :
    j ∈ cellVertices ε η D := by
  obtain ⟨y, hyj, hyk⟩ := hjk
  exact ⟨y, hyj, interior_subset (cell_subset_interior_of_mem_interiorCellVertices hη hk hyk)⟩

/-- For an edge multiplicity `m` whose edges join intersecting cells, the neighbours of an interior
vertex of `D` are vertices of `𝒢^ε(D)`. -/
theorem mem_cellVertices_of_mult_ne_zero {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    {m : ℤ → ℤ → ℕ} (hadj : ∀ j k, m k j ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) {D : Set ℂ}
    {k : ℤ} (hk : k ∈ interiorCellVertices ε η D) {j : ℤ} (hm : m k j ≠ 0) :
    j ∈ cellVertices ε η D :=
  mem_cellVertices_of_inter_cell hη hk (hadj j k hm)

/-- Almost surely, for every `ε > 0` and every domain `D`, the neighbours in the mated-CRT map
`𝒢^ε` (edge multiplicity `S.mult ε ω`, Definition 1.1) of an interior vertex of `D` are vertices of
`𝒢^ε(D)`: adjacent vertices have intersecting cells (`MatedCRT.adjacentCellsMeetAeStep`) and the
curve is continuous. -/
theorem MatedCRTEnv.IsValid.ae_mem_cellVertices_of_mult_ne_zero {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ (D : Set ℂ) (k j : ℤ), k ∈ interiorCellVertices ε (S.η ω) D →
      S.mult ε ω k j ≠ 0 → j ∈ cellVertices ε (S.η ω) D := by
  filter_upwards [TraceInputs68.ae_continuous_eta hS, adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS]
    with ω hη hadj
  intro ε hε D k j hk hm
  refine mem_cellVertices_of_mult_ne_zero hη (fun j' k' h => ?_) hk hm
  rw [inter_comm]
  exact hadj ε hε k' j' h

end MatedCRT
