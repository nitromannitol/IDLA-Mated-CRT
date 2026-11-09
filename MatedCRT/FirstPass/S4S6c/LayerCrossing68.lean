import MatedCRT.FirstPass.S4S6c.UniformLayer68

/-!
# The deterministic layer crossing of the printed Lemma 6.7 (q2, task fp-S4S6c-envscaling-6-7-6-8)

Source: LEMMA68.md, "Proof of Lemma 6.7", the geometric crossing. With `K = Ā = fillCells ε η Θ`, `G = K + B_{r/2}`
(an open set), the layer is `L = V(∂G)` and the window is `W = V(K + B_r)` (cell vertices, `Defs/Map.lean`).

Deterministic statement (`layer_crossing`): a path `x` from `a ∈ cl Θ` whose consecutive vertices are joined by edges
of the map (`m (x n) (x (n+1)) ≠ 0`), whose edges join cells that meet (`hadj`), whose boundary cells of `Θ` have
diameter `< r/2` (`hdiam`), and which leaves `W` at some time, hits `L` at some time `k` strictly before its exit from `W`.

Proof (LEMMA68.md): `cell(x_0) ⊆ G`; the first index `M` with `cell(x_M) ⊄ G` satisfies `M ≤ N` (`N` the exit time of
`W`); the connected set `cell(x_M)` meets `G` (at a point of `cell(x_{M-1})`) and `Gᶜ`, hence meets the frontier of `G`;
so `x_M ∈ L` and `x_M ∈ W` (the frontier lies in `K + B_r`), giving `M < N`.

The adjacency input `hadj` is `AdjacentCellsMeetAeStep` (a.s.) and `hdiam` comes from `CellSizeEstimateStmt`; both enter
as hypotheses here, the probabilistic part is in later files.
-/

open MeasureTheory Set Function Metric Topology
open scoped ENNReal

namespace MatedCRT
namespace LayerCrossing68

open MatedCRT.UniformLayer68

variable {ε : ℝ} {η : ℝ → ℂ}

lemma isPreconnected_cell (hη : Continuous η) (k : ℤ) : IsPreconnected (cell ε η k) :=
  isPreconnected_Icc.image η hη.continuousOn

lemma isCompact_cell (hη : Continuous η) (k : ℤ) : IsCompact (cell ε η k) :=
  isCompact_Icc.image hη

lemma cell_nonempty (hε : 0 < ε) (k : ℤ) : (cell ε η k).Nonempty := by
  have hk : ε * ((k : ℝ) - 1) ≤ ε * (k : ℝ) :=
    mul_le_mul_of_nonneg_left (by linarith) hε.le
  exact (Set.nonempty_Icc.2 hk).image η

lemma mem_cellVertices_iff {D : Set ℂ} {k : ℤ} :
    k ∈ cellVertices ε η D ↔ (cell ε η k ∩ D).Nonempty :=
  Iff.rfl

lemma subset_fillCells {Θ : Set ℤ} {k : ℤ} (hk : k ∈ Θ) : cell ε η k ⊆ fillCells ε η Θ :=
  fun _ hz => mem_iUnion₂.2 ⟨k, hk, hz⟩

lemma thickening_sub_of_le {E : Set ℂ} {δ δ' : ℝ} (h : δ ≤ δ') :
    thickening δ E ⊆ thickening δ' E := by
  intro z hz
  rw [mem_thickening_iff] at hz ⊢
  obtain ⟨c, hc, hd⟩ := hz
  exact ⟨c, hc, lt_of_lt_of_le hd h⟩

/-- The closure of the `δ`-neighbourhood lies in the `δ'`-neighbourhood for `δ < δ'`. -/
lemma closure_thickening_subset {E : Set ℂ} {δ δ' : ℝ} (h : δ < δ') :
    closure (thickening δ E) ⊆ thickening δ' E := by
  intro f hf
  rw [Metric.mem_closure_iff] at hf
  obtain ⟨b, hbG, hfb⟩ := hf (δ' - δ) (by linarith)
  rw [mem_thickening_iff] at hbG ⊢
  obtain ⟨c, hcE, hbc⟩ := hbG
  exact ⟨c, hcE, by linarith [dist_triangle f b c]⟩

/-- A cell meeting `K` and of diameter `< δ` lies in the `δ`-neighbourhood of `K` (cells are bounded: `η` continuous). -/
lemma cell_subset_thickening_of_meets (hη : Continuous η) {k : ℤ} {K : Set ℂ} {δ : ℝ}
    (hmeet : (cell ε η k ∩ K).Nonempty) (hdiam : diam (cell ε η k) < δ) :
    cell ε η k ⊆ thickening δ K := by
  obtain ⟨p, hpc, hpK⟩ := hmeet
  intro z hz
  rw [mem_thickening_iff]
  exact ⟨p, hpK, lt_of_le_of_lt (dist_le_diam_of_mem (isCompact_cell hη k).isBounded hz hpc) hdiam⟩

open Classical in
/-- The exit time of a path from `W` (`vExitTime`) is a natural number `N` with `x N ∉ W` and `x j ∈ W` for `j < N`. -/
lemma exists_exit_spec {W : Set ℤ} {x : ℕ → ℤ} (h : ∃ n, x n ∉ W) :
    ∃ N : ℕ, vExitTime W x = (N : ℕ∞) ∧ x N ∉ W ∧ ∀ j : ℕ, j < N → x j ∈ W := by
  refine ⟨Nat.find h, ?_, Nat.find_spec h, fun j hj => ?_⟩
  · simp [vExitTime, h]
  · by_contra hc
    exact Nat.find_min h hj hc

open Classical in
/-- If `x M ∈ L` then the first visit time to `L` is some `k ≤ M`. -/
lemma exists_layerHit_le {L : Set ℤ} {x : ℕ → ℤ} {M : ℕ} (hM : x M ∈ L) :
    ∃ k : ℕ, layerHit L x = (k : ℕ∞) ∧ k ≤ M := by
  have h : ∃ n, x n ∈ L := ⟨M, hM⟩
  refine ⟨Nat.find h, ?_, Nat.find_min' h hM⟩
  simp [layerHit, h]

open Classical in
/-- The least index at which a predicate fails. -/
lemma exists_first {P : ℕ → Prop} (h : ∃ j, ¬ P j) :
    ∃ M : ℕ, ¬ P M ∧ (∀ j : ℕ, j < M → P j) ∧ ∀ j : ℕ, ¬ P j → M ≤ j :=
  ⟨Nat.find h, Nat.find_spec h, fun _ hj => not_not.1 (Nat.find_min h hj), fun _ hj => Nat.find_min' h hj⟩

/-- **Deterministic layer crossing** (LEMMA68.md, "Proof of Lemma 6.7"; the `hcross` input of
`UniformLayer68.srwLaw_visit_ge_of_layer`). -/
theorem layer_crossing (m : ℤ → ℤ → ℕ) (hη : Continuous η) (hε : 0 < ε) {r : ℝ} (hr : 0 < r)
    (Θ : Set ℤ) (a : ℤ) (ha : a ∈ vClosure m Θ)
    (hadj : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hdiam : ∀ k ∈ vBoundary m Θ, diam (cell ε η k) < r / 2)
    (x : ℕ → ℤ) (hx0 : x 0 = a) (hstep : ∀ n : ℕ, m (x n) (x (n + 1)) ≠ 0)
    (hexit : ∃ n : ℕ, x n ∉ cellVertices ε η (thickening r (fillCells ε η Θ))) :
    ∃ k : ℕ, layerHit (cellVertices ε η (frontier (thickening (r / 2) (fillCells ε η Θ)))) x = (k : ℕ∞) ∧
      (k : ℕ∞) < vExitTime (cellVertices ε η (thickening r (fillCells ε η Θ))) x := by
  set K := fillCells ε η Θ with hKdef
  set G := thickening (r / 2) K with hGdef
  have hGo : IsOpen G := isOpen_thickening
  have hKG : K ⊆ G := self_subset_thickening (by linarith) K
  have hGW : G ⊆ thickening r K := thickening_sub_of_le (by linarith)
  -- the start cell lies in `G`
  have hstart : cell ε η a ⊆ G := by
    unfold vClosure at ha
    rcases ha with haΘ | ⟨haΘ', b, hbΘ, hmba⟩
    · exact (subset_fillCells haΘ).trans hKG
    · obtain ⟨p, hpb, hpa⟩ := hadj b a hmba
      exact cell_subset_thickening_of_meets hη ⟨p, hpa, subset_fillCells hbΘ hpb⟩
        (hdiam a ⟨haΘ', b, hbΘ, hmba⟩)
  have hP0 : cell ε η (x 0) ⊆ G := by
    rw [hx0]
    exact hstart
  -- the exit time from `W`
  obtain ⟨N, hvN, hNW, hlt⟩ := exists_exit_spec hexit
  -- the first index whose cell leaves `G`
  have hNnot : ¬ (cell ε η (x N) ⊆ G) := by
    intro hsub
    obtain ⟨z, hz⟩ := cell_nonempty (η := η) hε (x N)
    exact hNW (mem_cellVertices_iff.2 ⟨z, hz, hGW (hsub hz)⟩)
  obtain ⟨M, hPM, hPlt, hMN⟩ := exists_first (P := fun j => cell ε η (x j) ⊆ G) ⟨N, hNnot⟩
  have hM0 : M ≠ 0 := by
    intro h0
    apply hPM
    rw [h0]
    exact hP0
  obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
  have hPj : cell ε η (x j) ⊆ G := hPlt j (Nat.lt_succ_self j)
  -- the cell of `x (j+1)` is connected, meets `G` and leaves `G`
  have hconn := isPreconnected_cell (ε := ε) hη (x (j + 1))
  obtain ⟨q, hqc, hqG⟩ := Set.not_subset.1 hPM
  obtain ⟨p, hpj, hpc⟩ := hadj (x j) (x (j + 1)) (hstep j)
  have hpG : p ∈ G := hPj hpj
  -- the frontier of `G` meets the cell of `x (j+1)`
  have hfr : ∃ f ∈ cell ε η (x (j + 1)), f ∈ frontier G := by
    by_contra hcon
    push Not at hcon
    have hdich : ∀ z ∈ cell ε η (x (j + 1)), z ∈ G ∨ z ∉ closure G := by
      intro z hz
      by_cases hzG : z ∈ G
      · exact Or.inl hzG
      · right
        intro hzc
        apply hcon z hz
        rw [frontier, hGo.interior_eq]
        exact ⟨hzc, hzG⟩
    have hres := hconn G (closure G)ᶜ hGo isClosed_closure.isOpen_compl
      (fun z hz => hdich z hz) ⟨p, hpc, hpG⟩
      ⟨q, hqc, (hdich q hqc).resolve_left hqG⟩
    obtain ⟨z, -, hzG, hzc⟩ := hres
    exact hzc (subset_closure hzG)
  obtain ⟨f, hfc, hff⟩ := hfr
  -- the layer point `x (j+1)` lies in `W` and in `L`
  have hWf : x (j + 1) ∈ cellVertices ε η (thickening r K) :=
    mem_cellVertices_iff.2 ⟨f, hfc, closure_thickening_subset (by linarith) (frontier_subset_closure hff)⟩
  have hLf : x (j + 1) ∈ cellVertices ε η (frontier G) :=
    mem_cellVertices_iff.2 ⟨f, hfc, hff⟩
  have hlt' : j + 1 < N := lt_of_le_of_ne (hMN N hNnot) (fun h => hNW (h ▸ hWf))
  obtain ⟨k, hk, hkle⟩ := exists_layerHit_le hLf
  refine ⟨k, hk, ?_⟩
  rw [hvN]
  exact_mod_cast lt_of_le_of_lt hkle hlt'

#print axioms MatedCRT.LayerCrossing68.layer_crossing

end LayerCrossing68
end MatedCRT
