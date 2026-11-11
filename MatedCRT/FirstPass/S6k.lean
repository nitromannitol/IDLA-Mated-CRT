import Mathlib
import MatedCRT.FirstPass.S4S6c.FrontierSeparation
import MatedCRT.FirstPass.S6e.GeometryId
import MatedCRT.FirstPass.S6e.Admissible

/-!
# FIRST PASS: Lemma 6.8 reduction, steps 2 and 3

Relation of the printed Lemma 6.8 to `UniformConstantOrderLowerBoundStmt` (`FirstPass/S6d.lean:95`). Written source:
 lines 498-512 (steps 1-4) and the reduction paragraph after the printed
Lemma 6.8 (corrected paper `lemma:constant-order-lower-bound`, proof, lines 2798-2810: the trace of the walk from
`a ∈ cl(Θ)` contains the trace from a boundary site `b ∈ V(∂(Θ̄ + B_{r/2}))` by the strong Markov property and the
cell-size estimate `lemma:cell-size-estimate`).

* Step 3, `sparsity_of_card_bound` (and `sparsity_of_card_bound_set`): the global cardinality bound
  `|A| < s₁ r^(2β)/ε` on `A = S' \ Θ` gives the local sparsity clause (15) of `Lemma68Admissible.Admissible` at the
  radius `x = r`, since the sparsity radius `t_B = (|B| ε / s₁)^{1/(2β)}` is `< r` for every `B ⊆ A`.
* Step 2, `start_frontier_before_exit`: from `a ∈ vClosure Θ`, almost surely the walk meets a cell of the middle
  boundary `V(∂(Θ̄ + B_{r/2}))` at some time before its exit from `W = V(Θ̄ + B_r)`; the first such vertex `b`
  satisfies the boundary-start clauses (12) of `Lemma68Admissible.Admissible` at `x = r`
  (`clause12_of_frontier`). The discrete part is `FrontierSeparation.exists_frontierVerts_before_exit` (printed proof
  of Lemma 6.7, LEMMA68 lines 514-548: connected cells, adjacent cells meet, small start cell).

Named inputs of the statements (hypotheses, not proved here): the adjacency of cells of the map (`hadj`, the pointwise
form of `FrozenAdjacentCellsMeetAe`, `FirstPass/Frozen/S1S2S8SA.lean`, DMS14 Lemma 8.8); the cell-size bound at the
radius scale (`hcs`, from `CellSizeEstimateStmt`, Draft Lemma 2.8); the closure of the filled set in a ball (`hK`);
the almost sure finiteness of the exit time from `W` (`hexit`); the finiteness of `S' \ Θ` (`hfin`).
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace MatedCRT

namespace S6k

open Lemma68Admissible Lemma68Geometry Lemma68GeometryId FrontierSeparation

/-! ## Step 3: the global cardinality bound gives the local sparsity clause (15) -/

/-- **Step 3 (sparsity).** For a finite set `A` with `|A| < s₁ r^(2β)/ε` (the cardinality bound of
`UniformConstantOrderLowerBoundStmt`, with `β = chosenBetaMinus γ`), every nonempty `B ⊆ A` satisfies the sparsity
clause (15) of `Lemma68Admissible.Admissible` at any radius `x ≥ r`: the second alternative `t_B < x` holds. -/
theorem sparsity_of_card_bound {ε s1 β r x : ℝ} (η : ℝ → ℂ) (A : Finset ℤ)
    (hε : 0 < ε) (hs1 : 0 < s1) (hβ : 0 < β) (hr : 0 < r)
    (hcard : (A.card : ℝ) < s1 * r ^ (2 * β) / ε) (hx : r ≤ x) :
    ∀ B ⊆ A, B.Nonempty → x ≤ cRad ε η B ∨ tRad ε s1 β B < x := by
  intro B hBA _
  right
  have hBcard : (B.card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hBA
  have h1 : (A.card : ℝ) * ε < s1 * r ^ (2 * β) := (lt_div_iff₀ hε).1 hcard
  have h2 : (B.card : ℝ) * ε < s1 * r ^ (2 * β) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hBcard hε.le) h1
  have h3 : (B.card : ℝ) * ε / s1 < r ^ (2 * β) := by
    rw [div_lt_iff₀ hs1]
    linarith
  have h2β : (2 * β) ≠ 0 := (by linarith : (0 : ℝ) < 2 * β).ne'
  have hexp : 0 < 1 / (2 * β) := one_div_pos.2 (by linarith)
  have h4 : ((B.card : ℝ) * ε / s1) ^ (1 / (2 * β)) < (r ^ (2 * β)) ^ (1 / (2 * β)) :=
    Real.rpow_lt_rpow (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hε.le) hs1.le) h3 hexp
  have h5 : (r ^ (2 * β)) ^ (1 / (2 * β)) = r := by
    rw [← Real.rpow_mul hr.le, mul_one_div_cancel h2β, Real.rpow_one]
  unfold tRad
  exact lt_of_lt_of_le (h4.trans_eq h5) hx

/-- **Step 3, set form.** The same for `A = S' \ Θ` with `S'`, `Θ` sets, as in the quantifier block of
`UniformConstantOrderLowerBoundStmt`. Finiteness of `S' \ Θ` is needed: `Set.ncard` of an infinite set is `0`, so the
printed bound would be vacuous for infinite `S' \ Θ`. -/
theorem sparsity_of_card_bound_set {ε s1 β r x : ℝ} (η : ℝ → ℂ) {S' Θ : Set ℤ}
    (hfin : (S' \ Θ).Finite) (hε : 0 < ε) (hs1 : 0 < s1) (hβ : 0 < β) (hr : 0 < r)
    (hcard : ((S' \ Θ).ncard : ℝ) < s1 * r ^ (2 * β) / ε) (hx : r ≤ x) :
    ∀ B ⊆ hfin.toFinset, B.Nonempty → x ≤ cRad ε η B ∨ tRad ε s1 β B < x := by
  apply sparsity_of_card_bound η hfin.toFinset hε hs1 hβ hr _ hx
  rw [Set.ncard_eq_toFinset_card _ hfin] at hcard
  exact hcard

/-! ## Step 2: from `vClosure Θ` the walk meets the middle boundary before exiting `W` -/

/-- The closed cell `H^ε_k = η([ε(k-1), εk])` is compact for continuous `η`. -/
lemma cell_isCompact (ε : ℝ) {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) : IsCompact (cell ε η k) := by
  unfold cell
  exact isCompact_Icc.image hη

/-- The cells are closed, so the closed cells of `FrontierSeparation` are the cells. -/
lemma cell_isClosed (ε : ℝ) {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) : IsClosed (cell ε η k) :=
  (cell_isCompact ε hη k).isClosed

/-- The cells are connected (continuous image of an interval). -/
lemma cell_isPreconnected (ε : ℝ) {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) :
    IsPreconnected (cell ε η k) := by
  unfold cell
  exact isPreconnected_Icc.image _ hη.continuousOn

/-- The cells are nonempty for `ε > 0`. -/
lemma cell_nonempty {ε : ℝ} (hε : 0 < ε) (η : ℝ → ℂ) (k : ℤ) : (cell ε η k).Nonempty := by
  refine ⟨η (ε * k), ?_⟩
  unfold cell
  exact ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩

/-- The vertices of the cells meeting `U`, with the closed cells, are the `cellVertices` of `U`. -/
lemma meetVerts_eq (ε : ℝ) {η : ℝ → ℂ} (hη : Continuous η) (U : Set ℂ) :
    FrontierSeparation.meetVerts (cell ε η) U = cellVertices ε η U := by
  ext k
  show (closure (cell ε η k) ∩ U).Nonempty ↔ (cell ε η k ∩ U).Nonempty
  rw [(cell_isClosed ε hη k).closure_eq]

/-- The frontier vertices (cells meeting `frontier U`) are the `cellVertices` of `frontier U`. -/
lemma frontierVerts_eq (ε : ℝ) {η : ℝ → ℂ} (hη : Continuous η) (U : Set ℂ) :
    FrontierSeparation.frontierVerts (cell ε η) U = cellVertices ε η (frontier U) := by
  ext k
  show (closure (cell ε η k) ∩ frontier U).Nonempty ↔ (cell ε η k ∩ frontier U).Nonempty
  rw [(cell_isClosed ε hη k).closure_eq]

/-- A cell of a vertex of `vClosure Θ` meets the closure of the filled set `K = ⋃_{w ∈ Θ} H_w`: either the vertex is in
`Θ`, or it is a neighbour of `Θ` and the adjacency (cells of adjacent vertices meet) applies. -/
lemma exists_cell_meet_closure_fill {m : ℤ → ℤ → ℕ} {Θ : Finset ℤ} {a : ℤ} {ε : ℝ} {η : ℝ → ℂ}
    (hadj : ∀ u v, m u v ≠ 0 → (cell ε η u ∩ cell ε η v).Nonempty) (hε : 0 < ε)
    (ha : a ∈ vClosure m (↑Θ : Set ℤ)) :
    (cell ε η a ∩ closure (fillCells ε η ↑Θ)).Nonempty := by
  unfold vClosure vBoundary at ha
  rcases ha with ha | ⟨_, w, hw, hmw⟩
  · obtain ⟨q, hq⟩ := cell_nonempty hε η a
    exact ⟨q, hq, subset_closure (Set.mem_biUnion ha hq)⟩
  · obtain ⟨q, hqw, hqa⟩ := hadj w a hmw
    exact ⟨q, hqa, subset_closure (Set.mem_biUnion hw hqw)⟩

/-- **Start clause.** For `a ∈ vClosure Θ`, the closed start cell lies in the open middle neighbourhood
`Θ̄ + B_{r/2} = thickening (r/2) K`: a cell has diameter `< r/2` (cell-size bound on the cells meeting `ball 0 ρ`),
and it meets `closure K ⊆ ball 0 ρ`. -/
lemma closure_cell_sub_thickening {m : ℤ → ℤ → ℕ} {Θ : Finset ℤ} {a : ℤ} {ε r ρ : ℝ} {η : ℝ → ℂ}
    (hη : Continuous η) (hε : 0 < ε)
    (hadj : ∀ u v, m u v ≠ 0 → (cell ε η u ∩ cell ε η v).Nonempty)
    (hK : closure (fillCells ε η ↑Θ) ⊆ ball 0 ρ)
    (hcs : ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) < r / 2)
    (ha : a ∈ vClosure m (↑Θ : Set ℤ)) :
    closure (cell ε η a) ⊆ thickening (r / 2) (fillCells ε η ↑Θ) := by
  rw [(cell_isClosed ε hη a).closure_eq]
  intro p hp
  obtain ⟨q, hqa, hqK⟩ := exists_cell_meet_closure_fill hadj hε ha
  have hdiam : diam (cell ε η a) < r / 2 := hcs a ⟨q, hqa, hK hqK⟩
  have hpq : dist p q < r / 2 :=
    lt_of_le_of_lt (dist_le_diam_of_mem (cell_isCompact ε hη a).isBounded hp hqa) hdiam
  obtain ⟨z, hzK, hqz⟩ := Metric.mem_closure_iff.1 hqK (r / 2 - dist p q) (by linarith)
  exact Metric.mem_thickening_iff.2 ⟨z, hzK, lt_of_le_of_lt (dist_triangle p q z) (by linarith)⟩

/-- The frontier of the open thickening `thickening s K` lies in the open thickening `thickening t K` for `s < t`. -/
lemma frontier_thickening_sub_thickening {K : Set ℂ} {s t : ℝ} (ht : 0 < t) (hst : s < t) :
    frontier (thickening s K) ⊆ thickening t K := by
  intro z hz
  have h : infEDist z K = ENNReal.ofReal s := frontier_thickening_subset K hz
  rw [mem_thickening_iff_infEDist_lt, h]
  exact (ENNReal.ofReal_lt_ofReal_iff ht).2 hst

/-- **Boundary-start clauses (12).** If the cell of `b` meets the middle boundary `frontier (thickening (r/2) K)`,
then `2 d_b ≤ r ≤ 2 M_b` (`d_b = dd`, `M_b = ddMax`), i.e. the clause (12) of
`Lemma68Admissible.Admissible` at the radius `x = r`. Here `d_b = inf_{u ∈ H_b} dist(u, K)` and
`M_b = sup_{u ∈ H_b} dist(u, K)`, and a point `z` of the frontier has `dist(z, K) = r/2`. -/
lemma clause12_of_frontier {η : ℝ → ℂ} {ε : ℝ} (hη : Continuous η) (hε : 0 < ε) {Θ : Finset ℤ} {r : ℝ}
    (hr : 0 < r) {b : ℤ} (hb : (cell ε η b ∩ frontier (thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty) :
    2 * dd ε η Θ b ≤ r ∧ r ≤ 2 * ddMax ε η Θ b := by
  obtain ⟨z, hzb, hzf⟩ := hb
  set K := fillCells ε η (↑Θ : Set ℤ) with hKdef
  have hz_inf : infEDist z K = ENNReal.ofReal (r / 2) := frontier_thickening_subset K hzf
  have hKne : K.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Metric.infEDist_empty] at hz_inf
    exact ENNReal.ofReal_ne_top hz_inf.symm
  have hcell_eq := cellDist_eq_iInf_cell hη hε Θ b
  have hcmax_eq := cellDistMax_eq_iSup_cell hη hε Θ b
  have hle : cellDist ε η Θ b ≤ ENNReal.ofReal (r / 2) := by
    rw [hcell_eq]
    exact (iInf₂_le z hzb).trans hz_inf.le
  have hge : ENNReal.ofReal (r / 2) ≤ cellDistMax ε η Θ b := by
    rw [hcmax_eq]
    exact hz_inf.ge.trans (le_iSup₂ (f := fun (u : ℂ) (_ : u ∈ cell ε η b) => infEDist u K) z hzb)
  have hmax_ne : cellDistMax ε η Θ b ≠ ⊤ := by
    obtain ⟨x0, _, hmax⟩ := (cell_isCompact ε hη b).exists_isMaxOn (cell_nonempty hε η b)
      (Metric.continuous_infEDist (s := K)).continuousOn
    obtain ⟨z0, hz0⟩ := hKne
    have hbd : cellDistMax ε η Θ b ≤ infEDist x0 K := by
      rw [hcmax_eq]
      exact iSup₂_le fun u hu => isMaxOn_iff.1 hmax u hu
    exact ne_top_of_le_ne_top (edist_ne_top x0 z0) (hbd.trans (Metric.infEDist_le_edist_of_mem hz0))
  have hr2 : 0 ≤ r / 2 := by linarith
  constructor
  · have h1 : (cellDist ε η Θ b).toReal ≤ r / 2 := ENNReal.toReal_le_of_le_ofReal hr2 hle
    unfold dd
    linarith
  · have h2 : r / 2 ≤ (cellDistMax ε η Θ b).toReal := (ENNReal.ofReal_le_iff_le_toReal hmax_ne).1 hge
    unfold ddMax
    linarith

/-- **Cell-size input of Step 2 (from `CellSizeEstimateStmt`, Draft Lemma 2.8).** If every cell meeting `ball 0 ρ` has
diameter `≤ ε^e` (the upper bound of `CellSizeEstimateStmt`, with `e = 2/(2+γ)² - ζ`), `ε < 1`, `10 ε^{ω₀} ≤ r`
and `ω₀ ≤ e`, then every such cell has diameter `< r/2`; this is the hypothesis `hcs` of
`start_frontier_before_exit`. -/
theorem diam_lt_half_of_cellSize {η : ℝ → ℂ} {ε r ρ ω₀ e : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hr : 10 * ε ^ ω₀ ≤ r) (he : ω₀ ≤ e)
    (hsize : ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) ≤ ε ^ e) :
    ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) < r / 2 := by
  intro k hk
  have h1 : diam (cell ε η k) ≤ ε ^ e := hsize k hk
  have h2 : ε ^ e ≤ ε ^ ω₀ := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le he
  have hpos : 0 < ε ^ ω₀ := Real.rpow_pos_of_pos hε0 _
  linarith

/-- **Step 2 (start before exit, almost surely).** Let `a ∈ vClosure Θ` and let the walk from `a` on the cell graph
`m` (the simple random walk `srwLaw m a`) exit the set `W = V(Θ̄ + B_r)` at finite time almost surely. Then almost
surely there is a first time `n` before the exit time of `W` at which the walk is in a cell meeting the middle boundary
`∂(Θ̄ + B_{r/2})`, and the vertex `x n` there satisfies the boundary-start clauses (12) of
`Lemma68Admissible.Admissible` at the radius `x = r`. -/
theorem start_frontier_before_exit {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {ε r ρ : ℝ} {Θ : Finset ℤ} {a : ℤ}
    (hη : Continuous η) (hε : 0 < ε) (hr : 0 < r)
    (hadj : ∀ u v, m u v ≠ 0 → (cell ε η u ∩ cell ε η v).Nonempty)
    (hK : closure (fillCells ε η ↑Θ) ⊆ ball 0 ρ)
    (hcs : ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) < r / 2)
    (ha : a ∈ vClosure m (↑Θ : Set ℤ))
    (hexit : ∀ᵐ x ∂srwLaw m a, vExitTime (cellVertices ε η (thickening r (fillCells ε η ↑Θ))) x ≠ ⊤) :
    ∀ᵐ x ∂srwLaw m a, ∃ n : ℕ,
      (n : ℕ∞) < vExitTime (cellVertices ε η (thickening r (fillCells ε η ↑Θ))) x ∧
      x n ∈ cellVertices ε η (frontier (thickening (r / 2) (fillCells ε η ↑Θ))) ∧
      (∀ j < n, x j ∉ cellVertices ε η (frontier (thickening (r / 2) (fillCells ε η ↑Θ)))) ∧
      2 * dd ε η Θ (x n) ≤ r ∧ r ≤ 2 * ddMax ε η Θ (x n) := by
  classical
  set K := fillCells ε η (↑Θ : Set ℤ) with hKdef
  set U1 := thickening (r / 2) K with hU1def
  set U2 := thickening r K with hU2def
  have hU1 : IsOpen U1 := isOpen_thickening
  have hU12 : U1 ⊆ U2 := thickening_mono (by linarith) K
  have hfr : frontier U1 ⊆ U2 := frontier_thickening_sub_thickening hr (by linarith)
  have hconn := cell_isPreconnected ε hη
  have hne := cell_nonempty hε η
  have hadj' : ∀ u v, m u v ≠ 0 → (closure (cell ε η u) ∩ closure (cell ε η v)).Nonempty := by
    intro u v h
    rw [(cell_isClosed ε hη u).closure_eq, (cell_isClosed ε hη v).closure_eq]
    exact hadj u v h
  have hstart : closure (cell ε η a) ⊆ U1 := closure_cell_sub_thickening hη hε hadj hK hcs ha
  have hmeet : FrontierSeparation.meetVerts (cell ε η) U2 = cellVertices ε η U2 := meetVerts_eq ε hη U2
  filter_upwards [FrontierSeparation.ae_srwStep_legal m a, srwLaw_ae_start m a, hexit] with x hstep hx0 hfin
  rw [← hmeet] at hfin
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hfin
  obtain ⟨n, hn1, hn2⟩ :=
    exists_frontierVerts_before_exit hU1 hU12 hfr hconn hne hadj' hstart x hx0 hstep hN.symm
  rw [hmeet] at hn1
  rw [frontierVerts_eq ε hη U1] at hn2
  have hP : ∃ n : ℕ, (n : ℕ∞) < vExitTime (cellVertices ε η U2) x ∧
      x n ∈ cellVertices ε η (frontier U1) := ⟨n, hn1, hn2⟩
  refine ⟨Nat.find hP, (Nat.find_spec hP).1, (Nat.find_spec hP).2, fun j hj hmem => ?_, ?_⟩
  · exact Nat.find_min hP hj ⟨lt_trans (ENat.natCast_lt_natCast.2 hj) (Nat.find_spec hP).1, hmem⟩
  · exact clause12_of_frontier hη hε hr (Nat.find_spec hP).2

/-! ## Admissibility of a middle-boundary start

`killed_eq_W` (equality `killed ε η Θ F0 r = W \ Θ` under `W ⊆ F0`) is already proved as
`Lemma68Relation.killed_eq_W` (`FirstPass/S6e/Relation.lean:121`, commit 4010091); it is not restated here. Only the
inclusion needed for admissibility is proved in this file. -/

/-- **Inclusion for the killed set.** If `W = V(Θ̄ + B_r) ⊆ F0`, then every vertex of `W \ Θ` lies in
`killed ε η Θ F0 r = {v ∈ F0 : d_v < r} \ Θ`: `d_v < r` because `v ∈ W` means
`d_v < r` by `cellVertices_thickening_eq`. -/
theorem sdiff_W_subset_killed {η : ℝ → ℂ} {ε r : ℝ} (hη : Continuous η) (hε : 0 < ε) {Θ F0 : Finset ℤ}
    (hF : cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) ⊆ (↑F0 : Set ℤ)) :
    cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) \ (↑Θ : Set ℤ) ⊆
      (killed ε η Θ F0 r : Set ℤ) := by
  rintro v ⟨hvW, hvΘ⟩
  have hv0 : v ∈ F0 := Finset.mem_coe.1 (hF hvW)
  have hvd : cellDist ε η Θ v < ENNReal.ofReal r := by
    rw [cellVertices_thickening_eq hη hε Θ r] at hvW
    exact hvW
  have hvr : dd ε η Θ v < r := ENNReal.toReal_lt_of_lt_ofReal hvd
  exact ⟨hv0, hvr, hvΘ⟩

/-- **Admissibility at a middle-boundary start (`frontier_admissible`).** Let `b` be a start vertex with
`d_b ≤ r/2 ≤ M_b` (the cell of `b` meets the middle boundary; `dd_bounds`), let `W ⊆ F0`, let the target satisfy
`A ⊆ W \ Θ`, and let `|A| < s₁ r^(2β)/ε`. Then `b` is admissible at the radius `x = r` in the sense of
`Lemma68Admissible.Admissible`: clause (12) at `b`, the inclusion `A ⊆ killed r`, and the sparsity clause (15). -/
theorem frontier_admissible {η : ℝ → ℂ} {ε r s1 β : ℝ} (hη : Continuous η) (hε : 0 < ε) (hs1 : 0 < s1)
    (hβ : 0 < β) (hr : 0 < r) {Θ F0 A : Finset ℤ} {b : ℤ}
    (hdd : dd ε η Θ b ≤ r / 2 ∧ r / 2 ≤ ddMax ε η Θ b)
    (hF : cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) ⊆ (↑F0 : Set ℤ))
    (hA : (↑A : Set ℤ) ⊆ cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) \ (↑Θ : Set ℤ))
    (hcard : (A.card : ℝ) < s1 * r ^ (2 * β) / ε) :
    Admissible ε η Θ F0 A b s1 β r := by
  unfold Admissible
  refine ⟨⟨by linarith [hdd.1], by linarith [hdd.2]⟩, hA.trans (sdiff_W_subset_killed hη hε hF), ?_⟩
  exact sparsity_of_card_bound η A hε hs1 hβ hr hcard le_rfl

end S6k

end MatedCRT
