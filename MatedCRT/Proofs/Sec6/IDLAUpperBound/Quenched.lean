import MatedCRT.Proofs.IDLA.Monotone
import MatedCRT.Proofs.Sec6.IterativeBound.Round
import MatedCRT.Proofs.Sec6.AbelianIDLA.Statement

/-!
# Proposition 6.1: the quenched bound (one environment)

For one environment (the map `m`, the curve `η` parametrized by `μ`-area, a harmonic ball `L = Λ_t ⊆ B_{ρ/3}` with
`μ(L) = t`, cells meeting `B_ρ` of diameter `≤ d`), `quenched_bound`: the probability that the cells of the IDLA
cluster `A(⌊t ε⁻¹⌋)` leave `B⁺_δ(L)` is at most the probability that the stopped lower bound
`B⁻_{δ₁}(L) ⊆ Ā(⌊t ε⁻¹⌋ → V^ε(L))` fails, plus the conclusion `F` of Lemma 6.10 for the clusters
`Θ̄ ⋐ B_{ρ/2}` with `B_{δ/4} ⊆ Θ̄` and `j ≤ ⌈δ₀ ε⁻¹⌉` walkers started in `cl(Θ)`, provided
`μ(L \ B⁻_{δ₁}(L)) < δ₀` (lines 2860-2921).

Proof: the Abelian property (Lemma 6.3, `walkersLaw_not_subset_le_round`) restarts the walkers stopped upon exiting
`V^ε(L)`. On the lower bound, there are fewer than `δ₀ ε⁻¹` of them (each cell has mass `ε`), they sit next to the
stopped cluster `Θ_ε`, and enlarging the occupied set to `Θ_ε ∪ V^ε(B_{δ/4})` (`idlaAggregate_univ_mono`) puts the
restarted aggregate in the frame of Lemma 6.10, whose conclusion confines the cells to `B⁺_δ(L)`.
-/

namespace MatedCRT

namespace IDLAUpperBound

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

/-! ### Cells -/

/-- Two points of a cell meeting `B_ρ` are at distance at most the cell-size bound. -/
theorem cell_dist_le {ε ρ d : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hcells : ∀ k ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η k) ≤ d) {k : ℤ}
    (hk : k ∈ cellVertices ε η (ball 0 ρ)) {x y : ℂ} (hx : x ∈ cell ε η k) (hy : y ∈ cell ε η k) :
    dist x y ≤ d := by
  have hb : Bornology.IsBounded (cell ε η k) := (isCompact_Icc.image hη).isBounded
  exact (dist_le_diam_of_mem hb hx hy).trans (hcells k hk)

theorem mem_cellVertices_of_subset {ε : ℝ} {η : ℝ → ℂ} {D D' : Set ℂ} (h : D ⊆ D') {k : ℤ}
    (hk : k ∈ cellVertices ε η D) : k ∈ cellVertices ε η D' := by
  obtain ⟨w, hwc, hwD⟩ := hk
  exact ⟨w, hwc, h hwD⟩

/-- Every cell has `μ`-mass `ε` (area parametrization). -/
theorem measure_cell {μ : Measure ℂ} {η : ℝ → ℂ} (harea : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (k : ℤ) :
    μ (cell ε η k) = ENNReal.ofReal ε := by
  have hlt : ε * ((k : ℝ) - 1) < ε * k := by
    rw [mul_sub, mul_one]
    linarith
  rw [cell, harea.2.2.2 _ _ hlt, show ε * (k : ℝ) - ε * ((k : ℝ) - 1) = ε by ring]

/-- `μ(Θ̄) ≤ ε |Θ|` for a finite vertex set `Θ`. -/
theorem measure_fillCells_le {μ : Measure ℂ} {η : ℝ → ℂ} (harea : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    {Θ : Set ℤ} (hfin : Θ.Finite) : μ (fillCells ε η Θ) ≤ ENNReal.ofReal (Θ.ncard * ε) := by
  have hfill : fillCells ε η Θ = ⋃ k ∈ hfin.toFinset, cell ε η k := by
    simp only [fillCells, Finite.mem_toFinset]
  rw [hfill]
  refine (measure_biUnion_finset_le _ _).trans (le_of_eq ?_)
  simp only [measure_cell harea hε, Finset.sum_const, nsmul_eq_mul]
  rw [ncard_eq_toFinset_card Θ hfin, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The cells cover the plane: `B_s ⊆ V^ε(B_s)‾`. -/
theorem ball_subset_fillCells {μ : Measure ℂ} {η : ℝ → ℂ} (harea : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (s : ℝ) : ball 0 s ⊆ fillCells ε η (cellVertices ε η (ball 0 s)) := by
  intro x hx
  obtain ⟨u, rfl⟩ := harea.2.2.1 x
  set k : ℤ := ⌈u / ε⌉ with hk
  have hk1 : (k : ℝ) - 1 < u / ε := by
    have := Int.ceil_lt_add_one (u / ε)
    linarith
  have h1 : ((k : ℝ) - 1) * ε < u := (lt_div_iff₀ hε).1 hk1
  have h2 : u ≤ (k : ℝ) * ε := (div_le_iff₀ hε).1 (Int.le_ceil (u / ε))
  have hu : η u ∈ cell ε η k :=
    ⟨u, ⟨by linarith [mul_comm ε ((k : ℝ) - 1)], by linarith [mul_comm ε (k : ℝ)]⟩, rfl⟩
  simp only [fillCells, mem_iUnion]
  exact ⟨k, ⟨η u, hu, hx⟩, hu⟩

/-- The cells of `Θ ∪ V^ε(B_s)`, `Θ ⊆ V^ε(L)`, lie within `d + s` of `L` and in `B̄_{ρ/3 + d}`. -/
theorem fillCells_union_subset {ε ρ d s : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hcells : ∀ k ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η k) ≤ d) {L : Set ℂ} (h0L : 0 ∈ L)
    (hLρ : L ⊆ ball 0 (ρ / 3)) (hs0 : 0 ≤ s) (hs : s ≤ ρ / 3) (hρ : 0 < ρ) {Θ : Set ℤ}
    (hΘ : Θ ⊆ cellVertices ε η L) :
    fillCells ε η (Θ ∪ cellVertices ε η (ball 0 s)) ⊆ cthickening (d + s) L ∩ closedBall 0 (ρ / 3 + d) := by
  intro x hx
  simp only [fillCells, mem_iUnion] at hx
  obtain ⟨k, hk, hxk⟩ := hx
  have hsub : ball (0 : ℂ) (ρ / 3) ⊆ ball 0 ρ := ball_subset_ball (by linarith)
  rcases hk with hk | hk
  · obtain ⟨y, hyc, hyL⟩ := hΘ hk
    have hkρ : k ∈ cellVertices ε η (ball 0 ρ) := ⟨y, hyc, hsub (hLρ hyL)⟩
    have hxy := cell_dist_le hη hcells hkρ hxk hyc
    have hy0 : dist y 0 < ρ / 3 := mem_ball.1 (hLρ hyL)
    refine ⟨mem_cthickening_of_dist_le x y _ L hyL (by linarith), mem_closedBall.2 ?_⟩
    linarith [dist_triangle x y 0]
  · obtain ⟨y, hyc, hyB⟩ := hk
    have hkρ : k ∈ cellVertices ε η (ball 0 ρ) := ⟨y, hyc, ball_subset_ball (by linarith) hyB⟩
    have hxy := cell_dist_le hη hcells hkρ hxk hyc
    have hy0 : dist y 0 < s := mem_ball.1 hyB
    refine ⟨mem_cthickening_of_dist_le x 0 _ L h0L (by linarith [dist_triangle x y 0]), mem_closedBall.2 ?_⟩
    linarith [dist_triangle x y 0]

/-- A cell meeting `B_ρ` and `B⁺_r(X)`, with `X` within `e` of `L`, lies in `B⁺_δ(L)` when `d + (r + e) ≤ δ`. -/
theorem cell_subset_outerNbhd {ε ρ d r e δ : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hcells : ∀ k ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η k) ≤ d) {L X : Set ℂ}
    (hX : X ⊆ cthickening e L) (hr : 0 ≤ r) (he : 0 ≤ e) (hd : 0 ≤ d) (hsum : d + (r + e) ≤ δ) {k : ℤ}
    (hk : k ∈ cellVertices ε η (outerNbhd r X)) (hkρ : k ∈ cellVertices ε η (ball 0 ρ)) :
    cell ε η k ⊆ outerNbhd δ L := by
  obtain ⟨y, hyc, hyX⟩ := hk
  have hy : y ∈ cthickening (r + e) L :=
    cthickening_cthickening_subset hr he L (cthickening_subset_of_subset r hX hyX)
  intro x hx
  have hxy : dist x y ≤ d := cell_dist_le hη hcells hkρ hx hyc
  have h1 : x ∈ cthickening d (cthickening (r + e) L) := mem_cthickening_of_dist_le x y d _ hy hxy
  exact cthickening_mono hsum L (cthickening_cthickening_subset hd (add_nonneg hr he) L h1)

/-! ### The quenched bound -/

/-- **The quenched bound of Proposition 6.1** (lines 2860-2921), for one environment. -/
theorem quenched_bound (m : ℤ → ℤ → ℕ) (hsrw : IsSrwPathLaw m) {ε t δ δ₀ δ₁ ρ d r : ℝ} (F : ℝ≥0∞)
    {η : ℝ → ℂ} {μ : Measure ℂ} {L : Set ℂ} (hε : 0 < ε) (ht : 0 < t) (hδ₀ : 0 < δ₀) (hρ : 0 < ρ)
    (hδρ : δ < ρ) (harea : IsAreaParametrized μ η) (h0L : 0 ∈ L) (hLρ : L ⊆ ball 0 (ρ / 3))
    (hμL : μ L = ENNReal.ofReal t) (hmass : μ (L \ innerNbhd δ₁ L) < ENNReal.ofReal δ₀)
    (hcells : ∀ k ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η k) ≤ d) (hd : 0 ≤ d) (hdρ : d < ρ / 6)
    (hr : 0 ≤ r) (hsum : d + (r + (d + δ / 4)) ≤ δ) (hδ : 0 < δ)
    (hF : ∀ Θ : Set ℤ, closure (fillCells ε η Θ) ⊆ ball 0 (ρ / 2) → ball 0 (δ / 4) ⊆ fillCells ε η Θ →
      ∀ j : ℕ, j ≤ ⌈δ₀ / ε⌉₊ → ∀ a : Fin j → ℤ, (∀ i, a i ∈ vClosure m Θ) →
        walkersLaw m a {xs | ¬ (idlaAggregate Θ univ (List.ofFn xs) ⊆
          cellVertices ε η (outerNbhd r (fillCells ε η Θ)) ∧
          cellVertices ε η (outerNbhd r (fillCells ε η Θ)) ⊆ cellVertices ε η (ball 0 ρ))} ≤ F) :
    walkersLaw m (fun _ : Fin ⌊t / ε⌋₊ => (0 : ℤ))
        {ys | ¬ fillCells ε η (idlaAggregate ∅ univ (List.ofFn ys)) ⊆ outerNbhd δ L} ≤
      walkersLaw m (fun _ : Fin ⌊t / ε⌋₊ => (0 : ℤ))
        {ys | ¬ innerNbhd δ₁ L ⊆ fillCells ε η (idlaAggregate ∅ (cellVertices ε η L) (List.ofFn ys))} + F := by
  have hη : Continuous η := harea.1
  set Θ' := cellVertices ε η L with hΘ'
  set T : Set ℤ := {k | cell ε η k ⊆ outerNbhd δ L} with hT
  set S := cellVertices ε η (ball 0 (δ / 4)) with hS
  set n := ⌊t / ε⌋₊ with hn
  have h0Θ' : (0 : ℤ) ∈ Θ' := ⟨0, ⟨0, ⟨by simp [hε.le], by simp⟩, harea.2.1⟩, h0L⟩
  have hev : {ys : Fin n → ℕ → ℤ | ¬ fillCells ε η (idlaAggregate ∅ univ (List.ofFn ys)) ⊆ outerNbhd δ L} =
      {ys | ¬ idlaAggregate ∅ univ (List.ofFn ys) ⊆ T} := by
    ext ys
    exact not_congr iUnion₂_subset_iff
  rw [hev]
  set G : Set (Fin n → ℕ → ℤ) := {xs | innerNbhd δ₁ L ⊆ fillCells ε η (idlaAggregate ∅ Θ' (List.ofFn xs)) ∧
    ∀ x ∈ List.ofFn xs, x 0 = 0 ∧ ∀ k, x (k + 1) = x k ∨ m (x k) (x (k + 1)) ≠ 0} with hG
  refine (IterativeBound.walkersLaw_not_subset_le_round (AbelianIDLA.isAbelianIDLA m) (empty_subset Θ')
    (fun _ : Fin n => (0 : ℤ)) T G F ?_).trans (add_le_add ?_ le_rfl)
  · intro xs hxs
    obtain ⟨hLB, hpx⟩ := hxs
    set Θx := idlaAggregate ∅ Θ' (List.ofFn xs) with hΘx
    set Px := idlaStopped ∅ Θ' (List.ofFn xs) with hPx
    have hcard := foldl_idlaStep_card Θ' (List.ofFn xs) (∅, []) finite_empty
    have hfin : Θx.Finite := hcard.1
    have hcount : Θx.ncard + Px.length ≤ n := by
      have h := hcard.2
      simp only [ncard_empty, List.length_nil, List.length_ofFn, zero_add] at h
      exact h
    have hsub : Θx ⊆ Θ' := by
      have h := foldl_idlaStep_subset Θ' (List.ofFn xs) (∅, [])
      simp only [empty_union] at h
      exact h
    have hadj : ∀ b ∈ Px, ∃ c ∈ Θx, m c b ≠ 0 :=
      foldl_idlaStep_stopped_adj m 0 (List.ofFn xs) (∅, []) hpx (mem_union_right _ h0Θ')
        (fun b hb => by simp at hb)
    -- the number of restarted walkers
    have hPlen : Px.length ≤ ⌈δ₀ / ε⌉₊ := by
      have hinner : μ (innerNbhd δ₁ L) ≤ ENNReal.ofReal (Θx.ncard * ε) :=
        (measure_mono hLB).trans (measure_fillCells_le harea hε hfin)
      have hnt : (n : ℝ) * ε ≤ t := by
        have h := Nat.floor_le (div_nonneg ht.le hε.le)
        rwa [le_div_iff₀ hε] at h
      have hcountR : (Θx.ncard : ℝ) + Px.length ≤ n := by exact_mod_cast hcount
      have hfinite : μ (innerNbhd δ₁ L) ≠ ⊤ :=
        ((measure_mono fun y (hy : y ∈ innerNbhd δ₁ L) => hy.1).trans_lt
          (hμL ▸ ENNReal.ofReal_lt_top)).ne
      have hprod := mul_le_mul_of_nonneg_right hcountR hε.le
      have key : ENNReal.ofReal (Px.length * ε) + μ (innerNbhd δ₁ L) ≤
          μ (L \ innerNbhd δ₁ L) + μ (innerNbhd δ₁ L) := by
        calc ENNReal.ofReal (Px.length * ε) + μ (innerNbhd δ₁ L)
            ≤ ENNReal.ofReal (Px.length * ε) + ENNReal.ofReal (Θx.ncard * ε) := add_le_add le_rfl hinner
          _ = ENNReal.ofReal (Px.length * ε + Θx.ncard * ε) :=
              (ENNReal.ofReal_add (by positivity) (by positivity)).symm
          _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal (by linarith)
          _ = μ L := hμL.symm
          _ ≤ μ ((L \ innerNbhd δ₁ L) ∪ innerNbhd δ₁ L) := by
              rw [sdiff_union_self]
              exact measure_mono subset_union_left
          _ ≤ μ (L \ innerNbhd δ₁ L) + μ (innerNbhd δ₁ L) := measure_union_le _ _
      have hlt : ENNReal.ofReal (Px.length * ε) < ENNReal.ofReal δ₀ :=
        (ENNReal.le_of_add_le_add_right hfinite key).trans_lt hmass
      have hlt' : (Px.length : ℝ) * ε < δ₀ := (ENNReal.ofReal_lt_ofReal_iff hδ₀).1 hlt
      have hle : (Px.length : ℝ) ≤ ⌈δ₀ / ε⌉₊ := ((lt_div_iff₀ hε).2 hlt').le.trans (Nat.le_ceil _)
      exact_mod_cast hle
    -- the geometry of `Θx ∪ V^ε(B_{δ/4})`
    have hgeo := fillCells_union_subset (s := δ / 4) hη hcells h0L hLρ (by linarith) (by linarith) hρ hsub
    have hclosure : closure (fillCells ε η (Θx ∪ S)) ⊆ ball 0 (ρ / 2) := by
      refine (closure_minimal (fun x hx => (hgeo hx).2) isClosed_closedBall).trans ?_
      exact closedBall_subset_ball (by linarith)
    have hball : ball 0 (δ / 4) ⊆ fillCells ε η (Θx ∪ S) :=
      (ball_subset_fillCells harea hε (δ / 4)).trans (biUnion_subset_biUnion_left subset_union_right)
    have hclos : ∀ i : Fin Px.length, Px.get i ∈ vClosure m (Θx ∪ S) := by
      intro i
      obtain ⟨c, hc, hcb⟩ := hadj _ (List.get_mem Px i)
      by_cases hb : Px.get i ∈ Θx ∪ S
      · exact Or.inl hb
      · exact Or.inr ⟨hb, c, Or.inl hc, hcb⟩
    calc walkersLaw m (fun i : Fin Px.length => Px.get i)
          {ys | ¬ idlaAggregate Θx univ (List.ofFn ys) ⊆ T}
        ≤ walkersLaw m (fun i : Fin Px.length => Px.get i)
          {ys | ¬ idlaAggregate (Θx ∪ S) univ (List.ofFn ys) ⊆ T} := by
          refine measure_mono fun ys hys hc => hys ?_
          exact (idlaAggregate_univ_mono subset_union_left _).trans hc
      _ ≤ walkersLaw m (fun i : Fin Px.length => Px.get i)
          {ys | ¬ (idlaAggregate (Θx ∪ S) univ (List.ofFn ys) ⊆
            cellVertices ε η (outerNbhd r (fillCells ε η (Θx ∪ S))) ∧
            cellVertices ε η (outerNbhd r (fillCells ε η (Θx ∪ S))) ⊆ cellVertices ε η (ball 0 ρ))} := by
          refine measure_mono fun ys hys hc => hys ?_
          intro k hk
          exact cell_subset_outerNbhd hη hcells (fun x hx => (hgeo hx).1) hr (by linarith) hd hsum
            (hc.1 hk) (hc.2 (hc.1 hk))
      _ ≤ F := hF (Θx ∪ S) hclosure hball Px.length hPlen _ hclos
  · have hpath : ∀ᵐ xs ∂walkersLaw m (fun _ : Fin n => (0 : ℤ)), ∀ x ∈ List.ofFn xs,
        x 0 = 0 ∧ ∀ k, x (k + 1) = x k ∨ m (x k) (x (k + 1)) ≠ 0 := by
      have h : ∀ i, ∀ᵐ xs ∂walkersLaw m (fun _ : Fin n => (0 : ℤ)),
          xs i 0 = 0 ∧ ∀ k, xs i (k + 1) = xs i k ∨ m (xs i k) (xs i (k + 1)) ≠ 0 := by
        intro i
        unfold walkersLaw
        exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => srwLaw m 0) (i := i)).eventually (hsrw 0)
      filter_upwards [ae_all_iff.2 h] with xs hxs x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact hxs i
    have hnull := ae_iff.1 hpath
    calc walkersLaw m (fun _ : Fin n => (0 : ℤ)) Gᶜ
        ≤ walkersLaw m (fun _ : Fin n => (0 : ℤ))
          ({ys | ¬ innerNbhd δ₁ L ⊆ fillCells ε η (idlaAggregate ∅ Θ' (List.ofFn ys))} ∪
            {xs | ¬ ∀ x ∈ List.ofFn xs, x 0 = 0 ∧ ∀ k, x (k + 1) = x k ∨ m (x k) (x (k + 1)) ≠ 0}) := by
          refine measure_mono fun xs hxs => ?_
          by_contra hc
          rw [mem_union, not_or] at hc
          exact hxs ⟨not_not.1 hc.1, not_not.1 hc.2⟩
      _ ≤ _ := measure_union_le _ _
      _ = _ := by rw [hnull, add_zero]

end IDLAUpperBound

end MatedCRT
