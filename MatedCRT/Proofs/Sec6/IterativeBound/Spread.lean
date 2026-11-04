import MatedCRT.Proofs.Sec6.IterativeBound.Round

/-!
# Lemma 6.10: how far the aggregate spreads (Step 3, lines 2804-2815, and the cluster growth of Steps 1-2)

* `fillCells_subset_cthickening_of_subset`: a cluster absorbed inside `V^ε(Θ̄ + B_r)` fills at most
  `B⁺_{r+d}(Θ̄)` when the cells near `Θ̄` have diameter at most `d`.
* `aggRun_univ_subset_cellVertices` (Step 3): `n` walkers started in `cl(Θ)` and moving along edges, with the cells
  of adjacent vertices intersecting, are absorbed in `V^ε(B⁺_{(n-1)d}(Θ̄))`: each absorbed site is adjacent to the
  current aggregate, and each new cell reaches at most `d` further.
-/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

namespace IterativeBound

open Absorption

theorem outerNbhd_eq_cthickening (δ : ℝ) (X : Set ℂ) : outerNbhd δ X = cthickening δ X := rfl

theorem cell_bounded {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (a : ℤ) : Bornology.IsBounded (cell ε η a) :=
  (isCompact_Icc.image hη).isBounded

theorem cell_nonempty {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (a : ℤ) : (cell ε η a).Nonempty :=
  (nonempty_Icc.2 (by nlinarith)).image η

theorem cell_subset_fillCells {ε : ℝ} {η : ℝ → ℂ} {Θ : Set ℤ} {a : ℤ} (ha : a ∈ Θ) :
    cell ε η a ⊆ fillCells ε η Θ :=
  subset_biUnion_of_mem (u := fun k => cell ε η k) ha

/-- A cell of diameter at most `d` meeting `Z` lies in `B⁺_d(Z)`. -/
theorem cell_subset_cthickening {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {a : ℤ} {d : ℝ} {Z : Set ℂ}
    (hdiam : diam (cell ε η a) ≤ d) (hZ : (cell ε η a ∩ Z).Nonempty) : cell ε η a ⊆ cthickening d Z := by
  obtain ⟨z, hza, hzZ⟩ := hZ
  intro y hy
  exact mem_cthickening_of_dist_le y z d Z hzZ ((dist_le_diam_of_mem (cell_bounded hη a) hy hza).trans hdiam)

/-- A cluster absorbed inside `V^ε(Θ̄ + B_r)` fills at most `B⁺_{r+d}(Θ̄)`. -/
theorem fillCells_subset_cthickening_of_subset {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {ρ' r d : ℝ}
    (hr : 0 ≤ r) (hd : 0 ≤ d) {Θ A : Set ℤ}
    (hdiam : ∀ a ∈ cellVertices ε η (ball 0 ρ'), diam (cell ε η a) ≤ d)
    (hball : thickening r (fillCells ε η Θ) ⊆ ball 0 ρ')
    (hA : A ⊆ Θ ∪ cellVertices ε η (thickening r (fillCells ε η Θ))) :
    fillCells ε η A ⊆ cthickening (r + d) (fillCells ε η Θ) := by
  intro y hy
  simp only [fillCells, mem_iUnion, exists_prop] at hy
  obtain ⟨a, ha, hya⟩ := hy
  rcases hA ha with ha | ha
  · exact cthickening_mono (by linarith) _ (self_subset_cthickening _ (cell_subset_fillCells ha hya))
  · have hmeet : (cell ε η a ∩ thickening r (fillCells ε η Θ)).Nonempty := ha
    have hball' : a ∈ cellVertices ε η (ball 0 ρ') := by
      obtain ⟨z, hz1, hz2⟩ := hmeet
      exact ⟨z, hz1, hball hz2⟩
    have h1 := cell_subset_cthickening hη (hdiam a hball') hmeet hya
    have h2 : cthickening d (thickening r (fillCells ε η Θ)) ⊆ cthickening (d + r) (fillCells ε η Θ) :=
      (cthickening_subset_of_subset d (thickening_subset_cthickening r _)).trans (cthickening_cthickening_subset hd hr _)
    rw [add_comm r d]
    exact h2 h1

/-- The site where a walker leaves the aggregate `A ⊇ Θ` is adjacent to `A`, if the walker starts in `cl(Θ)` and
moves along edges. -/
theorem exists_adj_of_firstExitSite {m : ℤ → ℤ → ℕ} {Θ A : Set ℤ} (h1 : Θ ⊆ A) {x : ℕ → ℤ} {b : ℤ}
    (hx0 : x 0 ∈ vClosure m Θ) (hxadj : ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)
    (ho : firstExitSite A x = some b) : ∃ c ∈ A, m c b ≠ 0 := by
  have hbA : b ∉ A := not_mem_of_firstExitSite_eq_some ho
  obtain ⟨n, hn, -, hlt⟩ := firstExitSite_eq_some_iff.1 ho
  cases n with
  | zero =>
    rw [hn] at hx0
    rcases hx0 with hx0 | ⟨-, c, hc, hcb⟩
    · exact absurd (h1 hx0) hbA
    · exact ⟨c, h1 hc, hcb⟩
  | succ j =>
    have hj : x j ∈ A := hlt j (Nat.lt_succ_self j)
    refine ⟨x j, hj, ?_⟩
    rcases hxadj j with h | h
    · rw [hn] at h
      exact absurd (h ▸ hj) hbA
    · rw [hn] at h
      exact h

/-- The invariant of Step 3 after `i` walkers: the cells of the absorbed sites meet `B⁺_{(i-1)d}(Θ̄)` and lie in
`B⁺_{id}(Θ̄)`. -/
def SpreadInv (ε : ℝ) (η : ℝ → ℂ) (Θ A : Set ℤ) (d : ℝ) (i : ℕ) : Prop :=
  Θ ⊆ A ∧ ∀ c ∈ A, c ∉ Θ → (cell ε η c ∩ cthickening (((i : ℝ) - 1) * d) (fillCells ε η Θ)).Nonempty ∧
    cell ε η c ⊆ cthickening ((i : ℝ) * d) (fillCells ε η Θ)

theorem cell_subset_cthickening_of_spreadInv {ε : ℝ} {η : ℝ → ℂ} {Θ A : Set ℤ} {d : ℝ} {i : ℕ}
    (h : SpreadInv ε η Θ A d i) {c : ℤ} (hc : c ∈ A) :
    cell ε η c ⊆ cthickening ((i : ℝ) * d) (fillCells ε η Θ) := by
  by_cases hcΘ : c ∈ Θ
  · exact (cell_subset_fillCells hcΘ).trans (self_subset_cthickening _)
  · exact (h.2 c hc hcΘ).2

theorem aggRun_univ_spreadInv {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 ≤ ε)
    {ρ' d : ℝ} (hd : 0 ≤ d)
    (hcell : ∀ a b : ℤ, a ∈ cellVertices ε η (ball 0 ρ') → m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hdiam : ∀ a ∈ cellVertices ε η (ball 0 ρ'), diam (cell ε η a) ≤ d) {Θ : Set ℤ} :
    ∀ (l : List (ℕ → ℤ)) (A : Set ℤ) (i : ℕ), SpreadInv ε η Θ A d i →
      (∀ x ∈ l, x 0 ∈ vClosure m Θ ∧ ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0) →
      cthickening ((((i + l.length : ℕ) : ℝ) - 1) * d) (fillCells ε η Θ) ⊆ ball 0 ρ' →
      SpreadInv ε η Θ (aggRun univ A l) d (i + l.length)
  | [], A, i, h, _, _ => by simpa using h
  | x :: l, A, i, h, hl, hball => by
    obtain ⟨hx0, hxadj⟩ := hl x List.mem_cons_self
    have hl' : ∀ y ∈ l, y 0 ∈ vClosure m Θ ∧ ∀ n, y (n + 1) = y n ∨ m (y n) (y (n + 1)) ≠ 0 :=
      fun y hy => hl y (List.mem_cons_of_mem x hy)
    have hlen : i + (x :: l).length = (i + 1) + l.length := by simp only [List.length_cons]; omega
    rw [aggRun_cons, aggStep_eq, hlen]
    rw [hlen] at hball
    refine aggRun_univ_spreadInv hη hε hd hcell hdiam l _ (i + 1) ?_ hl' hball
    have hi : ((i : ℕ) : ℝ) * d ≤ ((i + 1 : ℕ) : ℝ) * d := by
      apply mul_le_mul_of_nonneg_right _ hd
      exact_mod_cast Nat.le_succ i
    have hsub : cthickening ((i : ℝ) * d) (fillCells ε η Θ) ⊆ ball 0 ρ' := by
      refine (cthickening_mono ?_ _).trans hball
      apply mul_le_mul_of_nonneg_right _ hd
      have : (0 : ℝ) ≤ l.length := Nat.cast_nonneg _
      push_cast
      linarith
    -- monotonicity of the invariant in `i`
    have hmono : SpreadInv ε η Θ A d (i + 1) := by
      refine ⟨h.1, fun c hc hcΘ => ⟨?_, ?_⟩⟩
      · obtain ⟨z, hz1, hz2⟩ := (h.2 c hc hcΘ).1
        refine ⟨z, hz1, cthickening_mono ?_ _ hz2⟩
        push_cast
        nlinarith
      · exact (h.2 c hc hcΘ).2.trans (cthickening_mono hi _)
    rcases ho : firstExitSite A x with _ | b
    · exact hmono
    · simp only [nextAgg, mem_univ, ↓reduceIte]
      obtain ⟨c, hcA, hcb⟩ := exists_adj_of_firstExitSite h.1 hx0 hxadj ho
      have hcell_c := cell_subset_cthickening_of_spreadInv h hcA
      have hcV : c ∈ cellVertices ε η (ball 0 ρ') := by
        obtain ⟨z, hz⟩ := cell_nonempty hε η c
        exact ⟨z, hz, hsub (hcell_c hz)⟩
      obtain ⟨z, hzc, hzb⟩ := hcell c b hcV hcb
      have hmeet : (cell ε η b ∩ cthickening ((i : ℝ) * d) (fillCells ε η Θ)).Nonempty :=
        ⟨z, hzb, hcell_c hzc⟩
      have hbV : b ∈ cellVertices ε η (ball 0 ρ') := ⟨z, hzb, hsub (hcell_c hzc)⟩
      refine ⟨h.1.trans subset_union_left, fun c' hc' hc'Θ => ?_⟩
      rcases hc' with hc' | hc'
      · exact hmono.2 c' hc' hc'Θ
      · rw [mem_singleton_iff] at hc'
        subst hc'
        refine ⟨?_, ?_⟩
        · simpa using hmeet
        · refine (cell_subset_cthickening hη (hdiam c' hbV) hmeet).trans ?_
          refine (cthickening_cthickening_subset hd (by positivity) _).trans (cthickening_mono ?_ _)
          push_cast
          linarith

/-- **Step 3**: `n` walkers started in `cl(Θ)` and moving along edges, the cells of adjacent vertices of
`V^ε(B_{ρ'})` intersecting and having diameter at most `d`, are absorbed in `V^ε(B⁺_{(n-1)d}(Θ̄))` provided
`B⁺_{(n-1)d}(Θ̄) ⊆ B_{ρ'}`. -/
theorem aggRun_univ_subset_cellVertices {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 ≤ ε)
    {ρ' d : ℝ} (hd : 0 ≤ d)
    (hcell : ∀ a b : ℤ, a ∈ cellVertices ε η (ball 0 ρ') → m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hdiam : ∀ a ∈ cellVertices ε η (ball 0 ρ'), diam (cell ε η a) ≤ d) {Θ : Set ℤ} (l : List (ℕ → ℤ))
    (hl : ∀ x ∈ l, x 0 ∈ vClosure m Θ ∧ ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)
    (hball : cthickening (((l.length : ℝ) - 1) * d) (fillCells ε η Θ) ⊆ ball 0 ρ') :
    aggRun univ Θ l ⊆ cellVertices ε η (cthickening (((l.length : ℝ) - 1) * d) (fillCells ε η Θ)) := by
  have h0 : SpreadInv ε η Θ Θ d 0 := ⟨subset_rfl, fun c hc hcΘ => absurd hc hcΘ⟩
  have h := aggRun_univ_spreadInv hη hε hd hcell hdiam l Θ 0 h0 hl (by simpa using hball)
  simp only [zero_add] at h
  intro c hc
  by_cases hcΘ : c ∈ Θ
  · obtain ⟨z, hz⟩ := cell_nonempty hε η c
    exact ⟨z, hz, self_subset_cthickening _ (cell_subset_fillCells hcΘ hz)⟩
  · exact (h.2 c hc hcΘ).1

end IterativeBound

end MatedCRT
