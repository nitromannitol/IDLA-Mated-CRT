import MatedCRT.Proofs.Sec6.IterativeBound.Spread

/-!
# Lemma 6.10: the iteration for one environment (lines 2715-2815)

`core_induction`: strong induction on the number `n` of walkers. With radius budget `Ψ` and failure budget `G`:
* `n ≤ N` (Step 3): the walkers are absorbed in `V^ε(B⁺_{(n-1)d}(Θ̄))` almost surely;
* `n > N` (Steps 1-2): one round with radius `r_n`, stopping in `V^ε(Θ̄ + B_{r_n})`. Lemma 6.9 (`habs`) bounds the
  probability that at most `p_n n` walkers are absorbed by `e`; otherwise fewer than `(1 - p_n) n` walkers are
  stopped, in `cl(Θ¹)`, the cluster `Θ¹` fills at most `B⁺_{r_n + d}(Θ̄)`, and the Abelian property restarts them.
The budgets satisfy `Ψ(n₁) + r_n + d ≤ Ψ(n)` and `G(n₁) + e ≤ G(n)` for `n₁ < (1 - p_n) n`.
-/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

namespace IterativeBound

open Absorption

theorem fillCells_mono {ε : ℝ} {η : ℝ → ℂ} {Θ Θ' : Set ℤ} (h : Θ ⊆ Θ') : fillCells ε η Θ ⊆ fillCells ε η Θ' :=
  biUnion_subset_biUnion_left h

theorem cellVertices_mono' {ε : ℝ} {η : ℝ → ℂ} {D D' : Set ℂ} (h : D ⊆ D') :
    cellVertices ε η D ⊆ cellVertices ε η D' :=
  fun _ ⟨z, hz1, hz2⟩ => ⟨z, hz1, h hz2⟩

/-- **The iteration for one environment.** -/
theorem core_induction {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ' s₀ d N e : ℝ} (hab : IsAbelianIDLA m)
    (hsrw : IsSrwPathLaw m) (hη : Continuous η) (hε : 0 ≤ ε) (hd : 0 ≤ d) (hN : 0 ≤ N) (he : 0 ≤ e)
    (hcell : ∀ a b : ℤ, a ∈ cellVertices ε η (ball 0 ρ') → m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hdiam : ∀ a ∈ cellVertices ε η (ball 0 ρ'), diam (cell ε η a) ≤ d)
    {Θ₀ : Set ℤ} (hs₀ : ball 0 s₀ ⊆ fillCells ε η Θ₀) {Y : Set ℂ} (hYc : closure Y ⊆ ball 0 (ρ' / 2))
    (hρ' : 0 < ρ') (J : ℕ) (rr pp Ψ G : ℕ → ℝ)
    (habs : ∀ n : ℕ, N < n → n ≤ J → ∀ Θ : Set ℤ, closure (fillCells ε η Θ) ⊆ ball 0 (ρ' / 2) →
      ball 0 s₀ ⊆ fillCells ε η Θ → ∀ a : Fin n → ℤ, (∀ i, a i ∈ vClosure m Θ) →
        walkersLaw m a {xs | ((idlaAggregate Θ (cellVertices ε η (thickening (rr n) (fillCells ε η Θ)))
          (List.ofFn xs) \ Θ).ncard : ℝ) ≤ pp n * n} ≤ ENNReal.ofReal e)
    (hrr : ∀ n, 0 < rr n) (hpp0 : ∀ n, 0 ≤ pp n) (hpp1 : ∀ n, pp n < 1) (hΨ0 : ∀ n, 0 ≤ Ψ n)
    (hG0 : ∀ n, 0 ≤ G n)
    (hΨ3 : ∀ n : ℕ, (n : ℝ) ≤ N → ((n : ℝ) - 1) * d ≤ Ψ n)
    (hΨr : ∀ n : ℕ, N < n → n ≤ J → ∀ n₁ : ℕ, (n₁ : ℝ) < (1 - pp n) * n → Ψ n₁ + rr n + d ≤ Ψ n)
    (hGr : ∀ n : ℕ, N < n → n ≤ J → ∀ n₁ : ℕ, (n₁ : ℝ) < (1 - pp n) * n → G n₁ + e ≤ G n) :
    ∀ n : ℕ, n ≤ J → ∀ Θ : Set ℤ, Θ₀ ⊆ Θ → ∀ a : Fin n → ℤ, (∀ i, a i ∈ vClosure m Θ) →
      cthickening (Ψ n) (fillCells ε η Θ) ⊆ Y →
      walkersLaw m a {xs | ¬ idlaAggregate Θ univ (List.ofFn xs) ⊆ cellVertices ε η Y} ≤
        ENNReal.ofReal (G n) := by
  have hYball : Y ⊆ ball 0 ρ' :=
    subset_closure.trans (hYc.trans (ball_subset_ball (by linarith)))
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnJ Θ hΘ₀ a ha hΨ
  have hgood := ae_walkersLaw_path hsrw ha
  by_cases hn : (n : ℝ) ≤ N
  · -- Step 3: the last walkers are absorbed next to the cluster
    have h0 : walkersLaw m a {xs | ¬ idlaAggregate Θ univ (List.ofFn xs) ⊆ cellVertices ε η Y} = 0 := by
      have hnull := ae_iff.1 hgood
      refine measure_mono_null ?_ hnull
      intro xs hxs hgx
      refine hxs ?_
      have hball : cthickening ((((List.ofFn xs).length : ℝ) - 1) * d) (fillCells ε η Θ) ⊆ ball 0 ρ' := by
        rw [List.length_ofFn]
        exact (cthickening_mono (hΨ3 n hn) _).trans (hΨ.trans hYball)
      refine (aggRun_univ_subset_cellVertices hη hε hd hcell hdiam (List.ofFn xs) hgx hball).trans ?_
      rw [List.length_ofFn]
      exact cellVertices_mono' ((cthickening_mono (hΨ3 n hn) _).trans hΨ)
    rw [h0]
    exact zero_le
  · -- Steps 1-2: one round, then the Abelian property
    push Not at hn
    set r := rr n with hr_def
    set X := fillCells ε η Θ with hX
    set Θ' := cellVertices ε η (thickening r X) with hΘ'
    have hr : 0 < r := hrr n
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt hN hn
    have hpos : ((0 : ℕ) : ℝ) < (1 - pp n) * n := by
      have := hpp1 n
      push_cast
      nlinarith
    have hrΨ : r ≤ Ψ n := by
      have := hΨr n hn hnJ 0 hpos
      linarith [hΨ0 0]
    have hGe : e ≤ G n := by
      have := hGr n hn hnJ 0 hpos
      linarith [hG0 0]
    have hΘΘ' : Θ ⊆ Θ' := fun c hc => by
      obtain ⟨z, hz⟩ := cell_nonempty hε η c
      exact ⟨z, hz, self_subset_thickening hr _ (cell_subset_fillCells hc hz)⟩
    have hXY : X ⊆ Y := (self_subset_cthickening _).trans hΨ
    have hthick : thickening r X ⊆ ball 0 ρ' :=
      (thickening_subset_cthickening r X).trans ((cthickening_mono hrΨ _).trans (hΨ.trans hYball))
    have hadm1 : closure X ⊆ ball 0 (ρ' / 2) := (closure_mono hXY).trans hYc
    have hadm2 : ball 0 s₀ ⊆ X := hs₀.trans (fillCells_mono hΘ₀)
    have habsn := habs n hn hnJ Θ hadm1 hadm2 a ha
    set Gd : Set (Fin n → ℕ → ℤ) := {xs | (∀ x ∈ List.ofFn xs,
        x 0 ∈ vClosure m Θ ∧ ∀ k, x (k + 1) = x k ∨ m (x k) (x (k + 1)) ≠ 0) ∧
      ¬ (((idlaAggregate Θ Θ' (List.ofFn xs) \ Θ).ncard : ℝ) ≤ pp n * n)} with hGd
    have hGc : walkersLaw m a Gdᶜ ≤ ENNReal.ofReal e := by
      have hsub : Gdᶜ ⊆ {xs | ¬ ∀ x ∈ List.ofFn xs,
            x 0 ∈ vClosure m Θ ∧ ∀ k, x (k + 1) = x k ∨ m (x k) (x (k + 1)) ≠ 0} ∪
          {xs | ((idlaAggregate Θ Θ' (List.ofFn xs) \ Θ).ncard : ℝ) ≤ pp n * n} := by
        intro xs hxs
        by_cases h : ∀ x ∈ List.ofFn xs, x 0 ∈ vClosure m Θ ∧ ∀ k, x (k + 1) = x k ∨ m (x k) (x (k + 1)) ≠ 0
        · right
          by_contra h'
          exact hxs ⟨h, h'⟩
        · left
          exact h
      calc walkersLaw m a Gdᶜ ≤ _ := measure_mono hsub
        _ ≤ _ := measure_union_le _ _
        _ ≤ 0 + ENNReal.ofReal e := add_le_add (ae_iff.1 hgood).le habsn
        _ = ENNReal.ofReal e := zero_add _
    have hG : ∀ xs ∈ Gd, walkersLaw m (fun i : Fin (idlaStopped Θ Θ' (List.ofFn xs)).length =>
          (idlaStopped Θ Θ' (List.ofFn xs)).get i)
        {ys | ¬ idlaAggregate (idlaAggregate Θ Θ' (List.ofFn xs)) univ (List.ofFn ys) ⊆ cellVertices ε η Y} ≤
          ENNReal.ofReal (G n - e) := by
      rintro xs ⟨hgx, hncard⟩
      obtain ⟨f1, f2, -, f4, f5⟩ := idlaRun_facts m hΘΘ' hgx
      have hcnt : ((idlaAggregate Θ Θ' (List.ofFn xs) \ Θ).ncard : ℝ) +
          ((idlaStopped Θ Θ' (List.ofFn xs)).length : ℝ) ≤ n := by exact_mod_cast f4
      have hn₁ : ((idlaStopped Θ Θ' (List.ofFn xs)).length : ℝ) < (1 - pp n) * n := by
        push Not at hncard
        nlinarith
      have hlt : (idlaStopped Θ Θ' (List.ofFn xs)).length < n := by
        have h1 : ((idlaStopped Θ Θ' (List.ofFn xs)).length : ℝ) < n := by
          have := hpp0 n
          nlinarith
        exact_mod_cast h1
      have hfill : fillCells ε η (idlaAggregate Θ Θ' (List.ofFn xs)) ⊆ cthickening (r + d) X :=
        fillCells_subset_cthickening_of_subset hη hr.le hd hdiam hthick (f2.trans subset_union_right)
      have hΨn := hΨr n hn hnJ _ hn₁
      have hΨ₁ : cthickening (Ψ (idlaStopped Θ Θ' (List.ofFn xs)).length)
          (fillCells ε η (idlaAggregate Θ Θ' (List.ofFn xs))) ⊆ Y :=
        (cthickening_subset_of_subset _ hfill).trans
          ((cthickening_cthickening_subset (hΨ0 _) (by linarith) _).trans
            ((cthickening_mono (by linarith) _).trans hΨ))
      refine (ih _ hlt (hlt.le.trans hnJ) _ (hΘ₀.trans f1)
        (fun i : Fin (idlaStopped Θ Θ' (List.ofFn xs)).length => (idlaStopped Θ Θ' (List.ofFn xs)).get i)
        (fun i => (f5 _ (List.get_mem _ _)).2) hΨ₁).trans ?_
      exact ENNReal.ofReal_le_ofReal (by linarith [hGr n hn hnJ _ hn₁])
    refine (walkersLaw_not_subset_le_round hab hΘΘ' a (cellVertices ε η Y) Gd _ hG).trans ?_
    calc walkersLaw m a Gdᶜ + ENNReal.ofReal (G n - e) ≤ ENNReal.ofReal e + ENNReal.ofReal (G n - e) :=
          add_le_add hGc le_rfl
      _ = ENNReal.ofReal (G n) := by
          rw [← ENNReal.ofReal_add he (by linarith)]
          congr 1
          ring

end IterativeBound

end MatedCRT
