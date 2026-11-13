import MatedCRT.FirstPass.Derived.ExitTimeShortGaps

/-!
# No short travel before the exit time: the Markov and union-bound step of BG20 Proposition 6.5

Let `A y ⊆ ℤ` be the region attached to a vertex `y` and let `σ_k` be the successive exit times from the
regions `A (X_{σ_{k-1}})` (`succExit`).  The proof of Berestycki–Gwynne, Proposition 6.5, combines

* `(6.36)`: `P [τ_Y ≤ σ_K] ≥ 1 - ψ₀` (the walk leaves `Y` within `K = ⌊δ⁻³⌋` successive exits),
* Lemma 6.11: from every `y ∈ Y` the exit time from `A y` is shorter than `g` with probability at most `q`,

by the strong Markov property at `σ_k` and a union bound over `k < K`.  On the complement of the
bad event, no gap `σ_{k+1} - σ_k` with `σ_k < τ_Y` is shorter than `g`, and then (deterministically) any
two times `s < t ≤ τ_Y` with `t < s + g` are linked by at most one crossing of a region:
`X_s ∈ A (X_p)` for a time `p ≤ s`, and either `X_t ∈ A (X_p)` or the walk leaves `A (X_p)` at a time
`q ∈ (s, t]` (so `X_{q-1} ∈ A (X_p)`, `X_q ∉ A (X_p)`) and `X_t ∈ A (X_q)` (or `t = q`).

* `shortGapAt`, `srwLaw_shortGapAt_le`: one short gap has probability at most `q` (strong Markov),
* `srwLaw_exists_shortGapAt_le`: union bound `K q`,
* `exists_stay_or_cross`: the deterministic consequence of the absence of short gaps,
* `srwLaw_not_noShortTravel_le`: `P [¬ NoShortTravel] ≤ ψ₀ + K q`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT

namespace SuccessiveExitGaps

/-- The `k`-th gap of the successive exits is shorter than `g` while `σ_k` is before the exit time from
`Y`. -/
def shortGapAt (A : ℤ → Set ℤ) (Y : Set ℤ) (g k : ℕ) : Set (ℕ → ℤ) :=
  {x | succExit A k x < vExitTime Y x ∧ succExit A (k + 1) x < succExit A k x + (g : ℕ∞)}

/-- **One short gap** (strong Markov at `σ_k`): if from every `y ∈ Y` the exit time from `A y` is shorter
than `g` with probability at most `q`, the `k`-th gap is short, while `σ_k < τ_Y`, with probability at
most `q`. -/
theorem srwLaw_shortGapAt_le (m : ℤ → ℤ → ℕ) (a : ℤ) (A : ℤ → Set ℤ) (Y : Set ℤ) (g k : ℕ)
    {q : ℝ≥0∞} (hq : ∀ y ∈ Y, srwLaw m y {z | vExitTime (A y) z < (g : ℕ∞)} ≤ q) :
    srwLaw m a (shortGapAt A Y g k) ≤ q := by
  set G : ℤ → Set (ℕ → ℤ) := fun y => {z | vExitTime (A y) z < (g : ℕ∞)} with hG
  have hGm : ∀ y, MeasurableSet (G y) := fun y =>
    (measurable_vExitTime (A y)) (Set.to_countable {t : ℕ∞ | t < (g : ℕ∞)}).measurableSet
  have h := srwLaw_test_bound_random_time m a (succExit A k) G hGm
    (S := {x | succExit A k x < vExitTime Y x}) (fun j => exists_pathHist_gapStart A Y k j)
    (Y := Y) (c := q) hq
    (by
      intro x hx j hj
      have hx' : succExit A k x < vExitTime Y x := hx
      rw [hj] at hx'
      exact natCast_lt_vExitTime_iff.1 hx' j le_rfl)
  refine le_trans (measure_mono ?_) (h.trans ?_)
  · rintro x ⟨hlt, hgap⟩
    have hne : succExit A k x ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hlt le_top)
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hne
    refine ⟨hlt, j, hj.symm, ?_⟩
    have hnext : succExit A (k + 1) x =
        (j : ℕ∞) + vExitTime (A (x j)) (WalkPotential.pathShift j x) :=
      S6j.nextExit_of_eq_coe A (succExit A k) hj.symm
    rw [hnext, ← hj] at hgap
    show vExitTime (A (x j)) (WalkPotential.pathShift j x) < (g : ℕ∞)
    generalize vExitTime (A (x j)) (WalkPotential.pathShift j x) = t at hgap ⊢
    induction t using ENat.recTopCoe with
    | top => simp at hgap
    | coe t =>
      have h2 : j + t < j + g := by exact_mod_cast hgap
      exact_mod_cast Nat.lt_of_add_lt_add_left h2
  · calc q * srwLaw m a ({x | succExit A k x < vExitTime Y x} ∩
          {x | ∃ j : ℕ, succExit A k x = (j : ℕ∞)})
        ≤ q * 1 := mul_le_mul_of_nonneg_left prob_le_one (by simp)
      _ = q := mul_one _

/-- **Union bound over the first `K` gaps**: the probability that some gap `σ_{k+1} - σ_k`, `k < K`, is
shorter than `g` while `σ_k < τ_Y` is at most `K q`. -/
theorem srwLaw_exists_shortGapAt_le (m : ℤ → ℤ → ℕ) (a : ℤ) (A : ℤ → Set ℤ) (Y : Set ℤ) (g K : ℕ)
    {q : ℝ≥0∞} (hq : ∀ y ∈ Y, srwLaw m y {z | vExitTime (A y) z < (g : ℕ∞)} ≤ q) :
    srwLaw m a {x | ∃ k < K, x ∈ shortGapAt A Y g k} ≤ (K : ℝ≥0∞) * q := by
  have hU : {x | ∃ k < K, x ∈ shortGapAt A Y g k} = ⋃ k ∈ Finset.range K, shortGapAt A Y g k := by
    ext x
    simp
  calc srwLaw m a {x | ∃ k < K, x ∈ shortGapAt A Y g k}
      ≤ ∑ k ∈ Finset.range K, srwLaw m a (shortGapAt A Y g k) := by
        rw [hU]
        exact measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range K, q :=
        Finset.sum_le_sum fun k _ => srwLaw_shortGapAt_le m a A Y g k hq
    _ = (K : ℝ≥0∞) * q := by simp

/-- Between two successive exits the walk stays in the region of the last exit position. -/
lemma mem_of_lt_succExit (A : ℤ → Set ℤ) (x : ℕ → ℤ) {k i u : ℕ} (hk : succExit A k x = (i : ℕ∞))
    (hiu : i ≤ u) (hu : (u : ℕ∞) < succExit A (k + 1) x) : x u ∈ A (x i) := by
  have hnext : succExit A (k + 1) x =
      (i : ℕ∞) + vExitTime (A (x i)) (WalkPotential.pathShift i x) :=
    S6j.nextExit_of_eq_coe A (succExit A k) hk
  rw [hnext] at hu
  have hv : ((u - i : ℕ) : ℕ∞) < vExitTime (A (x i)) (WalkPotential.pathShift i x) := by
    generalize vExitTime (A (x i)) (WalkPotential.pathShift i x) = t at hu ⊢
    induction t using ENat.recTopCoe with
    | top => exact ENat.natCast_lt_top _
    | coe t =>
      have h2 : u < i + t := by exact_mod_cast hu
      have h3 : u - i < t := by omega
      exact_mod_cast h3
  have h := natCast_lt_vExitTime_iff.1 hv (u - i) le_rfl
  have hx : WalkPotential.pathShift i x (u - i) = x u := by
    simp only [WalkPotential.pathShift]
    congr 1
    omega
  rwa [hx] at h

/-- **Deterministic consequence of the absence of short gaps** (BG20 (6.37) ⟹ (6.7)).  If `τ_Y ≤ σ_K`
and none of the first `K` gaps `σ_{k+1} - σ_k` with `σ_k < τ_Y` is shorter than `g`, then two times
`s < t ≤ τ_Y` with `t < s + g` are linked by at most one crossing of a region: there is `p ≤ s` with
`X_s ∈ A (X_p)`, and either `X_t ∈ A (X_p)` or there is a time `q ∈ (s, t]` at which the walk leaves
`A (X_p)` (`X_{q-1} ∈ A (X_p)`, `X_q ∉ A (X_p)`) and `t = q` or `X_t ∈ A (X_q)`. -/
theorem exists_stay_or_cross (A : ℤ → Set ℤ) (Y : Set ℤ) {g K : ℕ} (x : ℕ → ℤ)
    (hgap : ∀ k < K, x ∉ shortGapAt A Y g k) (hK : vExitTime Y x ≤ succExit A K x)
    {s t : ℕ} (hst : s < t) (htg : t < s + g) (ht : (t : ℕ∞) ≤ vExitTime Y x) :
    ∃ p : ℕ, p ≤ s ∧ x s ∈ A (x p) ∧
      (x t ∈ A (x p) ∨ ∃ q : ℕ, s < q ∧ q ≤ t ∧ x (q - 1) ∈ A (x p) ∧ x q ∉ A (x p) ∧
        (t = q ∨ x t ∈ A (x q))) := by
  have hst' : (s : ℕ∞) < (t : ℕ∞) := by exact_mod_cast hst
  have hsK : (s : ℕ∞) < succExit A K x := lt_of_lt_of_le (lt_of_lt_of_le hst' ht) hK
  have hP : ∃ n, (s : ℕ∞) < succExit A n x := ⟨K, hsK⟩
  have hn0 : Nat.find hP ≠ 0 := by
    intro h0
    have h := Nat.find_spec hP
    rw [h0] at h
    have h00 : succExit A 0 x = 0 := rfl
    rw [h00] at h
    exact absurd h (by simp)
  obtain ⟨k, hk1⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hlt : (s : ℕ∞) < succExit A (k + 1) x := by
    have h := Nat.find_spec hP
    rwa [hk1] at h
  have hle : succExit A k x ≤ (s : ℕ∞) := by
    by_contra hcon
    have h := Nat.find_min' hP (not_le.1 hcon)
    omega
  have hkK : k + 1 ≤ K := by
    have h := Nat.find_min' hP hsK
    omega
  obtain ⟨i, hi⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top s) hle)
  have hσk : succExit A k x = (i : ℕ∞) := hi.symm
  have his : i ≤ s := by
    rw [hσk] at hle
    exact_mod_cast hle
  have hxs : x s ∈ A (x i) := mem_of_lt_succExit A x hσk his hlt
  refine ⟨i, his, hxs, ?_⟩
  by_cases hts : (t : ℕ∞) < succExit A (k + 1) x
  · exact Or.inl (mem_of_lt_succExit A x hσk (by omega) hts)
  · right
    have hts' : succExit A (k + 1) x ≤ (t : ℕ∞) := not_lt.1 hts
    obtain ⟨q, hq⟩ := ENat.ne_top_iff_exists.1
      (ne_top_of_le_ne_top (ENat.natCast_ne_top t) hts')
    have hσq : succExit A (k + 1) x = (q : ℕ∞) := hq.symm
    have hqt : q ≤ t := by
      rw [hσq] at hts'
      exact_mod_cast hts'
    have hsq : s < q := by
      rw [hσq] at hlt
      exact_mod_cast hlt
    obtain ⟨i₁, -, hσk', hnot⟩ := exists_notMem_of_succExit A x k q hσq
    have hii : i = i₁ := by
      rw [hσk] at hσk'
      exact_mod_cast hσk'
    subst hii
    have hxq1 : x (q - 1) ∈ A (x i) := by
      refine mem_of_lt_succExit A x hσk (by omega) ?_
      rw [hσq]
      exact_mod_cast (by omega : q - 1 < q)
    refine ⟨q, hsq, hqt, hxq1, hnot, ?_⟩
    by_cases htq : t = q
    · exact Or.inl htq
    · right
      have hqt' : q < t := by omega
      have hkK' : k + 1 < K := by
        rcases Nat.lt_or_eq_of_le hkK with h | h
        · exact h
        · exfalso
          rw [← h, hσq] at hK
          have h1 : (t : ℕ∞) ≤ (q : ℕ∞) := ht.trans hK
          have h2 : t ≤ q := by exact_mod_cast h1
          omega
      have hgk := hgap (k + 1) hkK'
      have hlt1 : succExit A (k + 1) x < vExitTime Y x := by
        rw [hσq]
        exact lt_of_lt_of_le (by exact_mod_cast hqt') ht
      have hge : ¬ succExit A (k + 1 + 1) x < succExit A (k + 1) x + (g : ℕ∞) := by
        intro hh
        exact hgk ⟨hlt1, hh⟩
      have hge' : succExit A (k + 1) x + (g : ℕ∞) ≤ succExit A (k + 1 + 1) x := not_lt.1 hge
      rw [hσq] at hge'
      have htlt : (t : ℕ∞) < succExit A (k + 1 + 1) x :=
        lt_of_lt_of_le (by exact_mod_cast (by omega : t < q + g)) hge'
      exact mem_of_lt_succExit A x hσq hqt htlt

/-- The path `x` makes no short travel before `τ_Y` with respect to the regions `A`: any two times
`s < t ≤ τ_Y` with `t < s + g` are linked by at most one crossing of a region (see
`exists_stay_or_cross`). -/
def NoShortTravel (A : ℤ → Set ℤ) (Y : Set ℤ) (g : ℕ) (x : ℕ → ℤ) : Prop :=
  ∀ s t : ℕ, s < t → t < s + g → (t : ℕ∞) ≤ vExitTime Y x →
    ∃ p : ℕ, p ≤ s ∧ x s ∈ A (x p) ∧
      (x t ∈ A (x p) ∨ ∃ q : ℕ, s < q ∧ q ≤ t ∧ x (q - 1) ∈ A (x p) ∧ x q ∉ A (x p) ∧
        (t = q ∨ x t ∈ A (x q)))

/-- **Markov property and union bound of BG20 Proposition 6.5.**  If `P_a [τ_Y ≤ σ_K] ≥ 1 - ψ₀` (the
bound (6.36)) and from every `y ∈ Y` the exit time from `A y` is shorter than `g` with probability at
most `q` (Lemma 6.11), then the walk started at `a` makes a short travel with probability at most
`ψ₀ + K q`. -/
theorem srwLaw_not_noShortTravel_le (m : ℤ → ℤ → ℕ) (a : ℤ) (A : ℤ → Set ℤ) (Y : Set ℤ) (g K : ℕ)
    {ψ₀ q : ℝ≥0∞} (h0 : srwLaw m a {x | ¬ vExitTime Y x ≤ succExit A K x} ≤ ψ₀)
    (hq : ∀ y ∈ Y, srwLaw m y {z | vExitTime (A y) z < (g : ℕ∞)} ≤ q) :
    srwLaw m a {x | ¬ NoShortTravel A Y g x} ≤ ψ₀ + (K : ℝ≥0∞) * q := by
  have hsub : {x | ¬ NoShortTravel A Y g x} ⊆
      {x | ¬ vExitTime Y x ≤ succExit A K x} ∪ {x | ∃ k < K, x ∈ shortGapAt A Y g k} := by
    intro x hx
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_exists, not_and] at hcon
    obtain ⟨hK, hgap⟩ := hcon
    exact hx fun s t hst htg ht =>
      exists_stay_or_cross A Y x (fun k hk hmem => hgap k hk hmem) hK hst htg ht
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add h0 (srwLaw_exists_shortGapAt_le m a A Y g K hq)))

end SuccessiveExitGaps

end MatedCRT
