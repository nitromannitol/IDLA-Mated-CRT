import MatedCRT.FirstPass.Derived.SuccessiveExitWindows

/-!
# Short exit times from many short successive gaps (BG20 (6.33)-(6.35), proof of Lemma 6.11)

Let `A y ⊆ ℤ` be the region attached to a vertex `y` and `σ_k = succExit A k` the successive exit times
of the walk from these regions (`σ_0 = 0`, `σ_{k+1} = σ_k + τ_{A (X_{σ_k})} ∘ θ_{σ_k}`).  Let `U ⊆ ℤ` be a
bigger region with exit time `τ_U` (in Berestycki–Gwynne: the vertices of the mated-CRT map in the
Euclidean ball `B_δ (η x)`, and `A y` the vertices in `B_{δ^ℓ} (η y)`).

* `srwLaw_shortGapEvent_le_pow` is the product bound (6.34): if from every vertex `y ∈ U` the exit time
  from `A y` is shorter than `g` with probability at most `q`, then the probability that the first `K`
  gaps are all shorter than `g` while `σ_K < τ_U` is at most `q ^ K` (strong Markov property at `σ_k`).
* `srwLaw_exit_lt_le` is the dichotomy used for (6.31): `τ_U < g` forces either `τ_U ≤ σ_K` or that
  all `K` gaps are shorter than `g`, so `P [τ_U < g] ≤ P [τ_U ≤ σ_K] + q ^ K`.
* `pow_one_sub_le_factorial_div` is the real arithmetic `(1 - p) ^ K ≤ N! / s ^ N` for `s ≤ p K`, which
  turns `q = 1 - δ ^ a` and `K ≈ δ ^ (-b)` with `b > a` into a superpolynomially small term, and
  `srwLaw_exit_lt_le_of_lower_tail` combines the two.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT

open WalkPotential

namespace SuccessiveExitGaps

/-- The successive exit times are nondecreasing in the index. -/
lemma succExit_mono (A : ℤ → Set ℤ) (x : ℕ → ℤ) {i k : ℕ} (h : i ≤ k) :
    succExit A i x ≤ succExit A k x :=
  monotone_nat_of_le_succ (fun n => succExit_le_succ A x n) h

/-- If `σ_i ≤ j` then `σ_i` is determined by the path up to time `j`. -/
lemma succExit_eq_of_pathHist_eq {A : ℤ → Set ℤ} {i j : ℕ} {x y : ℕ → ℤ}
    (h : pathHist j x = pathHist j y) (hx : succExit A i x ≤ (j : ℕ∞)) :
    succExit A i y = succExit A i x := by
  have hne : succExit A i x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top j) hx
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
  have hnj : n ≤ j := by
    rw [← hn] at hx
    exact_mod_cast hx
  have hn' : pathHist n x = pathHist n y := SuccessiveExitStop.pathHist_mono hnj h
  have hτ : S6j.IsWalkRandomTime (succExit A i) := S6j.isWalkRandomTime_nextExitSchedule (fun _ => A) i
  have h1 : succExit A i y = (n : ℕ∞) := (isWalkRandomTime_congr hτ hn').1 hn.symm
  rw [h1, hn]

/-- The event that the first `K` gaps `σ_{i+1} - σ_i` are shorter than `g` while `σ_K` is before the exit
time from `Y`. -/
def shortGapEvent (A : ℤ → Set ℤ) (Y : Set ℤ) (g K : ℕ) : Set (ℕ → ℤ) :=
  {x | succExit A K x < vExitTime Y x ∧ ∀ i < K, succExit A (i + 1) x < succExit A i x + (g : ℕ∞)}

/-- `{σ_K = j} ∩ shortGapEvent` is determined by the history up to time `j`. -/
lemma exists_pathHist_shortGapEvent (A : ℤ → Set ℤ) (Y : Set ℤ) (g K j : ℕ) :
    ∃ F : Set (Fin (j + 1) → ℤ), MeasurableSet F ∧
      shortGapEvent A Y g K ∩ {x | succExit A K x = (j : ℕ∞)} = {x | pathHist j x ∈ F} := by
  have key : ∀ x y : ℕ → ℤ, pathHist j x = pathHist j y →
      (x ∈ shortGapEvent A Y g K ∧ succExit A K x = (j : ℕ∞)) →
        (y ∈ shortGapEvent A Y g K ∧ succExit A K y = (j : ℕ∞)) := by
    rintro x y hxy ⟨⟨hlt, hgap⟩, hKj⟩
    have hσ : ∀ i ≤ K, succExit A i y = succExit A i x := fun i hi =>
      succExit_eq_of_pathHist_eq hxy ((succExit_mono A x hi).trans hKj.le)
    have hKy : succExit A K y = (j : ℕ∞) := by rw [hσ K le_rfl, hKj]
    refine ⟨⟨?_, fun i hi => ?_⟩, hKy⟩
    · rw [hKy]
      rw [hKj] at hlt
      refine natCast_lt_vExitTime_iff.2 fun k hk => ?_
      rw [← SuccessiveExitStop.pathHist_apply_of_le hxy k hk]
      exact natCast_lt_vExitTime_iff.1 hlt k hk
    · rw [hσ (i + 1) hi, hσ i hi.le]
      exact hgap i hi
  obtain ⟨F, hF, hFe⟩ := NextExitStop.exists_pathHist_of_determinacy j
    (fun x => x ∈ shortGapEvent A Y g K ∧ succExit A K x = (j : ℕ∞))
    (fun x y hxy => ⟨key x y hxy, key y x hxy.symm⟩)
  exact ⟨F, hF, hFe⟩

/-- **One more short gap**: if the exit time from `A y` is shorter than `g` with probability at most `q`
from every `y ∈ Y`, then `P [first K + 1 gaps short] ≤ q P [first K gaps short]`. -/
theorem srwLaw_shortGapEvent_succ_le (m : ℤ → ℤ → ℕ) (a : ℤ) (A : ℤ → Set ℤ) (Y : Set ℤ) (g K : ℕ)
    {q : ℝ≥0∞} (hq : ∀ y ∈ Y, srwLaw m y {z | vExitTime (A y) z < (g : ℕ∞)} ≤ q) :
    srwLaw m a (shortGapEvent A Y g (K + 1)) ≤ q * srwLaw m a (shortGapEvent A Y g K) := by
  set G : ℤ → Set (ℕ → ℤ) := fun y => {z | vExitTime (A y) z < (g : ℕ∞)} with hG
  have hGm : ∀ y, MeasurableSet (G y) := fun y =>
    (measurable_vExitTime (A y)) (Set.to_countable {t : ℕ∞ | t < (g : ℕ∞)}).measurableSet
  have h := srwLaw_test_bound_random_time m a (succExit A K) G hGm
    (S := shortGapEvent A Y g K) (fun j => exists_pathHist_shortGapEvent A Y g K j)
    (Y := Y) (c := q) hq
    (by
      intro x hx k hk
      have hx' : succExit A K x < vExitTime Y x := hx.1
      rw [hk] at hx'
      exact natCast_lt_vExitTime_iff.1 hx' k le_rfl)
  have hsub : shortGapEvent A Y g (K + 1) ⊆
      shortGapEvent A Y g K ∩ {x | ∃ k : ℕ, succExit A K x = (k : ℕ∞) ∧ WalkPotential.pathShift k x ∈ G (x k)} := by
    rintro x ⟨hlt1, hgap⟩
    have hlt : succExit A K x < vExitTime Y x :=
      lt_of_le_of_lt (succExit_le_succ A x K) hlt1
    have hne : succExit A K x ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hlt le_top)
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hne
    refine ⟨⟨hlt, fun i hi => hgap i (Nat.lt_succ_of_lt hi)⟩, j, hj.symm, ?_⟩
    have hnext : succExit A (K + 1) x =
        (j : ℕ∞) + vExitTime (A (x j)) (WalkPotential.pathShift j x) :=
      S6j.nextExit_of_eq_coe A (succExit A K) hj.symm
    have h1 := hgap K (Nat.lt_succ_self K)
    rw [hnext, ← hj] at h1
    show vExitTime (A (x j)) (WalkPotential.pathShift j x) < (g : ℕ∞)
    generalize vExitTime (A (x j)) (WalkPotential.pathShift j x) = t at h1 ⊢
    induction t using ENat.recTopCoe with
    | top => simp at h1
    | coe t =>
      have h2 : j + t < j + g := by exact_mod_cast h1
      exact_mod_cast Nat.lt_of_add_lt_add_left h2
  refine (measure_mono hsub).trans (h.trans ?_)
  gcongr
  exact Set.inter_subset_left

/-- **Product bound** (BG20 (6.34)): `P [first K gaps short] ≤ q ^ K`. -/
theorem srwLaw_shortGapEvent_le_pow (m : ℤ → ℤ → ℕ) (a : ℤ) (A : ℤ → Set ℤ) (Y : Set ℤ) (g : ℕ)
    {q : ℝ≥0∞} (hq : ∀ y ∈ Y, srwLaw m y {z | vExitTime (A y) z < (g : ℕ∞)} ≤ q) (K : ℕ) :
    srwLaw m a (shortGapEvent A Y g K) ≤ q ^ K := by
  induction K with
  | zero => simpa using prob_le_one
  | succ K ih =>
    refine (srwLaw_shortGapEvent_succ_le m a A Y g K hq).trans ?_
    rw [pow_succ']
    gcongr

/-- **Dichotomy for the exit time from `U`** (BG20 (6.31) from (6.32) and (6.34)): the exit time from `U`
is shorter than `g` with probability at most `P [τ_U ≤ σ_K] + q ^ K`. -/
theorem srwLaw_exit_lt_le (m : ℤ → ℤ → ℕ) (a : ℤ) (A : ℤ → Set ℤ) (U : Set ℤ) (g K : ℕ)
    {q : ℝ≥0∞} (hq : ∀ y ∈ U, srwLaw m y {z | vExitTime (A y) z < (g : ℕ∞)} ≤ q) :
    srwLaw m a {x | vExitTime U x < (g : ℕ∞)} ≤
      srwLaw m a {x | vExitTime U x ≤ succExit A K x} + q ^ K := by
  have hsub : {x | vExitTime U x < (g : ℕ∞)} ⊆
      {x | vExitTime U x ≤ succExit A K x} ∪ shortGapEvent A U g K := by
    intro x hx
    by_cases h : vExitTime U x ≤ succExit A K x
    · exact Or.inl h
    · refine Or.inr ⟨not_le.1 h, fun i hi => ?_⟩
      have h1 : succExit A (i + 1) x ≤ succExit A K x := succExit_mono A x hi
      have h2 : succExit A K x < (g : ℕ∞) := lt_trans (not_le.1 h) hx
      exact lt_of_lt_of_le (lt_of_le_of_lt h1 h2) le_add_self
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  exact add_le_add le_rfl (srwLaw_shortGapEvent_le_pow m a A U g hq K)

/-- Real arithmetic: `(1 - p) ^ K ≤ N! / s ^ N` whenever `0 < s ≤ p K` and `p ≤ 1`. -/
lemma pow_one_sub_le_factorial_div {p s : ℝ} (hp1 : p ≤ 1) (K N : ℕ) (hs : 0 < s)
    (hsK : s ≤ p * K) : (1 - p) ^ K ≤ (N.factorial : ℝ) / s ^ N := by
  have h1 : 1 - p ≤ Real.exp (-p) := by
    have := Real.add_one_le_exp (-p)
    linarith
  have h2 : (1 - p) ^ K ≤ Real.exp (-p) ^ K := pow_le_pow_left₀ (by linarith) h1 K
  have h3 : Real.exp (-p) ^ K = Real.exp (-(p * K)) := by
    have : (K : ℝ) * (-p) = -(p * K) := by ring
    rw [← Real.exp_nat_mul, this]
  have h4 : Real.exp (-(p * K)) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith)
  have h5 : Real.exp (-s) ≤ (N.factorial : ℝ) / s ^ N := by
    have h6 := Real.pow_div_factorial_le_exp s hs.le N
    have hpos : 0 < s ^ N := pow_pos hs N
    have hf : (0 : ℝ) < N.factorial := Nat.cast_pos.2 (Nat.factorial_pos N)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos s) (by positivity), inv_div]
    exact h6
  exact (h2.trans (h3.le.trans h4)).trans h5

/-- **BG20 (6.31) from (6.32) and Lemma 6.7, quenched**: if from every `y ∈ U` the exit time from `A y` is
at least `g` with probability at least `p`, then, for `0 < s ≤ p K`, the exit time from `U` is shorter
than `g` with probability at most `P [τ_U ≤ σ_K] + N! / s ^ N`. -/
theorem srwLaw_exit_lt_le_of_lower_tail (m : ℤ → ℤ → ℕ) (a : ℤ) (A : ℤ → Set ℤ) (U : Set ℤ)
    (g K N : ℕ) {p s : ℝ} (hp1 : p ≤ 1) (hs : 0 < s) (hsK : s ≤ p * K)
    (hq : ∀ y ∈ U, srwLaw m y {z | vExitTime (A y) z < (g : ℕ∞)} ≤ ENNReal.ofReal (1 - p)) :
    srwLaw m a {x | vExitTime U x < (g : ℕ∞)} ≤
      srwLaw m a {x | vExitTime U x ≤ succExit A K x} +
        ENNReal.ofReal ((N.factorial : ℝ) / s ^ N) := by
  refine (srwLaw_exit_lt_le m a A U g K hq).trans (add_le_add le_rfl ?_)
  rw [← ENNReal.ofReal_pow (by linarith)]
  exact ENNReal.ofReal_le_ofReal (pow_one_sub_le_factorial_div hp1 K N hs hsK)

#print axioms MatedCRT.SuccessiveExitGaps.srwLaw_shortGapEvent_le_pow
#print axioms MatedCRT.SuccessiveExitGaps.srwLaw_exit_lt_le
#print axioms MatedCRT.SuccessiveExitGaps.srwLaw_exit_lt_le_of_lower_tail

end SuccessiveExitGaps

end MatedCRT
