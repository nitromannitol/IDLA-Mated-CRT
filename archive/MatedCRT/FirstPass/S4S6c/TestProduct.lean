import Mathlib

/-!
# Successive tests: the product bound behind the amplification of Lemma 6.8

Abstract probability. Let `G n` be the event that the `n`-th test is passed, with `G n ∈ ℱ (n+1)` for a filtration `ℱ`.
If the conditional probability of passing test `n`, given the history `ℱ n`, is at most `c`, in set form
`μ (S ∩ G n) ≤ c * μ S` for every `S ∈ ℱ n`, then the probability that the first `N` tests are all passed is at most
`c ^ N`. With `c = 1 - q`, `q = c₀/(1+|log r|)²`, and `eventually_amplified_le_half` (FirstPass/S4S6c/AmplifiedBound.lean)
this gives the uniform `1/2` of Lemma 6.8.

Not here: that the walk's tests satisfy the conditional bound (the per-test estimate of Lemma 3, and the stopping times (27)
with their filtration). Those are the open NEW steps of Lemma 6.8 (see the round report).
-/

open MeasureTheory Set

namespace MatedCRT

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Product bound for successive tests.** If passing test `n` has conditional probability at most `c` given `ℱ n`,
then the first `N` tests are all passed with probability at most `c ^ N`. -/
theorem measure_biInter_range_le_pow (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : ℕ → MeasurableSpace Ω) (hmono : Monotone ℱ)    (G : ℕ → Set Ω) (hG : ∀ n, MeasurableSet[ℱ (n + 1)] (G n)) (c : ENNReal)
    (hcond : ∀ n, ∀ S, MeasurableSet[ℱ n] S → μ (S ∩ G n) ≤ c * μ S) (N : ℕ) :
    μ (⋂ k ∈ Finset.range N, G k) ≤ c ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hS : MeasurableSet[ℱ N] (⋂ k ∈ Finset.range N, G k) := by
      refine Finset.measurableSet_biInter _ fun k hk => ?_
      exact hmono (Nat.succ_le_of_lt (Finset.mem_range.mp hk)) _ (hG k)
    have hset : (⋂ k ∈ Finset.range (N + 1), G k) = (⋂ k ∈ Finset.range N, G k) ∩ G N := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iInter₂, Finset.mem_range]
      constructor
      · intro h
        exact ⟨fun k hk => h k (by omega), h N (by omega)⟩
      · rintro ⟨h1, h2⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
        · exact h1 k hk'
        · subst hk'
          exact h2
    rw [hset, pow_succ]
    calc μ ((⋂ k ∈ Finset.range N, G k) ∩ G N)
        ≤ c * μ (⋂ k ∈ Finset.range N, G k) := hcond N _ hS
      _ ≤ c * c ^ N := mul_le_mul_of_nonneg_left ih (by simp)
      _ = c ^ N * c := mul_comm _ _

/-- **Product bound with a real threshold.** If `(1 - q)^N ≤ b` and passing each test has conditional probability at
most `1 - q` (with `q ≤ 1`), then the first `N` tests are all passed with probability at most `b`. -/
theorem measure_biInter_range_le_ofReal (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : ℕ → MeasurableSpace Ω) (hmono : Monotone ℱ)    (G : ℕ → Set Ω) (hG : ∀ n, MeasurableSet[ℱ (n + 1)] (G n)) {q : ℝ} (hq1 : q ≤ 1)
    (hcond : ∀ n, ∀ S, MeasurableSet[ℱ n] S → μ (S ∩ G n) ≤ ENNReal.ofReal (1 - q) * μ S)
    (N : ℕ) {b : ℝ} (hb : (1 - q) ^ N ≤ b) :
    μ (⋂ k ∈ Finset.range N, G k) ≤ ENNReal.ofReal b := by
  refine (measure_biInter_range_le_pow μ ℱ hmono G hG _ hcond N).trans ?_
  rw [← ENNReal.ofReal_pow (by linarith)]
  exact ENNReal.ofReal_le_ofReal hb

end MatedCRT
