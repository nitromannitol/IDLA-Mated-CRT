import MatedCRT.FirstPass.S4S6c.RandomTimeTestBound

/-!
# Successive random tests: the product bound at random times

The random-time analogue of `TestProduct.lean`. The `N`-th test starts at the random time `τ N` and is passed when the
future event `G N (x (τ N))` occurs. Let `S N` be the event that the first `N` tests are all passed (`S 0 = univ`,
`S (N+1) = S N ∩ {test N passed}`). If, for every `N`, the stopping property holds for `S N` at `τ N`, the state at the
start of test `N` lies in `Y` on `S N`, and each test has conditional passing probability at most `c` from every state in
`Y`, then `P^a(S N) ≤ c^N`. The induction uses the one-test bound at a random time (`RandomTimeTestBound.lean`).
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace MatedCRT

open WalkPotential

/-- **The first `N` successive random tests are all passed with probability at most `c^N`**. -/
theorem srwLaw_successive_tests_le_pow (m : ℤ → ℤ → ℕ) (a : ℤ) (τ : ℕ → (ℕ → ℤ) → ℕ∞)
    (G : ℕ → ℤ → Set (ℕ → ℤ)) (hG : ∀ N y, MeasurableSet (G N y))
    {Y : Set ℤ} {c : ℝ≥0∞} (hc : ∀ N, ∀ y ∈ Y, srwLaw m y (G N y) ≤ c)
    (S : ℕ → Set (ℕ → ℤ)) (hS0 : S 0 = univ)
    (hSsucc : ∀ N, S (N + 1) = S N ∩ {x | ∃ k : ℕ, τ N x = k ∧ pathShift k x ∈ G N (x k)})
    (hstop : ∀ N k : ℕ, ∃ F : Set (Fin (k + 1) → ℤ), MeasurableSet F ∧
      S N ∩ {x | τ N x = k} = {x | pathHist k x ∈ F})
    (hSY : ∀ N, ∀ x ∈ S N, ∀ k : ℕ, τ N x = k → x k ∈ Y) (N : ℕ) :
    srwLaw m a (S N) ≤ c ^ N := by
  induction N with
  | zero =>
    rw [hS0]
    simp
  | succ N ih =>
    rw [hSsucc N]
    have h := srwLaw_test_bound_random_time m a (τ N) (G N) (hG N) (hstop N) (hc N) (hSY N)
    calc srwLaw m a (S N ∩ {x | ∃ k : ℕ, τ N x = k ∧ pathShift k x ∈ G N (x k)})
        ≤ c * srwLaw m a (S N ∩ {x | ∃ k : ℕ, τ N x = k}) := h
      _ ≤ c * srwLaw m a (S N) :=
          mul_le_mul_of_nonneg_left (measure_mono inter_subset_left) (by simp)
      _ ≤ c * c ^ N := mul_le_mul_of_nonneg_left ih (by simp)
      _ = c ^ (N + 1) := (pow_succ' c N).symm

end MatedCRT
