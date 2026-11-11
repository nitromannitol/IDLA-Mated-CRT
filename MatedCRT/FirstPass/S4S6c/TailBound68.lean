import MatedCRT.FirstPass.S4S6c.SuccessiveExitStop
import MatedCRT.FirstPass.S4S6c.AmplCutoff

/-!
# The tail bound of the printed Lemma 6.8 from the test-level inputs (D1-D2)

The argument bounds the
probability that the walk stays in `A` during every local test window `[T_j, T_{j+1})` by `(1 - q(r))^N`, with
`q(r) = q₀ / (1 + log (1/r))²` (C16) and `N = ⌊r / (100 s)⌋ ≥ r^(-ζ) / 200` (D1), `ζ = p/2 - 1 ∈ (0, 1/2)`.
This file proves the arithmetic and the event inclusion around that chain. The NEW inputs are *named hypotheses*:

* `hc` : the one-test bound `P_y(stay in A during the test window) ≤ 1 - q(r)` for every state `y ∈ Y` (C15-C16,
  strong Markov at `S_j` and eq. (15) of Lemma 3);
* `hSY` : the state at the start of each test lies in `Y` on the event that the earlier tests are passed (C3);
* `hwin` : on the good trajectories, every test window `[T_j, T_{j+1})` with `j < N` is contained in the time before
  the exit of `U` (C12, C11).

Under these, `printed68_tail_bound` gives `P(walk stays in A until exit of U) ≤ 1/2` (the printed Lemma 6.8 with `s₂ = 1/2`).
-/

open MeasureTheory Set Function Real
open scoped ENNReal
open MatedCRT.SuccessiveExitStop MatedCRT.AmplCutoff

namespace MatedCRT

open WalkPotential

namespace TailBound68

/-- `x / 2 ≤ ⌊x⌋` for `x ≥ 2` (`⌊x⌋ ≥ x/2`). -/
theorem floor_half_le {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one x
  linarith

/-- The number of tests `N = ⌊r / (100 s)⌋` is at least `r^(-ζ) / 200` with `ζ = p/2 - 1`, when `s ≤ r^(p/2)` and
`r^(-ζ) ≥ 200`. -/
theorem count_ge_of_scale {r s p : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r ^ (p / 2))
    (hbig : 200 ≤ r ^ (-(p / 2 - 1))) :
    r ^ (-(p / 2 - 1)) / 200 ≤ (⌊r / (100 * s)⌋₊ : ℝ) := by
  have hpow : r ^ (-(p / 2 - 1)) = r / r ^ (p / 2) := by
    rw [show -(p / 2 - 1) = 1 - p / 2 by ring, Real.rpow_sub hr, Real.rpow_one]
  have hx1 : r ^ (-(p / 2 - 1)) / 100 ≤ r / (100 * s) := by
    rw [hpow, div_div]
    exact div_le_div_of_nonneg_left hr.le (by linarith) (by linarith)
  have hx2 : 2 ≤ r / (100 * s) := by linarith
  have h := floor_half_le hx2
  linarith

/-- `(1 - q)^N ≤ exp (-(q N))` for `0 ≤ q ≤ 1`. -/
theorem one_sub_pow_le_exp_neg {q : ℝ} (hq1 : q ≤ 1) (N : ℕ) :
    (1 - q) ^ N ≤ Real.exp (-(q * N)) := by
  have h0 : 0 ≤ 1 - q := by linarith
  have h1 : 1 - q ≤ Real.exp (-q) := by
    linarith [Real.add_one_le_exp (-q)]
  calc (1 - q) ^ N ≤ (Real.exp (-q)) ^ N := pow_le_pow_left₀ h0 h1 N
    _ = Real.exp (-(q * N)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The `N`-test tail with per-test probability `q₀ / (1 + log (1/r))²` is at most the cutoff exponential
`exp (-((q₀/200) r^(-ζ) / (1 + log (1/r))²))` when `N ≥ r^(-ζ)/200`. -/
theorem exp_tail_le_cutoff {q0 ζ r : ℝ} (hq0 : 0 < q0) (hr : 0 < r) (hr1 : r ≤ 1) (N : ℕ)
    (hN : r ^ (-ζ) / 200 ≤ N) :
    Real.exp (-(q0 / (1 + Real.log (1 / r)) ^ 2 * N)) ≤
      Real.exp (-(q0 / 200 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2)) := by
  apply Real.exp_le_exp.2
  have hL : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have hP : 0 ≤ (1 + Real.log (1 / r)) ^ 2 := sq_nonneg _
  have hqN : 0 ≤ q0 / (1 + Real.log (1 / r)) ^ 2 := div_nonneg hq0.le hP
  have key : q0 / 200 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2 ≤
      q0 / (1 + Real.log (1 / r)) ^ 2 * N := by
    calc q0 / 200 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2
        = q0 / (1 + Real.log (1 / r)) ^ 2 * (r ^ (-ζ) / 200) := by ring
      _ ≤ q0 / (1 + Real.log (1 / r)) ^ 2 * N := mul_le_mul_of_nonneg_left hN hqN
  linarith

/-- **The tail bound of the printed Lemma 6.8** (D1-D2): the walk started at `a` stays in `A` until
it exits `U` with probability at most `1/2`, given the named test-level inputs `hc`, `hSY`, `hwin`, and the good event
`Good` of quenched probability one. -/
theorem printed68_tail_bound (m : ℤ → ℤ → ℕ) (a : ℤ) (W : ℤ → Set ℤ) (A U : Set ℤ)
    (τ : ℕ → (ℕ → ℤ) → ℕ∞) (S : ℕ → Set (ℕ → ℤ))
    (hτ0 : ∀ x, τ 0 x = 0)
    (hτsucc : ∀ N x (i : ℕ), τ N x = (i : ℕ∞) →
      τ (N + 1) x = (i : ℕ∞) + vExitTime (W (x i)) (pathShift i x))
    (hτtop : ∀ N x, τ N x = ⊤ → τ (N + 1) x = ⊤)
    (hS0 : S 0 = univ)
    (hSsucc : ∀ N, S (N + 1) = S N ∩ {x | ∃ k : ℕ, τ N x = k ∧ pathShift k x ∈ stayInRegion W A (x k)})
    {Y : Set ℤ} {q0 ζ r : ℝ} (hq0 : 0 < q0) (hq0' : q0 ≤ 1) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hrA : r ≤ (q0 / 200 * ζ ^ 2 / (16 * Real.log 2)) ^ (2 / ζ))
    (hc : ∀ y ∈ Y, srwLaw m y (stayInRegion W A y) ≤
      ENNReal.ofReal (1 - q0 / (1 + Real.log (1 / r)) ^ 2))
    (hSY : ∀ N, ∀ x ∈ S N, ∀ k : ℕ, τ N x = k → x k ∈ Y)
    (N : ℕ) (hN : r ^ (-ζ) / 200 ≤ N)
    (Good : Set (ℕ → ℤ)) (hGood : srwLaw m a Goodᶜ = 0)
    (hwin : ∀ x ∈ Good, ∀ j < N, ∃ k : ℕ, τ j x = k ∧
      ∀ n : ℕ, (n : ℕ∞) < vExitTime (W (x k)) (pathShift k x) → ((k + n : ℕ) : ℕ∞) < vExitTime U x) :
    srwLaw m a {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A} ≤ ENNReal.ofReal (1 / 2) := by
  have hL : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have hP : 1 ≤ (1 + Real.log (1 / r)) ^ 2 := by nlinarith
  have hq : 0 ≤ q0 / (1 + Real.log (1 / r)) ^ 2 := div_nonneg hq0.le (sq_nonneg _)
  have hq1 : q0 / (1 + Real.log (1 / r)) ^ 2 ≤ 1 :=
    le_trans (div_le_self hq0.le hP) hq0'
  have h0q : (0 : ℝ) ≤ 1 - q0 / (1 + Real.log (1 / r)) ^ 2 := by linarith
  -- the walk stays in `A` until the exit of `U` only if every test window stays in `A`
  have hstay : ∀ j ≤ N, ∀ x ∈ Good, (∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A) → x ∈ S j := by
    intro j
    induction j with
    | zero =>
      intro _ x _ _
      rw [hS0]
      exact mem_univ x
    | succ j ih =>
      intro hj x hx hstay
      have hxS : x ∈ S j := ih (by omega) x hx hstay
      obtain ⟨k, hk, hwk⟩ := hwin x hx j (by omega)
      rw [hSsucc j]
      refine ⟨hxS, k, hk, ?_⟩
      intro n hn
      exact hstay (k + n) (hwk n hn)
  have hsub : {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A} ⊆ Goodᶜ ∪ S N := by
    intro x hx
    by_cases hg : x ∈ Good
    · exact Or.inr (hstay N le_rfl x hg hx)
    · exact Or.inl hg
  have hSN := srwLaw_successive_exit_le_pow m a W A τ S hτ0 hτsucc hτtop hS0 hSsucc hc hSY N
  have hpow : ENNReal.ofReal (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N ≤
      ENNReal.ofReal (Real.exp (-(q0 / (1 + Real.log (1 / r)) ^ 2 * N))) := by
    rw [← ENNReal.ofReal_pow h0q]
    exact ENNReal.ofReal_le_ofReal (one_sub_pow_le_exp_neg hq1 N)
  have hcut := exp_tail_le_cutoff hq0 hr hr1 N hN
  have hhalf := amplification_cutoff (c := q0 / 200) (by linarith) hζ hζ' hr hr1 hrA
  have hfin : ENNReal.ofReal (Real.exp (-(q0 / (1 + Real.log (1 / r)) ^ 2 * N))) ≤ ENNReal.ofReal (1 / 2) :=
    ENNReal.ofReal_le_ofReal (le_trans hcut hhalf)
  calc srwLaw m a {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A}
      ≤ srwLaw m a (Goodᶜ ∪ S N) := measure_mono hsub
    _ ≤ srwLaw m a Goodᶜ + srwLaw m a (S N) := measure_union_le _ _
    _ = srwLaw m a (S N) := by rw [hGood, zero_add]
    _ ≤ ENNReal.ofReal (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N := hSN
    _ ≤ ENNReal.ofReal (Real.exp (-(q0 / (1 + Real.log (1 / r)) ^ 2 * N))) := hpow
    _ ≤ ENNReal.ofReal (1 / 2) := hfin

#print axioms MatedCRT.TailBound68.printed68_tail_bound

end TailBound68

end MatedCRT
