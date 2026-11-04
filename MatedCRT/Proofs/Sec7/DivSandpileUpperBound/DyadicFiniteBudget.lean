import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicStoppedBlocks
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicHorizon

/-! Radius and time budgets up to a finite shell horizon. -/

namespace MatedCRT.Sec7

/-- Finite-horizon contraction bounds the delayed shell-radius sum through
each dyadic crossing time. No contraction or radius estimate is assumed at
or beyond the horizon. -/
theorem finite_dyadic_delayed_radius_budget
    (O r u : ℕ → ℝ) (S K α F s a q : ℝ) (n N : ℕ)
    (hS : 0 < S) (hK : 0 ≤ K) (hα : 0 < α) (hF : 0 ≤ F)
    (hs : 0 < s) (hs1 : s ≤ 1) (ha : 0 < a) (hq : 0 < q)
    (h0 : O 0 ≤ S)
    (hu : ∀ j k, k < n → S * (1 / 2 : ℝ) ^ (j + 1) < O k →
      a * q ^ j ≤ u k ∧ u k ≤ 1)
    (hstep : ∀ j k, k < n → S * (1 / 2 : ℝ) ^ (j + 1) < O k →
      O (k + 1) ≤ (1 - s / (1 + |Real.log (u k)|) ^ 2) * O k)
    (hr : ∀ k < n, r (k + 1) ≤ max ((O k * K) ^ α) F) :
    let P : ℕ → ℝ := fun k => if k < n then O k else 0
    let times := levelCrossingTimes P (fun j => S * (1 / 2 : ℝ) ^ j)
    let Q : ℝ := (1 / 2 : ℝ) ^ α
    let C : ℝ := 2 / s + 2
    let A : ℝ := 1 + |Real.log a|
    let B : ℝ := |Real.log q|
    times N ≤ n ∧ (O (times N) ≤ S * (1 / 2 : ℝ) ^ N ∨ times N = n) ∧
      (∑ k ∈ Finset.range (times N), r (k + 1)) ≤
        (S * K) ^ α * C * ((A + B) ^ 2 *
          ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * Q ^ j) + F * (times N : ℝ) ∧
      (times N : ℝ) ≤ (N : ℝ) * C * (A + B * (N : ℝ)) ^ 2 := by
  let P : ℕ → ℝ := fun k => if k < n then O k else 0
  let times := levelCrossingTimes P (fun j => S * (1 / 2 : ℝ) ^ j)
  let Q : ℝ := (1 / 2 : ℝ) ^ α
  let C : ℝ := 2 / s + 2
  let A : ℝ := 1 + |Real.log a|
  let B : ℝ := |Real.log q|
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQ1 : Q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := abs_nonneg _
  have hspec := finite_dyadic_level_blocks O u S s a q n hS hs hs1 ha hq h0 hu hstep
  have htn : ∀ j, times j ≤ n := fun j => (hspec j).1
  have hmono : ∀ j, times j ≤ times (j + 1) := fun j => (hspec j).2.2.1
  have hlen : ∀ j, ((times (j + 1) - times j : ℕ) : ℝ) ≤
      C * (A + B * (j : ℝ)) ^ 2 := by
    intro j
    have hh := (hspec j).2.2.2.1
    change ((times (j + 1) - times j : ℕ) : ℝ) ≤
      (2 / s + 2) * (1 + |Real.log a| + (j : ℝ) * |Real.log q|) ^ 2 at hh
    simpa only [C, A, B, mul_comm] using hh
  have hblock : ∀ j k, k < times (j + 1) - times j →
      r (times j + k + 1) ≤ (S * K) ^ α * Q ^ j + F := by
    intro j k hk
    have hkn : times j + k < n := by have := htn (j + 1); omega
    have htjn : times j < n := by omega
    have hstart : O (times j) ≤ S * (1 / 2 : ℝ) ^ j := by
      have hh := (hspec j).2.1
      change P (times j) ≤ S * (1 / 2 : ℝ) ^ j at hh
      have heq : P (times j) = O (times j) := by simp only [P, htjn, ite_true]
      rw [heq] at hh
      exact hh
    have hactive : ∀ i < times (j + 1) - times j,
        S * (1 / 2 : ℝ) ^ (j + 1) < O (times j + i) := (hspec j).2.2.2.2
    have hlocal : ∀ i < times (j + 1) - times j,
        O (times j + i + 1) ≤
          (1 - s / (1 + |Real.log (u (times j + i))|) ^ 2) * O (times j + i) := by
      intro i hi
      have hin : times j + i < n := by have := htn (j + 1); omega
      exact hstep j (times j + i) hin (hactive i hi)
    have hlo : 0 ≤ S * (1 / 2 : ℝ) ^ (j + 1) := by positivity
    have hO : 0 ≤ O (times j + k) := le_trans hlo (hactive k hk).le
    have hprev := odometer_le_block_start O (times j) (times (j + 1) - times j)
      (S * (1 / 2 : ℝ) ^ (j + 1)) s u hlo hs.le hactive hlocal k (Nat.le_of_lt hk)
    have hp := Real.rpow_le_rpow (mul_nonneg hO hK)
      (mul_le_mul_of_nonneg_right (hprev.trans hstart) hK) hα.le
    have heq : ((S * (1 / 2 : ℝ) ^ j) * K) ^ α = (S * K) ^ α * Q ^ j := by
      dsimp [Q]
      rw [show (S * (1 / 2 : ℝ) ^ j) * K = (S * K) * (1 / 2 : ℝ) ^ j by ring,
        Real.mul_rpow (mul_nonneg hS.le hK) (by positivity),
        ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2) j α,
        mul_comm (j : ℝ) α, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2) α j]
    rw [heq] at hp
    have hterm : 0 ≤ (S * K) ^ α * Q ^ j := by positivity
    exact (hr (times j + k) hkn).trans (max_le (by linarith) (by linarith))
  have ht0 : times 0 = 0 := by rfl
  have hsum := crossing_blocks_radius_budget times (fun j k => r (times j + k + 1))
    N Q ((S * K) ^ α) F C A B hQ hQ1 (by positivity) hC hA hB ht0 hmono
    (fun j _ => hlen j) (fun j _ k hk => hblock j k hk)
  rw [sum_delayed_radii_over_crossing_blocks r times ht0 hmono N] at hsum
  have hhorizon := crossing_time_le_quadratic_level_horizon times N C A B hC hA hB ht0 hmono hlen
  have hcross : O (times N) ≤ S * (1 / 2 : ℝ) ^ N ∨ times N = n := by
    by_cases ht : times N < n
    · left
      have hh := (hspec N).2.1
      change P (times N) ≤ S * (1 / 2 : ℝ) ^ N at hh
      have heq : P (times N) = O (times N) := by simp only [P, ht, ite_true]
      rw [heq] at hh
      exact hh
    · right
      have := htn N
      omega
  exact ⟨htn N, hcross, hsum, hhorizon⟩

end MatedCRT.Sec7
