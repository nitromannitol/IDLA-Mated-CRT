import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicFiniteTimes
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicLevelBlocks

/-! Dyadic level blocks with contraction restricted to a finite horizon. -/

namespace MatedCRT.Sec7

/-- A zero extension turns finite-horizon contraction into global contraction
without imposing any estimate on the original odometer after the horizon. -/
theorem finite_dyadic_level_blocks
    (O r : ℕ → ℝ) (S s a q : ℝ) (n : ℕ)
    (hS : 0 < S) (hs : 0 < s) (hs1 : s ≤ 1) (ha : 0 < a) (hq : 0 < q)
    (h0 : O 0 ≤ S)
    (hr : ∀ j k, k < n → S * (1 / 2 : ℝ) ^ (j + 1) < O k →
      a * q ^ j ≤ r k ∧ r k ≤ 1)
    (hstep : ∀ j k, k < n → S * (1 / 2 : ℝ) ^ (j + 1) < O k →
      O (k + 1) ≤ (1 - s / (1 + |Real.log (r k)|) ^ 2) * O k) :
    let P : ℕ → ℝ := fun k => if k < n then O k else 0
    let level : ℕ → ℝ := fun j => S * (1 / 2 : ℝ) ^ j
    let times := levelCrossingTimes P level
    ∀ j, times j ≤ n ∧ P (times j) ≤ level j ∧ times j ≤ times (j + 1) ∧
      ((times (j + 1) - times j : ℕ) : ℝ) ≤
        (2 / s + 2) * (1 + |Real.log a| + (j : ℝ) * |Real.log q|) ^ 2 ∧
      ∀ k < times (j + 1) - times j, level (j + 1) < O (times j + k) := by
  let P : ℕ → ℝ := fun k => if k < n then O k else 0
  let level : ℕ → ℝ := fun j => S * (1 / 2 : ℝ) ^ j
  let times := levelCrossingTimes P level
  have hp0 : P 0 ≤ S := by
    by_cases hn : 0 < n
    · simpa [P, hn] using h0
    · simpa [P, hn] using hS.le
  have hpr : ∀ j k, level (j + 1) < P k → a * q ^ j ≤ r k ∧ r k ≤ 1 := by
    intro j k hk
    have hlevel : 0 < level (j + 1) := by dsimp [level]; positivity
    have hkn : k < n := by
      by_contra h
      simp [P, h] at hk
      linarith
    exact hr j k hkn (by simpa [P, hkn, level] using hk)
  have hpstep : ∀ j k, level (j + 1) < P k →
      P (k + 1) ≤ (1 - s / (1 + |Real.log (r k)|) ^ 2) * P k := by
    intro j k hk
    have hlevel : 0 < level (j + 1) := by dsimp [level]; positivity
    have hkn : k < n := by
      by_contra h
      simp [P, h] at hk
      linarith
    have hkO : S * (1 / 2 : ℝ) ^ (j + 1) < O k := by simpa [P, hkn, level] using hk
    by_cases hnext : k + 1 < n
    · simpa [P, hkn, hnext] using hstep j k hkn hkO
    · have hden : 1 ≤ (1 + |Real.log (r k)|) ^ 2 := by
        have := abs_nonneg (Real.log (r k))
        nlinarith
      have hrate : s / (1 + |Real.log (r k)|) ^ 2 ≤ 1 :=
        (div_le_one₀ (by linarith)).2 (hs1.trans hden)
      have hnonneg : 0 ≤ (1 - s / (1 + |Real.log (r k)|) ^ 2) * O k :=
        mul_nonneg (by linarith) (by linarith [hlevel])
      simpa [P, hkn, hnext] using hnonneg
  have hspec := dyadic_level_crossing_times_spec P r S s a q hS hs ha hq hp0 hpr hpstep
  have htn : ∀ j, times j ≤ n := by
    apply levelCrossingTimes_le_terminal P level n
    intro j
    have hlev : 0 ≤ level (j + 1) := by dsimp [level]; positivity
    simpa [P] using hlev
  change ∀ j, times j ≤ n ∧ P (times j) ≤ level j ∧ times j ≤ times (j + 1) ∧
      ((times (j + 1) - times j : ℕ) : ℝ) ≤
        (2 / s + 2) * (1 + |Real.log a| + (j : ℝ) * |Real.log q|) ^ 2 ∧
      ∀ k < times (j + 1) - times j, level (j + 1) < O (times j + k)
  intro j
  obtain ⟨hstart, hmono, hlen, hactive⟩ := hspec j
  refine ⟨htn j, hstart, hmono, hlen, ?_⟩
  intro k hk
  have hkn : times j + k < n := by have := htn (j + 1); omega
  have hactive' : level (j + 1) < P (times j + k) := hactive k hk
  have heq : P (times j + k) = O (times j + k) := by simp only [P, hkn, ite_true]
  rw [heq] at hactive'
  exact hactive'

end MatedCRT.Sec7
