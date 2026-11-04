import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicLevelTimes

/-! Dyadic odometer blocks under the radius-dependent contraction estimate. -/

namespace MatedCRT.Sec7

/-- The shell maximum admits first-crossing blocks at all dyadic levels.
Each block is bounded by the corresponding quadratic logarithmic loss, even
when a single shell crosses several levels. -/
theorem dyadic_level_crossing_times_spec
    (O r : ℕ → ℝ) (S s a q : ℝ)
    (hS : 0 < S) (hs : 0 < s) (ha : 0 < a) (hq : 0 < q)
    (h0 : O 0 ≤ S)
    (hr : ∀ j k, S * (1 / 2 : ℝ) ^ (j + 1) < O k →
      a * q ^ j ≤ r k ∧ r k ≤ 1)
    (hstep : ∀ j k, S * (1 / 2 : ℝ) ^ (j + 1) < O k →
      O (k + 1) ≤ (1 - s / (1 + |Real.log (r k)|) ^ 2) * O k) :
    let level : ℕ → ℝ := fun j => S * (1 / 2 : ℝ) ^ j
    let times := levelCrossingTimes O level
    ∀ j, O (times j) ≤ level j ∧ times j ≤ times (j + 1) ∧
      ((times (j + 1) - times j : ℕ) : ℝ) ≤
        (2 / s + 2) * (1 + |Real.log a| + (j : ℝ) * |Real.log q|) ^ 2 ∧
      ∀ k < times (j + 1) - times j, level (j + 1) < O (times j + k) := by
  dsimp only
  apply levelCrossingTimes_spec O (fun j => S * (1 / 2 : ℝ) ^ j)
    (fun j => (2 / s + 2) * (1 + |Real.log a| + (j : ℝ) * |Real.log q|) ^ 2)
  · simpa using h0
  · intro j t ht
    have hlo : 0 < S * (1 / 2 : ℝ) ^ (j + 1) := by positivity
    have hstart : O t ≤ 2 * (S * (1 / 2 : ℝ) ^ (j + 1)) := by
      calc
        O t ≤ S * (1 / 2 : ℝ) ^ j := ht
        _ = 2 * (S * (1 / 2 : ℝ) ^ (j + 1)) := by rw [pow_succ]; ring
    obtain ⟨d, hd, _, hbound⟩ := exists_first_geometric_level_crossing
      (fun k => O (t + k)) (fun k => r (t + k)) s a q
      (S * (1 / 2 : ℝ) ^ (j + 1)) j hs ha hq hlo (by simpa using hstart)
      (fun k hk => hr j (t + k) hk)
      (fun k hk => by simpa [Nat.add_assoc] using hstep j (t + k) hk)
    exact ⟨d, hd, hbound⟩

end MatedCRT.Sec7
