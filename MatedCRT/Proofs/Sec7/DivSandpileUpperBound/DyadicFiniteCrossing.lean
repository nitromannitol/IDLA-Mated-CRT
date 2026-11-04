import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicLevelCrossing

/-! First dyadic level crossing before a finite shell horizon. -/

namespace MatedCRT.Sec7

/-- A block either crosses its level or reaches the given horizon. Its length
has the same logarithmic bound as an unconstrained first crossing, and the
radius and contraction estimates are only required before the horizon. -/
theorem exists_first_geometric_level_crossing_or_horizon
    (O r : ℕ → ℝ) (s a q lo : ℝ) (j n : ℕ)
    (hs : 0 < s) (hs1 : s ≤ 1) (ha : 0 < a) (hq : 0 < q) (hlo : 0 < lo)
    (hstart : O 0 ≤ 2 * lo)
    (hr : ∀ k < n, lo < O k → a * q ^ j ≤ r k ∧ r k ≤ 1)
    (hstep : ∀ k < n, lo < O k →
      O (k + 1) ≤ (1 - s / (1 + |Real.log (r k)|) ^ 2) * O k) :
    ∃ τ : ℕ, τ ≤ n ∧ (O τ ≤ lo ∨ τ = n) ∧ (∀ k < τ, lo < O k) ∧
      (τ : ℝ) ≤ (2 / s + 2) * (1 + |Real.log a| + (j : ℝ) * |Real.log q|) ^ 2 := by
  by_cases hn : n = 0
  · subst n
    refine ⟨0, le_rfl, Or.inr rfl, ?_, ?_⟩
    · intro k hk
      omega
    · simp only [Nat.cast_zero]
      positivity
  let P : ℕ → ℝ := fun k => if k < n then O k else 0
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hp0 : P 0 = O 0 := by simp [P, hnpos]
  have hpstart : P 0 ≤ 2 * lo := by simpa [hp0] using hstart
  have hpr : ∀ k, lo < P k → a * q ^ j ≤ r k ∧ r k ≤ 1 := by
    intro k hk
    have hkn : k < n := by
      by_contra h
      simp [P, h] at hk
      linarith
    exact hr k hkn (by simpa [P, hkn] using hk)
  have hpstep : ∀ k, lo < P k →
      P (k + 1) ≤ (1 - s / (1 + |Real.log (r k)|) ^ 2) * P k := by
    intro k hk
    have hkn : k < n := by
      by_contra h
      simp [P, h] at hk
      linarith
    have hkO : lo < O k := by simpa [P, hkn] using hk
    by_cases hnext : k + 1 < n
    · simpa [P, hkn, hnext] using hstep k hkn hkO
    · have hden : 1 ≤ (1 + |Real.log (r k)|) ^ 2 := by
        have := abs_nonneg (Real.log (r k))
        nlinarith
      have hrate : s / (1 + |Real.log (r k)|) ^ 2 ≤ 1 :=
        (div_le_one₀ (by linarith)).2 (hs1.trans hden)
      have hnonneg : 0 ≤ (1 - s / (1 + |Real.log (r k)|) ^ 2) * O k :=
        mul_nonneg (by linarith) (by linarith)
      simpa [P, hkn, hnext] using hnonneg
  obtain ⟨τ, hτ, hbefore, hbound⟩ :=
    exists_first_geometric_level_crossing P r s a q lo j hs ha hq hlo hpstart hpr hpstep
  have hτn : τ ≤ n := by
    by_contra h
    have := hbefore n (by omega)
    simp [P] at this
    linarith
  refine ⟨τ, hτn, ?_, ?_, hbound⟩
  · by_cases hlt : τ < n
    · exact Or.inl (by simpa [P, hlt] using hτ)
    · exact Or.inr (by omega)
  · intro k hk
    have hkn : k < n := by omega
    simpa [P, hkn] using hbefore k hk

end MatedCRT.Sec7
