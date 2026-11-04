import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicBlockLength

/-! Crossing fixed geometric levels, including levels skipped by an overshoot. -/

namespace MatedCRT.Sec7

/-- The first crossing of a fixed level has the same quadratic logarithmic
bound as a halving block. If the level is already crossed, the stopping time
is zero; no radius or contraction hypothesis is needed at skipped levels. -/
theorem exists_first_geometric_level_crossing
    (O r : ℕ → ℝ) (s a q lo : ℝ) (j : ℕ)
    (hs : 0 < s) (ha : 0 < a) (hq : 0 < q) (hlo : 0 < lo)
    (hstart : O 0 ≤ 2 * lo)
    (hr : ∀ k, lo < O k → a * q ^ j ≤ r k ∧ r k ≤ 1)
    (hstep : ∀ k, lo < O k →
      O (k + 1) ≤ (1 - s / (1 + |Real.log (r k)|) ^ 2) * O k) :
    ∃ τ : ℕ, O τ ≤ lo ∧ (∀ k < τ, lo < O k) ∧
      (τ : ℝ) ≤ (2 / s + 2) * (1 + |Real.log a| + (j : ℝ) * |Real.log q|) ^ 2 := by
  let L := 1 + |Real.log a| + (j : ℝ) * |Real.log q|
  have hL : 1 ≤ L := by
    dsimp [L]
    have hmul : 0 ≤ (j : ℝ) * |Real.log q| := by positivity
    linarith [abs_nonneg (Real.log a)]
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  let N : ℕ := ⌈2 * L ^ 2 / s⌉₊ + 1
  have hn0 : 0 ≤ 2 * L ^ 2 / s := by positivity
  have hnhi := Nat.ceil_lt_add_one hn0
  have hNlo : 2 * L ^ 2 < (N : ℝ) * s := by
    have h : 2 * L ^ 2 / s < (N : ℝ) := by
      dsimp [N]
      push_cast
      have := Nat.le_ceil (2 * L ^ 2 / s)
      linarith
    exact (div_lt_iff₀ hs).1 h
  have hNhi : (N : ℝ) ≤ (2 / s + 2) * L ^ 2 := by
    dsimp [N]
    push_cast
    have hnhi' : (⌈2 * L ^ 2 / s⌉₊ : ℝ) < (2 / s) * L ^ 2 + 1 := by
      convert hnhi using 1
      ring
    nlinarith
  have hex : ∃ k ≤ N, O k ≤ lo := by
    by_contra h
    have habove : ∀ k ≤ N, lo < O k := by
      intro k hk
      exact lt_of_not_ge (fun hk' => h ⟨k, hk, hk'⟩)
    have hO : 0 < O 0 := lt_trans hlo (habove 0 (Nat.zero_le N))
    have hLsq : 0 < L ^ 2 := by positivity
    have hhalf : ∃ k ≤ N, O k ≤ O 0 / 2 := by
      apply exists_halving_before_of_uniform_contraction O (s / L ^ 2) N hO
        (div_pos hs hLsq) ?_ ?_
      · rw [← mul_div_assoc, lt_div_iff₀ hLsq]
        exact hNlo
      · intro k hk _
        have hk' : lo < O k := habove k (Nat.le_of_lt hk)
        have hlog : 1 + |Real.log (r k)| ≤ L :=
          log_loss_le_of_geometric_radius_lower_bound j ha hq (hr k hk').1 (hr k hk').2
        have hden : 0 < (1 + |Real.log (r k)|) ^ 2 := by positivity
        have hsq : (1 + |Real.log (r k)|) ^ 2 ≤ L ^ 2 :=
          pow_le_pow_left₀ (by positivity) hlog 2
        have hrate : s / L ^ 2 ≤ s / (1 + |Real.log (r k)|) ^ 2 :=
          div_le_div_of_nonneg_left hs.le hden hsq
        have hmul := mul_le_mul_of_nonneg_right hrate (show 0 ≤ O k by linarith)
        have hs' := hstep k hk'
        nlinarith
    obtain ⟨k, hk, hkhalf⟩ := hhalf
    have := habove k hk
    linarith
  let τ := Nat.find hex
  refine ⟨τ, (Nat.find_spec hex).2, ?_, ?_⟩
  · intro k hk
    have hkN : k ≤ N := (Nat.le_of_lt hk).trans (Nat.find_spec hex).1
    exact lt_of_not_ge (fun hk' => Nat.find_min hex hk ⟨hkN, hk'⟩)
  · exact (Nat.cast_le.mpr (Nat.find_spec hex).1).trans hNhi

end MatedCRT.Sec7
