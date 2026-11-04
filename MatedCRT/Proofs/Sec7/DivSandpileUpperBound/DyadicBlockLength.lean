import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicRadius

/-! Quantitative first-halving times for the dyadic radius budget. -/

namespace MatedCRT.Sec7

/-- The first halving time has a quadratic bound in the logarithmic loss of
the geometric radius scale, with a coefficient independent of the block. -/
theorem exists_first_halving_with_geometric_radius_bound
    (O r : ℕ → ℝ) (s a q : ℝ) (j : ℕ)
    (hO : 0 < O 0) (hs : 0 < s) (ha : 0 < a) (hq : 0 < q)
    (hr : ∀ k, O 0 / 2 < O k → a * q ^ j ≤ r k ∧ r k ≤ 1)
    (hstep : ∀ k, O 0 / 2 < O k →
      O (k + 1) ≤ (1 - s / (1 + |Real.log (r k)|) ^ 2) * O k) :
    ∃ τ : ℕ, O τ ≤ O 0 / 2 ∧ (∀ k < τ, O 0 / 2 < O k) ∧
      (τ : ℝ) ≤ (2 / s + 2) * (1 + |Real.log a| + (j : ℝ) * |Real.log q|) ^ 2 := by
  let L := 1 + |Real.log a| + (j : ℝ) * |Real.log q|
  have hL : 1 ≤ L := by
    dsimp [L]
    have hmul : 0 ≤ (j : ℝ) * |Real.log q| := by positivity
    linarith [abs_nonneg (Real.log a)]
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  let N : ℕ := ⌈2 * L ^ 2 / s⌉₊ + 1
  have hn0 : 0 ≤ 2 * L ^ 2 / s := by positivity
  have hnlo := Nat.le_ceil (2 * L ^ 2 / s)
  have hnhi := Nat.ceil_lt_add_one hn0
  have hNlo : 2 * L ^ 2 < (N : ℝ) * s := by
    have h : 2 * L ^ 2 / s < (N : ℝ) := by dsimp [N]; push_cast; linarith
    exact (div_lt_iff₀ hs).1 h
  have hNhi : (N : ℝ) ≤ (2 / s + 2) * L ^ 2 := by
    dsimp [N]
    push_cast
    have hnhi' : (⌈2 * L ^ 2 / s⌉₊ : ℝ) < (2 / s) * L ^ 2 + 1 := by
      convert hnhi using 1
      ring
    nlinarith
  have hex : ∃ k ≤ N, O k ≤ O 0 / 2 := by
    have hLsq : 0 < L ^ 2 := by positivity
    apply exists_halving_before_of_uniform_contraction O (s / L ^ 2) N hO
      (div_pos hs hLsq) ?_ ?_
    · rw [← mul_div_assoc, lt_div_iff₀ hLsq]
      exact hNlo
    · intro k _ hk
      have hlog : 1 + |Real.log (r k)| ≤ L :=
        log_loss_le_of_geometric_radius_lower_bound j ha hq (hr k hk).1 (hr k hk).2
      have hden : 0 < (1 + |Real.log (r k)|) ^ 2 := by positivity
      have hsq : (1 + |Real.log (r k)|) ^ 2 ≤ L ^ 2 :=
        pow_le_pow_left₀ (by positivity) hlog 2
      have hrate : s / L ^ 2 ≤ s / (1 + |Real.log (r k)|) ^ 2 :=
        div_le_div_of_nonneg_left hs.le hden hsq
      have hmul := mul_le_mul_of_nonneg_right hrate (show 0 ≤ O k by linarith)
      have hs' := hstep k hk
      nlinarith
  let τ := Nat.find hex
  refine ⟨τ, (Nat.find_spec hex).2, ?_, ?_⟩
  · intro k hk
    have hkN : k ≤ N := (Nat.le_of_lt hk).trans (Nat.find_spec hex).1
    exact lt_of_not_ge (fun hk' => Nat.find_min hex hk ⟨hkN, hk'⟩)
  · exact (Nat.cast_le.mpr (Nat.find_spec hex).1).trans hNhi

end MatedCRT.Sec7
