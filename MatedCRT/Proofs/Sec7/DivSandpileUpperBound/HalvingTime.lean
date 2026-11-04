import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LogLossSeries

/-! Finite halving times for a shell-dependent contraction. -/

namespace MatedCRT.Sec7

/-- If the contraction has a uniform lower bound `p` until the maximum has
halved, then it halves in at most any number of steps whose product with `p`
exceeds two. This only assumes contraction before the halving time. -/
theorem exists_halving_before_of_uniform_contraction
    (O : ℕ → ℝ) (p : ℝ) (N : ℕ)
    (hO : 0 < O 0) (hp : 0 < p) (hN : 2 < (N : ℝ) * p)
    (hstep : ∀ k < N, O 0 / 2 < O k → O (k + 1) ≤ (1 - p) * O k) :
    ∃ k ≤ N, O k ≤ O 0 / 2 := by
  by_contra h
  have habove : ∀ k ≤ N, O 0 / 2 < O k := by
    intro k hk
    exact lt_of_not_ge (fun hk' => h ⟨k, hk, hk'⟩)
  have hbound : ∀ k ≤ N, O k ≤ O 0 - (k : ℝ) * (p * (O 0 / 2)) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hmul := mul_le_mul_of_nonneg_left (habove k (by omega)).le hp.le
      have hnext := hstep k (by omega) (habove k (by omega))
      have hprev := ih (by omega)
      push_cast
      nlinarith
  have hprod := mul_lt_mul_of_pos_right hN (show 0 < O 0 / 2 by linarith)
  have hlast := hbound N le_rfl
  have hlastpos := habove N le_rfl
  nlinarith

/-- On a range of radii where the log-loss denominator is at most `L²`,
the halving time is at most a constant multiple of `L² / s`. -/
theorem exists_halving_before_of_log_loss
    (O : ℕ → ℝ) (r : ℕ → ℝ) (s L : ℝ) (N : ℕ)
    (hO : 0 < O 0) (hs : 0 < s) (hL : 0 < L)
    (hN : 2 * L ^ 2 < (N : ℝ) * s)
    (hlog : ∀ k < N, 1 + |Real.log (r k)| ≤ L)
    (hstep : ∀ k < N, O 0 / 2 < O k →
      O (k + 1) ≤ (1 - s / (1 + |Real.log (r k)|) ^ 2) * O k) :
    ∃ k ≤ N, O k ≤ O 0 / 2 := by
  have hLsq : 0 < L ^ 2 := by positivity
  apply exists_halving_before_of_uniform_contraction O (s / L ^ 2) N hO
    (div_pos hs hLsq) ?_ ?_
  · rw [← mul_div_assoc, lt_div_iff₀ hLsq]
    nlinarith
  · intro k hk hOk
    have hden : 0 < (1 + |Real.log (r k)|) ^ 2 := by positivity
    have hle : (1 + |Real.log (r k)|) ^ 2 ≤ L ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hlog k hk) 2
    have hrate : s / L ^ 2 ≤ s / (1 + |Real.log (r k)|) ^ 2 :=
      div_le_div_of_nonneg_left hs.le hden hle
    have hpos : 0 ≤ O k := by linarith
    have hmul := mul_le_mul_of_nonneg_right hrate hpos
    have h := hstep k hk hOk
    nlinarith

/-- A positive lower scale bounds the logarithmic loss for radii at most one. -/
theorem log_loss_le_of_radius_lower_bound {a r : ℝ}
    (ha : 0 < a) (har : a ≤ r) (hr : r ≤ 1) :
    1 + |Real.log r| ≤ 1 + |Real.log a| := by
  have hrpos : 0 < r := lt_of_lt_of_le ha har
  have ha1 : a ≤ 1 := har.trans hr
  have hlog := Real.log_le_log ha har
  rw [abs_of_nonpos (Real.log_nonpos hrpos.le hr),
    abs_of_nonpos (Real.log_nonpos ha.le ha1)]
  linarith

/-- A shell radius floor gives an explicit logarithmic halving-time bound,
and the chosen index is the first time that the maximum has halved. -/
theorem exists_first_halving_before_of_radius_floor
    (O : ℕ → ℝ) (r : ℕ → ℝ) (s a : ℝ) (N : ℕ)
    (hO : 0 < O 0) (hs : 0 < s) (ha : 0 < a)
    (hN : 2 * (1 + |Real.log a|) ^ 2 < (N : ℝ) * s)
    (hr : ∀ k < N, a ≤ r k ∧ r k ≤ 1)
    (hstep : ∀ k < N, O 0 / 2 < O k →
      O (k + 1) ≤ (1 - s / (1 + |Real.log (r k)|) ^ 2) * O k) :
    ∃ τ ≤ N, O τ ≤ O 0 / 2 ∧ ∀ k < τ, O 0 / 2 < O k := by
  have hex := exists_halving_before_of_log_loss O r s (1 + |Real.log a|) N
    hO hs (by positivity) hN
    (fun k hk => log_loss_le_of_radius_lower_bound ha (hr k hk).1 (hr k hk).2) hstep
  let τ := Nat.find hex
  refine ⟨τ, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro k hk
  have hkN : k ≤ N := (Nat.le_of_lt hk).trans (Nat.find_spec hex).1
  exact lt_of_not_ge (fun hk' => Nat.find_min hex hk ⟨hkN, hk'⟩)

end MatedCRT.Sec7
