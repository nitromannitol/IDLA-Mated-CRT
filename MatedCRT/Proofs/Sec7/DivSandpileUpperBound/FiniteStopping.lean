import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.Stopping

/-! Finite-horizon stopping for the shell iteration. -/

namespace MatedCRT.Sec7

/-- If the geometric majorant is below the threshold at the end of a finite
horizon, a first threshold crossing occurs within that horizon.  Contraction
is only needed before the crossing and within the horizon. -/
theorem exists_first_shell_threshold_before_horizon
    (O : ℕ → ℝ) (q B : ℝ) (n : ℕ) (hq : 0 ≤ q)
    (hbound : O 0 * q ^ n ≤ B)
    (hstep : ∀ k < n, B < O k → O (k + 1) ≤ q * O k) :
    ∃ τ : ℕ, τ ≤ n ∧ O τ ≤ B ∧ ∀ k < τ, B < O k := by
  have hex : ∃ k, k ≤ n ∧ O k ≤ B := by
    by_contra h
    have habove : ∀ k ≤ n, B < O k := by
      intro k hk
      exact lt_of_not_ge (fun hle => h ⟨k, hk, hle⟩)
    have hgeom : ∀ k ≤ n, O k ≤ O 0 * q ^ k := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        calc
          O (k + 1) ≤ q * O k := hstep k (by omega) (habove k (by omega))
          _ ≤ q * (O 0 * q ^ k) := mul_le_mul_of_nonneg_left (ih (by omega)) hq
          _ = O 0 * q ^ (k + 1) := by rw [pow_succ]; ring
    exact (not_lt_of_ge ((hgeom n le_rfl).trans hbound)) (habove n le_rfl)
  let τ := Nat.find hex
  have hτn : τ ≤ n := (Nat.find_spec hex).1
  refine ⟨τ, hτn, (Nat.find_spec hex).2, ?_⟩
  intro k hk
  have hnot := Nat.find_min hex hk
  exact lt_of_not_ge (fun hle => hnot ⟨by omega, hle⟩)

/-- The finite-horizon crossing also satisfies the logarithmic step bound when
the initial maximum is above the threshold. -/
theorem exists_first_shell_threshold_before_horizon_with_log_bound
    (O : ℕ → ℝ) (q B : ℝ) (n : ℕ) (hq : 0 < q) (hq1 : q < 1)
    (hB : 0 < B) (hinitial : B < O 0) (hbound : O 0 * q ^ n ≤ B)
    (hstep : ∀ k < n, B < O k → O (k + 1) ≤ q * O k) :
    ∃ τ : ℕ, τ ≤ n ∧ O τ ≤ B ∧ (∀ k < τ, B < O k) ∧
      (τ : ℝ) < Real.log (O 0 / B) / (-Real.log q) + 1 := by
  obtain ⟨τ, hτn, hτ, hprev⟩ :=
    exists_first_shell_threshold_before_horizon O q B n hq.le hbound hstep
  have hτpos : 0 < τ := by
    by_contra h
    have hτ0 : τ = 0 := Nat.eq_zero_of_not_pos h
    rw [hτ0] at hτ
    exact (not_le_of_gt hinitial) hτ
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hτpos)
  have hlog := shell_steps_lt_log_ratio O q B hq hq1 hB k
    (hprev k (by omega)) (fun j hj => hstep j (by omega) (hprev j (by omega)))
  refine ⟨τ, hτn, hτ, hprev, ?_⟩
  rw [hk, Nat.cast_succ]
  linarith

end MatedCRT.Sec7
