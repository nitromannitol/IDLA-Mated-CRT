import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.Iteration
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Stopping-time and radius estimates for the shell iteration. -/

namespace MatedCRT.Sec7

open Filter Topology

/-- A maximum which contracts whenever it exceeds a positive threshold reaches
that threshold in finitely many steps. -/
theorem exists_shell_maximum_le_threshold (O : ℕ → ℝ) (q B : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hB : 0 < B)
    (hstep : ∀ k, B < O k → O (k + 1) ≤ q * O k) :
    ∃ n, O n ≤ B := by
  by_contra h
  have hall : ∀ n, B < O n := by simpa only [not_exists, not_le] using h
  have hgeom : ∀ n, O n ≤ O 0 * q ^ n :=
    shell_maximum_le_geometric O q hq (fun k => hstep k (hall k))
  have hlim : Tendsto (fun n : ℕ => O 0 * q ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1))
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 B hB)
  exact (not_lt_of_ge (hgeom N)) ((hN N le_rfl).trans (hall N))

/-- Before the first threshold crossing, the number of shell steps is bounded
by the logarithm of the initial-to-threshold odometer ratio. -/
theorem shell_steps_lt_log_ratio (O : ℕ → ℝ) (q B : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hB : 0 < B) (n : ℕ)
    (hbefore : B < O n)
    (hstep : ∀ k < n, O (k + 1) ≤ q * O k) :
    (n : ℝ) < Real.log (O 0 / B) / (-Real.log q) := by
  have hgeom : ∀ k ≤ n, O k ≤ O 0 * q ^ k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        O (k + 1) ≤ q * O k := hstep k (by omega)
        _ ≤ q * (O 0 * q ^ k) := mul_le_mul_of_nonneg_left (ih (by omega)) hq.le
        _ = O 0 * q ^ (k + 1) := by rw [pow_succ]; ring
  have hprod : B < O 0 * q ^ n := lt_of_lt_of_le hbefore (hgeom n le_rfl)
  have hO : 0 < O 0 := by
    have : 0 < O 0 * q ^ n := lt_trans hB hprod
    exact pos_of_mul_pos_left this (pow_nonneg hq.le n)
  have hlog := Real.log_lt_log hB hprod
  rw [Real.log_mul hO.ne' (pow_ne_zero _ hq.ne'), Real.log_pow] at hlog
  have hqlog : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  rw [lt_div_iff₀ hqlog, Real.log_div hO.ne' hB.ne']
  nlinarith

/-- The first crossing exists and is at most one more than the logarithmic bound
for the previous shell. The contraction is only required before crossing. -/
theorem exists_first_shell_threshold_with_log_bound (O : ℕ → ℝ) (q B : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hB : 0 < B) (hinitial : B < O 0)
    (hstep : ∀ k, B < O k → O (k + 1) ≤ q * O k) :
    ∃ τ : ℕ, O τ ≤ B ∧ (∀ k < τ, B < O k) ∧
      (τ : ℝ) < Real.log (O 0 / B) / (-Real.log q) + 1 := by
  have hex := exists_shell_maximum_le_threshold O q B hq.le hq1 hB hstep
  let τ := Nat.find hex
  have hτ : O τ ≤ B := Nat.find_spec hex
  have hprev : ∀ k < τ, B < O k := by
    intro k hk
    exact lt_of_not_ge (Nat.find_min hex hk)
  have hτpos : 0 < τ := by
    by_contra hn
    have hτ0 : τ = 0 := Nat.eq_zero_of_not_pos hn
    rw [hτ0] at hτ
    exact (not_le_of_gt hinitial) hτ
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hτpos)
  have hbound := shell_steps_lt_log_ratio O q B hq hq1 hB n
    (hprev n (by omega)) (fun k hk => hstep k (hprev k (by omega)))
  refine ⟨τ, hτ, hprev, ?_⟩
  rw [hn, Nat.cast_succ]
  linarith

/-- The logarithmic odometer ratio in the second phase of the iteration. -/
theorem log_initial_to_threshold (C ε ω : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    Real.log ((C / ε) / ε ^ (-ω)) =
      Real.log C + (1 - ω) * Real.log ε⁻¹ := by
  rw [Real.log_div (div_ne_zero hC.ne' hε.ne') (Real.rpow_pos_of_pos hε _).ne',
    Real.log_div hC.ne' hε.ne', Real.log_rpow hε, Real.log_inv]
  ring

/-- For an initial maximum at most `C / ε` and threshold `ε ^ (-ω)`, the
first threshold crossing has the logarithmic bound used in Step 2. -/
theorem exists_first_shell_threshold_log_scale (O : ℕ → ℝ) (q C ε ω : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hC : 0 < C) (hε : 0 < ε)
    (hinitial : ε ^ (-ω) < O 0) (hupper : O 0 ≤ C / ε)
    (hstep : ∀ k, ε ^ (-ω) < O k → O (k + 1) ≤ q * O k) :
    ∃ τ : ℕ, O τ ≤ ε ^ (-ω) ∧ (∀ k < τ, ε ^ (-ω) < O k) ∧
      (τ : ℝ) < (Real.log C + (1 - ω) * Real.log ε⁻¹) / (-Real.log q) + 1 := by
  have hB : 0 < ε ^ (-ω) := Real.rpow_pos_of_pos hε _
  obtain ⟨τ, hτ, hbefore, hbound⟩ :=
    exists_first_shell_threshold_with_log_bound O q (ε ^ (-ω)) hq hq1 hB hinitial hstep
  refine ⟨τ, hτ, hbefore, ?_⟩
  have hlog : Real.log (O 0 / ε ^ (-ω)) ≤ Real.log ((C / ε) / ε ^ (-ω)) :=
    Real.log_le_log (div_pos (lt_trans hB hinitial) hB) (div_le_div_of_nonneg_right hupper hB.le)
  rw [log_initial_to_threshold C ε ω hC hε] at hlog
  have hden : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq hq1)
  have hdiv := div_le_div_of_nonneg_right hlog hden.le
  linarith

/-- A maximum-based radius reduces to its geometric branch while it is strictly
above the floor. This uses an inequality, not equality for the maximum. -/
theorem shell_radius_le_geometric_above_floor {r A q R : ℝ} {k : ℕ}
    (hr : r ≤ max (A * q ^ k) R) (hfloor : R < r) : r ≤ A * q ^ k := by
  rcases le_total (A * q ^ k) R with h | h
  · rw [max_eq_right h] at hr
    linarith
  · rwa [max_eq_left h] at hr

/-- A uniformly bounded tail contributes at most its length times the floor. -/
theorem shell_radius_tail_sum_le (r : ℕ → ℝ) (R : ℝ) (n : ℕ)
    (hr : ∀ k < n, r k ≤ R) : ∑ k ∈ Finset.range n, r k ≤ (n : ℝ) * R := by
  calc
    ∑ k ∈ Finset.range n, r k ≤ ∑ _k ∈ Finset.range n, R :=
      Finset.sum_le_sum fun k hk => hr k (Finset.mem_range.mp hk)
    _ = (n : ℝ) * R := by simp

/-- The floor-scale contribution to the total radius vanishes, even with a
logarithmic number of shell steps. -/
theorem tendsto_shell_floor_log_bound (A B ω : ℝ) (hω : 0 < ω) :
    Tendsto (fun ε : ℝ => (A + B * Real.log ε⁻¹) * ε ^ ω) (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun ε : ℝ => ε ^ ω) (𝓝[>] 0) (𝓝 0) := by
    have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa [Real.zero_rpow hω.ne'] using hi.rpow_const (Or.inr hω.le)
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero hω
  have hlim := (hp.const_mul A).add (hlog.neg.const_mul B)
  simp only [mul_zero, neg_zero, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [] with ε
  rw [Real.log_inv]
  ring

end MatedCRT.Sec7
