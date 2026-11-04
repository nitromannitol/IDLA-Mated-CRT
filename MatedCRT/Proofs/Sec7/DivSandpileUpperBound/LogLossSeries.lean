import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! A geometric series with the quadratic loss arising from shell halving. -/

namespace MatedCRT.Sec7

open Filter Topology

/-- A quadratic polynomial times a geometric sequence is summable. -/
theorem summable_quadratic_mul_geometric {q : ℝ} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * q ^ n) := by
  have h0 : Summable (fun n : ℕ => q ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 0 hq)
  have h1 : Summable (fun n : ℕ => (n : ℝ) * q ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 hq)
  have h2 : Summable (fun n : ℕ => (n : ℝ) ^ 2 * q ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hq
  convert (h2.add (h1.mul_left 2)).add h0 using 1
  ext n
  ring

/-- Every finite sum of shell scales times a quadratic logarithmic loss is
bounded by a constant depending only on the geometric ratio. -/
theorem quadratic_geometric_sum_le
    {q A B : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (N : ℕ) :
    (∑ n ∈ Finset.range N, (A + B * (n : ℝ)) ^ 2 * q ^ n) ≤
      (A + B) ^ 2 * ∑' n : ℕ, ((n : ℝ) + 1) ^ 2 * q ^ n := by
  have hqnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  have hs := summable_quadratic_mul_geometric hqnorm
  have hterm : ∀ n : ℕ, (A + B * (n : ℝ)) ^ 2 * q ^ n ≤
      (A + B) ^ 2 * (((n : ℝ) + 1) ^ 2 * q ^ n) := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hcomp : A + B * n ≤ (A + B) * (n + 1) := by nlinarith
    have hnonneg : 0 ≤ A + B * n := by positivity
    have hsq := pow_le_pow_left₀ hnonneg hcomp 2
    have hqpow : 0 ≤ q ^ n := pow_nonneg hq _
    nlinarith [mul_le_mul_of_nonneg_right hsq hqpow]
  calc
    _ ≤ ∑ n ∈ Finset.range N, (A + B) ^ 2 * (((n : ℝ) + 1) ^ 2 * q ^ n) :=
      Finset.sum_le_sum (fun n _ => hterm n)
    _ = (A + B) ^ 2 * ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ 2 * q ^ n := by
      rw [Finset.mul_sum]
    _ ≤ (A + B) ^ 2 * ∑' n : ℕ, ((n : ℝ) + 1) ^ 2 * q ^ n :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (by intros; positivity)) (sq_nonneg _)

/-- A positive power dominates the quadratic logarithmic loss at zero. -/
theorem tendsto_rpow_mul_quadratic_log_loss {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto (fun x : ℝ => x ^ α * (1 + |Real.log x|) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hhalf : 0 < α / 2 := by positivity
  have hp : Filter.Tendsto (fun x : ℝ => x ^ (α / 2)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (α / 2) (Or.inr hhalf.le)).tendsto
    simpa [Real.zero_rpow hhalf.ne'] using h.mono_left nhdsWithin_le_nhds
  have hl := (tendsto_log_mul_rpow_nhdsGT_zero hhalf).abs
  have hs : Filter.Tendsto (fun x : ℝ => x ^ (α / 2) + |Real.log x * x ^ (α / 2)|)
      (𝓝[>] 0) (𝓝 0) := by simpa using hp.add hl
  have hs2 : Filter.Tendsto
      (fun x : ℝ => (x ^ (α / 2) + |Real.log x * x ^ (α / 2)|) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by simpa using hs.pow 2
  apply hs2.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := hx
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]
  have hr : x ^ α = (x ^ (α / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    congr 1
    ring
  rw [hr]
  ring

end MatedCRT.Sec7
