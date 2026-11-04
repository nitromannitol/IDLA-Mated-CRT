import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LogLossSeries
import Mathlib.Algebra.Ring.GeomSum

/-! Control of the geometric shell-radius sum for a small contraction rate. -/

namespace MatedCRT.Sec7

/-- A positive real power loses at least a constant multiple of the gap from
one. The constant is the reciprocal of any natural number whose reciprocal is
bounded above by the exponent. -/
theorem one_sub_rpow_ge_gap_div_nat
    (q α : ℝ) (N : ℕ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hN : 0 < N) (hα : 1 / (N : ℝ) ≤ α) :
    (1 - q) / (N : ℝ) ≤ 1 - q ^ α := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let y := q ^ (1 / (N : ℝ))
  have hy : 0 ≤ y := Real.rpow_nonneg hq _
  have hy1 : y ≤ 1 := Real.rpow_le_one hq hq1 (by positivity)
  have hyN : y ^ N = q := by
    dsimp [y]
    rw [← Real.rpow_mul_natCast hq]
    have h : (1 / (N : ℝ)) * N = 1 := by field_simp
    rw [h, Real.rpow_one]
  have hcomp : q ^ α ≤ y :=
    Real.rpow_le_rpow_of_exponent_ge' hq hq1 (by positivity) hα
  have hsum : (∑ i ∈ Finset.range N, y ^ i) ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_one₀ hy hy1
      _ = _ := by simp
  have hgeom := geom_sum_mul_of_le_one hy1 N
  rw [hyN] at hgeom
  have hmul := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hy1)
  apply (div_le_iff₀ hNr).2
  nlinarith

/-- The geometric radius sum under a logarithmic contraction is bounded by a
quadratic logarithmic loss, uniformly as the contraction rate tends to zero. -/
theorem log_contraction_geometric_sum_le
    (x s a α : ℝ) (N : ℕ) (hx : 0 ≤ x) (hs : 0 < s)
    (hsbound : s ≤ (1 + |Real.log a|) ^ 2)
    (hN : 0 < N) (hα : 1 / (N : ℝ) ≤ α) :
    x / (1 - (1 - s / (1 + |Real.log a|) ^ 2) ^ α) ≤
      x * (N : ℝ) * (1 + |Real.log a|) ^ 2 / s := by
  let L := (1 + |Real.log a|) ^ 2
  let p := s / L
  have hL : 0 < L := by dsimp [L]; positivity
  have hp : 0 < p := div_pos hs hL
  have hp1 : p ≤ 1 := (div_le_one₀ hL).2 hsbound
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hgap := one_sub_rpow_ge_gap_div_nat (1 - p) α N
    (sub_nonneg.mpr hp1) (by linarith) hN hα
  have hgap' : p / (N : ℝ) ≤ 1 - (1 - p) ^ α := by simpa using hgap
  have hpos : 0 < p / (N : ℝ) := div_pos hp hN'
  calc
    _ ≤ x / (p / (N : ℝ)) := div_le_div_of_nonneg_left hx hpos hgap'
    _ = _ := by dsimp [p, L]; field_simp

end MatedCRT.Sec7
