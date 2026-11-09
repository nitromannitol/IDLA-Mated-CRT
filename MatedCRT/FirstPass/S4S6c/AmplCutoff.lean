import Mathlib

/-!
# The numerical amplification cutoff (q2, task fp-S4S6c; LEMMA68 D1-D2)

Pure real analysis behind the explicit cutoff (D2) of the write-up of LEMMA68: for `0 < ζ < 1/2`, `c > 0` and
`0 < r ≤ 1` with `r ≤ (c ζ² / (16 log 2))^(2/ζ)`, the exponent `c r^(-ζ) / (1 + log (1/r))²` is at least `log 2`, so
`exp (-(c r^(-ζ) / (1 + log (1/r))²)) ≤ 1/2`. The argument: `1 + t ≤ (4/ζ) exp (ζ t / 4)` for `t ≥ 0` (from
`1 + u ≤ exp u`), hence `(1 + t)² ≤ (16/ζ²) exp (ζ t / 2)`, and the cutoff gives `exp (ζ t / 2) ≥ 16 log 2 / (c ζ²)`
with `t = log (1/r)`.
-/

open Real

namespace MatedCRT

namespace AmplCutoff

theorem one_add_le_four_div_mul_exp {ζ t : ℝ} (hζ : 0 < ζ) (hζ' : ζ < 1 / 2) (ht : 0 ≤ t) :
    1 + t ≤ (4 / ζ) * Real.exp (ζ * t / 4) := by
  have hζ0 : ζ ≠ 0 := hζ.ne'
  have h1 : 1 + ζ * t / 4 ≤ Real.exp (ζ * t / 4) := by
    linarith [Real.add_one_le_exp (ζ * t / 4)]
  have h2 : 1 ≤ 4 / ζ := by
    rw [le_div_iff₀ hζ]
    linarith
  have hpos : 0 ≤ 4 / ζ := div_nonneg (by norm_num) hζ.le
  have hid : (4 / ζ) * (1 + ζ * t / 4) = 4 / ζ + t := by
    field_simp
  calc 1 + t ≤ 4 / ζ + t := by linarith
    _ = (4 / ζ) * (1 + ζ * t / 4) := hid.symm
    _ ≤ (4 / ζ) * Real.exp (ζ * t / 4) := mul_le_mul_of_nonneg_left h1 hpos

theorem sq_le_exp_half {ζ t : ℝ} (hζ : 0 < ζ) (hζ' : ζ < 1 / 2) (ht : 0 ≤ t) :
    (1 + t) ^ 2 ≤ (16 / ζ ^ 2) * Real.exp (ζ * t / 2) := by
  have h := one_add_le_four_div_mul_exp hζ hζ' ht
  have h0 : 0 ≤ 1 + t := by linarith
  have hsq : (1 + t) ^ 2 ≤ ((4 / ζ) * Real.exp (ζ * t / 4)) ^ 2 := pow_le_pow_left₀ h0 h 2
  have hE : Real.exp (ζ * t / 4) ^ 2 = Real.exp (ζ * t / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc (1 + t) ^ 2 ≤ ((4 / ζ) * Real.exp (ζ * t / 4)) ^ 2 := hsq
    _ = (16 / ζ ^ 2) * Real.exp (ζ * t / 2) := by
      rw [mul_pow, hE]
      ring

/-- **The amplification cutoff** (LEMMA68 D2): below the radius `(c ζ² / (16 log 2))^(2/ζ)` the exponent
`c r^(-ζ) / (1 + log (1/r))²` is at least `log 2`, so the exponential of its negative is at most `1/2`. -/
theorem amplification_cutoff {c ζ r : ℝ} (hc : 0 < c) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2)
    (hr : 0 < r) (hr1 : r ≤ 1) (hrA : r ≤ (c * ζ ^ 2 / (16 * Real.log 2)) ^ (2 / ζ)) :
    Real.exp (-(c * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2)) ≤ 1 / 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl20 : Real.log 2 ≠ 0 := hl2.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have hζ0 : ζ ≠ 0 := hζ.ne'
  have hL : Real.log (1 / r) = -Real.log r := by
    rw [one_div, Real.log_inv]
  have hpow : r ^ (-ζ) = Real.exp (ζ * (-Real.log r)) := by
    rw [Real.rpow_def_of_pos hr]
    congr 1
    ring
  have ht : 0 ≤ -Real.log r := by
    have := Real.log_nonpos hr.le hr1
    linarith
  rw [hL, hpow]
  generalize ht_def : -Real.log r = t at ht ⊢
  have hlr : Real.log r = -t := by linarith
  have hK : 0 < c * ζ ^ 2 / (16 * Real.log 2) :=
    div_pos (mul_pos hc (pow_pos hζ 2)) (by linarith)
  have hlogr : Real.log r ≤ (2 / ζ) * Real.log (c * ζ ^ 2 / (16 * Real.log 2)) := by
    have h := Real.log_le_log hr hrA
    rwa [Real.log_rpow hK] at h
  set K := c * ζ ^ 2 / (16 * Real.log 2) with hKdef
  -- the cutoff gives `exp (ζ t / 2) ≥ 1 / K`
  have hE_lb : K⁻¹ ≤ Real.exp (ζ * t / 2) := by
    have e1 : (ζ / 2) * ((2 / ζ) * Real.log K) = Real.log K := by
      field_simp
    have e2 : (ζ / 2) * Real.log r ≤ (ζ / 2) * ((2 / ζ) * Real.log K) :=
      mul_le_mul_of_nonneg_left hlogr (by linarith)
    have e3 : ζ * t / 2 = -((ζ / 2) * Real.log r) := by
      rw [hlr]
      ring
    have h3 : -Real.log K ≤ ζ * t / 2 := by
      linarith [e1, e2, e3]
    have h4 : Real.exp (-Real.log K) ≤ Real.exp (ζ * t / 2) := Real.exp_le_exp.2 h3
    rwa [Real.exp_neg, Real.exp_log hK] at h4
  -- hence `16 log 2 / ζ² ≤ c exp (ζ t / 2)`
  have hcE : 16 * Real.log 2 / ζ ^ 2 ≤ c * Real.exp (ζ * t / 2) := by
    have e4 : c * K⁻¹ = 16 * Real.log 2 / ζ ^ 2 := by
      rw [hKdef]
      field_simp
    have := mul_le_mul_of_nonneg_left hE_lb hc.le
    linarith [e4, this]
  have hE_pos : 0 < Real.exp (ζ * t / 2) := Real.exp_pos _
  have hexp2 : Real.exp (ζ * t) = Real.exp (ζ * t / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsq := sq_le_exp_half hζ hζ' ht
  have h1t : 0 < (1 + t) ^ 2 := pow_pos (by linarith) 2
  have hX : Real.log 2 ≤ c * Real.exp (ζ * t) / (1 + t) ^ 2 := by
    rw [le_div_iff₀ h1t]
    calc Real.log 2 * (1 + t) ^ 2 ≤ Real.log 2 * ((16 / ζ ^ 2) * Real.exp (ζ * t / 2)) :=
          mul_le_mul_of_nonneg_left hsq hl2.le
      _ = (16 * Real.log 2 / ζ ^ 2) * Real.exp (ζ * t / 2) := by ring
      _ ≤ (c * Real.exp (ζ * t / 2)) * Real.exp (ζ * t / 2) :=
          mul_le_mul_of_nonneg_right hcE hE_pos.le
      _ = c * Real.exp (ζ * t) := by
          rw [hexp2]
          ring
  calc Real.exp (-(c * Real.exp (ζ * t) / (1 + t) ^ 2)) ≤ Real.exp (-Real.log 2) :=
        Real.exp_le_exp.2 (by linarith)
    _ = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num

#print axioms MatedCRT.AmplCutoff.amplification_cutoff

end AmplCutoff

end MatedCRT
