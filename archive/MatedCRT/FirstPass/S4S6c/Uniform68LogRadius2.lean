import MatedCRT.FirstPass.S4S6c.Uniform68LogRadius

/-!
# The logarithmic relation with a dyadic loss

The walk radius `δ` of the uniform statement is the dyadic number below `(r · r^ζ)²` (`Uniform68Params.dyadicBelow_bounds`),
so `(r · r^ζ)²/2 ≤ δ ≤ R` only, and the relation of `Uniform68LogRadius.logRadius_le_of_delta` loses a factor `2`:
`1 + log(1/R) ≤ (3 + 2ζ + log 2)(1 + log(1/r))` when `(r · r^ζ)²/2 ≤ R`, `0 < r ≤ 1`, `ζ ≥ 0`.
-/

open Real

namespace MatedCRT.Uniform68LogRadius2

/-- `1 + log(1/R) ≤ (3 + 2ζ + log 2)(1 + log(1/r))` when `(r · r^ζ)²/2 ≤ R`. -/
theorem logRadius_le_of_half_delta {R r ζ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hζ : 0 ≤ ζ)
    (hδ : (r * r ^ ζ) ^ 2 / 2 ≤ R) :
    1 + Real.log (1 / R) ≤ (3 + 2 * ζ + Real.log 2) * (1 + Real.log (1 / r)) := by
  have hrζ : 0 < r ^ ζ := Real.rpow_pos_of_pos hr ζ
  have hX : 0 < (r * r ^ ζ) ^ 2 := by positivity
  have hR : 0 < R := lt_of_lt_of_le (by positivity) hδ
  have hL : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log ((r * r ^ ζ) ^ 2) = -((2 + 2 * ζ) * Real.log (1 / r)) := by
    rw [Real.log_pow, Real.log_mul hr.ne' hrζ.ne', Real.log_rpow hr, one_div, Real.log_inv]
    push_cast
    ring
  have hlogR : Real.log ((r * r ^ ζ) ^ 2 / 2) ≤ Real.log R := Real.log_le_log (by positivity) hδ
  have hsplit : Real.log ((r * r ^ ζ) ^ 2 / 2) = Real.log ((r * r ^ ζ) ^ 2) - Real.log 2 :=
    Real.log_div hX.ne' (by norm_num)
  have hinv : Real.log (1 / R) = -Real.log R := by rw [one_div, Real.log_inv]
  have hexp : (3 + 2 * ζ + Real.log 2) * (1 + Real.log (1 / r))
      = (3 + 2 * ζ + Real.log 2) + (3 + 2 * ζ + Real.log 2) * Real.log (1 / r) := by ring
  have hmul : (2 + 2 * ζ) * Real.log (1 / r) ≤ (3 + 2 * ζ + Real.log 2) * Real.log (1 / r) := by
    have : 0 ≤ (1 + Real.log 2) * Real.log (1 / r) := mul_nonneg (by linarith) hL
    nlinarith
  rw [hinv, hexp]
  rw [hsplit, hlog1] at hlogR
  linarith

end MatedCRT.Uniform68LogRadius2

/-! ## Audit -/

#print axioms MatedCRT.Uniform68LogRadius2.logRadius_le_of_half_delta
