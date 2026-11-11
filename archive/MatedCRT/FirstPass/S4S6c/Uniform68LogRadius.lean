import MatedCRT.FirstPass.S4S6c.Uniform68Radius

/-!
# The logarithmic parameter relation `hLR` of the local test

With the test radius `R` and the walk scale `r` satisfying `δ(r) := (r · r^ζ)² ≤ R` (the lower bound of the selected
radius, `Uniform68Radius.radiusAt_good` and `Uniform68Params.trace_numerics`), the logarithmic relation of
`Uniform68Events.hloc_point`, `1 + log(1/R) ≤ K_L (1 + log(1/r))`, holds with `K_L = 2 + 2ζ`.

Terminology: Lemma 6.8 scale bookkeeping; Armitage-Gardiner logarithmic potential.
-/

open Real

namespace MatedCRT.Uniform68LogRadius

/-- `1 + log(1/R) ≤ (2 + 2ζ)(1 + log(1/r))` when `(r · r^ζ)² ≤ R`, `0 < r ≤ 1`, `ζ ≥ 0`. -/
theorem logRadius_le_of_delta {R r ζ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hζ : 0 ≤ ζ)
    (hδ : (r * r ^ ζ) ^ 2 ≤ R) : 1 + Real.log (1 / R) ≤ (2 + 2 * ζ) * (1 + Real.log (1 / r)) := by
  have hrζ : 0 < r ^ ζ := Real.rpow_pos_of_pos hr ζ
  have hL : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have hlog1 : Real.log ((r * r ^ ζ) ^ 2) = -((2 + 2 * ζ) * Real.log (1 / r)) := by
    rw [Real.log_pow, Real.log_mul hr.ne' hrζ.ne', Real.log_rpow hr, one_div, Real.log_inv]
    push_cast
    ring
  have hlogR : Real.log ((r * r ^ ζ) ^ 2) ≤ Real.log R := Real.log_le_log (by positivity) hδ
  have hinv : Real.log (1 / R) = -Real.log R := by rw [one_div, Real.log_inv]
  have hexp : (2 + 2 * ζ) * (1 + Real.log (1 / r)) = (2 + 2 * ζ) + (2 + 2 * ζ) * Real.log (1 / r) := by ring
  rw [hinv, hexp]
  rw [hlog1] at hlogR
  linarith

end MatedCRT.Uniform68LogRadius

/-! ## Audit -/

#print axioms MatedCRT.Uniform68LogRadius.logRadius_le_of_delta
