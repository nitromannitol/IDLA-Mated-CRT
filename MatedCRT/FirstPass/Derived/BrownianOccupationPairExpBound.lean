import MatedCRT.FirstPass.Derived.BrownianOccupationPairSmallBall

/-!
# Exponential form of the two-point bound for the occupation measure of killed planar Brownian motion

The two-point bound `lintegral_occupation_prod_norm_sub_lt_le` controls
`E_y[(μ_τ ⊗ μ_τ){‖b u - b v‖ < a}]` by the time integral of
`(q ^ (⌊max u v⌋₊ - 1)) ^ θ · (a ² / |u - v|) ^ (1 - θ)`, with `q = unitIncrementStayProb r < 1`. Here the
integrand is bounded by an exponentially damped Riesz kernel: with `q' = max (q, 1/2) ∈ (0, 1)`,
`c = -θ log q' > 0` and `K = q' ^ (-2θ)`,

`(q ^ (⌊t⌋₊ - 1)) ^ θ ≤ K e ^ (-c t)`  and  `(a ² / d) ^ (1 - θ) = a ^ (2 (1 - θ)) d ^ (θ - 1)`,

so that, for `0 < θ ≤ 1` and `a ≥ 0`,

`E_y[(μ_τ ⊗ μ_τ){‖b u - b v‖ < a}] ≤ K a ^ (2 (1 - θ)) ∫∫ e ^ (-c max (u, v)) |u - v| ^ (θ - 1) du dv`.

The constants depend on `r` and `θ` only.

* `stayRate`, `stayDecay`, `stayConst`: the constants `q'`, `c`, `K`; `stayDecay_pos`, `stayConst_pos`.
* `pow_floor_sub_one_rpow_le`: the exponential bound of the exit-time factor.
* `ofReal_sq_div_rpow_eq`: the factorization of the small-ball factor.
* `lintegral_occupation_prod_norm_sub_lt_le_exp`: the bound above.
-/

open MeasureTheory Set Metric MarkovProcess ProbabilityTheory HarmonicBalls HarmonicBalls.Section6
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The rate `q' = max (q, 1/2)` with `q = unitIncrementStayProb r`; it lies in `(0, 1)`. -/
noncomputable def stayRate (r : ℝ) : ℝ := max (unitIncrementStayProb r).toReal (1 / 2)

/-- The decay rate `c = -θ log q'` of the exit-time factor. -/
noncomputable def stayDecay (r θ : ℝ) : ℝ := -(θ * Real.log (stayRate r))

/-- The constant `K = q' ^ (-2θ) = e ^ (-2θ log q')` of the exit-time factor. -/
noncomputable def stayConst (r θ : ℝ) : ℝ := Real.exp (-2 * θ * Real.log (stayRate r))

theorem stayRate_pos (r : ℝ) : 0 < stayRate r :=
  lt_of_lt_of_le (by norm_num) (le_max_right _ _)

theorem stayRate_lt_one (r : ℝ) : stayRate r < 1 := by
  refine max_lt ?_ (by norm_num)
  have h := unitIncrementStayProb_lt_one r
  rw [← ENNReal.ofReal_one] at h
  exact ENNReal.toReal_lt_of_lt_ofReal h

theorem unitIncrementStayProb_le_ofReal_stayRate (r : ℝ) :
    unitIncrementStayProb r ≤ ENNReal.ofReal (stayRate r) :=
  calc unitIncrementStayProb r = ENNReal.ofReal (unitIncrementStayProb r).toReal :=
        (ENNReal.ofReal_toReal (ne_top_of_lt (unitIncrementStayProb_lt_one r))).symm
    _ ≤ ENNReal.ofReal (stayRate r) := ENNReal.ofReal_le_ofReal (le_max_left _ _)

theorem stayDecay_pos (r : ℝ) {θ : ℝ} (hθ0 : 0 < θ) : 0 < stayDecay r θ :=
  neg_pos.2 (mul_neg_of_pos_of_neg hθ0 (Real.log_neg (stayRate_pos r) (stayRate_lt_one r)))

theorem stayConst_pos (r θ : ℝ) : 0 < stayConst r θ :=
  Real.exp_pos _

/-- **Exponential bound of the exit-time factor.** For `θ > 0` and `t ≥ 0`,
`(q ^ (⌊t⌋₊ - 1)) ^ θ ≤ K e ^ (-c t)`, with `q = unitIncrementStayProb r`, `K = stayConst r θ` and
`c = stayDecay r θ`. -/
theorem pow_floor_sub_one_rpow_le (r : ℝ) {θ : ℝ} (hθ0 : 0 < θ) (t : ℝ≥0) :
    (unitIncrementStayProb r ^ (⌊t⌋₊ - 1)) ^ θ ≤
      ENNReal.ofReal (stayConst r θ * Real.exp (-stayDecay r θ * t)) := by
  have hq0 := stayRate_pos r
  have hq1 := (stayRate_lt_one r).le
  have hn : (t : ℝ) - 2 ≤ ((⌊t⌋₊ - 1 : ℕ) : ℝ) := by
    have h1 : ⌊t⌋₊ ≤ (⌊t⌋₊ - 1) + 1 := by omega
    have h2 : (⌊t⌋₊ : ℝ) ≤ ((⌊t⌋₊ - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    have h3 : (t : ℝ) < (⌊t⌋₊ : ℝ) + 1 := by
      have := Nat.lt_floor_add_one t
      exact_mod_cast this
    linarith
  calc (unitIncrementStayProb r ^ (⌊t⌋₊ - 1)) ^ θ
      ≤ (ENNReal.ofReal (stayRate r) ^ (⌊t⌋₊ - 1)) ^ θ :=
        ENNReal.rpow_le_rpow
          (pow_le_pow_left₀ zero_le (unitIncrementStayProb_le_ofReal_stayRate r) _) hθ0.le
    _ = ENNReal.ofReal ((stayRate r ^ (⌊t⌋₊ - 1)) ^ θ) := by
        rw [← ENNReal.ofReal_pow hq0.le, ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hq0.le _) hθ0.le]
    _ ≤ ENNReal.ofReal (stayConst r θ * Real.exp (-stayDecay r θ * t)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
        have hle : θ * ((t : ℝ) - 2) ≤ ((⌊t⌋₊ - 1 : ℕ) : ℝ) * θ := by
          have := mul_le_mul_of_nonneg_left hn hθ0.le
          linarith
        calc stayRate r ^ (((⌊t⌋₊ - 1 : ℕ) : ℝ) * θ) ≤ stayRate r ^ (θ * ((t : ℝ) - 2)) :=
              Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hle
          _ = stayConst r θ * Real.exp (-stayDecay r θ * t) := by
              rw [Real.rpow_def_of_pos hq0, stayConst, stayDecay, ← Real.exp_add]
              congr 1
              ring

/-- **Factorization of the small-ball factor.** For `a, d ≥ 0` and `θ ≤ 1`,
`(a ² / d) ^ (1 - θ) = a ^ (2 (1 - θ)) d ^ (θ - 1)`. -/
theorem ofReal_sq_div_rpow_eq {a d θ : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hθ1 : θ ≤ 1) :
    ENNReal.ofReal (a ^ 2 / d) ^ (1 - θ) = ENNReal.ofReal (a ^ (2 * (1 - θ)) * d ^ (θ - 1)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (div_nonneg (sq_nonneg a) hd) (sub_nonneg.2 hθ1),
    Real.div_rpow (sq_nonneg a) hd, ← Real.rpow_two, ← Real.rpow_mul ha, div_eq_mul_inv,
    ← Real.rpow_neg hd, neg_sub]

/-- The integrand of the two-point bound is at most `K a ^ (2 (1 - θ))` times the exponentially
damped Riesz kernel `e ^ (-c max (u, v)) |u - v| ^ (θ - 1)`. -/
theorem twoTime_bound_le (r : ℝ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {a : ℝ} (ha : 0 ≤ a)
    (u v : ℝ≥0) :
    (unitIncrementStayProb r ^ (⌊max u v⌋₊ - 1)) ^ θ *
        ENNReal.ofReal (a ^ 2 / |(u : ℝ) - v|) ^ (1 - θ) ≤
      ENNReal.ofReal (stayConst r θ * a ^ (2 * (1 - θ))) *
        ENNReal.ofReal (Real.exp (-stayDecay r θ * max (u : ℝ) v) * |(u : ℝ) - v| ^ (θ - 1)) := by
  have hd : 0 ≤ |(u : ℝ) - v| := abs_nonneg _
  calc (unitIncrementStayProb r ^ (⌊max u v⌋₊ - 1)) ^ θ *
        ENNReal.ofReal (a ^ 2 / |(u : ℝ) - v|) ^ (1 - θ)
      ≤ ENNReal.ofReal (stayConst r θ * Real.exp (-stayDecay r θ * ((max u v : ℝ≥0) : ℝ))) *
          ENNReal.ofReal (a ^ (2 * (1 - θ)) * |(u : ℝ) - v| ^ (θ - 1)) := by
        rw [ofReal_sq_div_rpow_eq ha hd hθ1]
        gcongr ?_ * _
        exact pow_floor_sub_one_rpow_le r hθ0 _
    _ = ENNReal.ofReal (stayConst r θ * a ^ (2 * (1 - θ))) *
        ENNReal.ofReal (Real.exp (-stayDecay r θ * max (u : ℝ) v) * |(u : ℝ) - v| ^ (θ - 1)) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (stayConst_pos r θ).le (Real.exp_pos _).le),
          ← ENNReal.ofReal_mul (mul_nonneg (stayConst_pos r θ).le (Real.rpow_nonneg ha _)),
          NNReal.coe_max]
        congr 1
        ring

/-- **Two-point bound for the occupation measure of killed planar Brownian motion, exponential form.**
For `0 < θ ≤ 1` and `a ≥ 0`, with `τ = exitNN z r b`,
`E_y[(lebNN|[0, τ] ⊗ lebNN|[0, τ]){‖b u - b v‖ < a}]` is at most
`K a ^ (2 (1 - θ)) ∫∫ e ^ (-c max (u, v)) |u - v| ^ (θ - 1) d(lebNN ⊗ lebNN)`, with `K = stayConst r θ` and
`c = stayDecay r θ > 0`. -/
theorem lintegral_occupation_prod_norm_sub_lt_le_exp (z y : ℂ) (r : ℝ) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ b, ((lebNN.restrict (Icc 0 (exitNN z r b))).prod (lebNN.restrict (Icc 0 (exitNN z r b))))
        {p : ℝ≥0 × ℝ≥0 | ‖b p.1 - b p.2‖ < a} ∂planarBrownianMotion y ≤
      ENNReal.ofReal (stayConst r θ * a ^ (2 * (1 - θ))) *
        ∫⁻ p : ℝ≥0 × ℝ≥0, ENNReal.ofReal (Real.exp (-stayDecay r θ * max (p.1 : ℝ) p.2) *
          |(p.1 : ℝ) - p.2| ^ (θ - 1)) ∂(lebNN.prod lebNN) := by
  refine (lintegral_occupation_prod_norm_sub_lt_le z y r ha hθ0.le hθ1).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun p => twoTime_bound_le r hθ0 hθ1 ha p.1 p.2

end MatedCRT.KilledOccupation
