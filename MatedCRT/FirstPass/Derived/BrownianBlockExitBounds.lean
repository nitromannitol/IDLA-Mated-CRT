import MatedCRT.FirstPass.Derived.BrownianHarmonicMeasureContinuity

/-!
# Harmonic measure bounds for the exit of a square block

Quantitative bounds on the exit distribution of planar Brownian motion from a bounded open set,
used in the chaining step of the proof of Theorem 3.10 of the Gwynne-Miller-Sheffield invariance
principle (convergence of the walk on the cells to Brownian motion, uniformly in the start).

* **Half-plane comparison.** If the bounded open set `U` lies in the closed half-plane
  `{x | ⟪x - p, n⟫ ≤ 0}` (`‖n‖ = 1`), then Brownian motion from `y ∈ U` leaves `U` in the ball
  `B_r(p)` with probability at most `9 r / (r + ⟪p - y, n⟫)`. The proof compares the indicator of
  the ball with the Poisson kernel `x ↦ Re (n / (ξ - x))` of the shifted half-plane
  `{⟪x - ξ, n⟫ < 0}`, `ξ = p + r n`, a bounded harmonic function on `U`, through the
  optional-stopping identity `q(y) = E_y[q(B_{τ_U})]`.
* **Lipschitz bound in the base point.** If `closedBall y ρ ⊆ U`, then for every `b` and every
  Borel set `A`, `|P_y(B_{τ_U} ∈ A) - P_b(B_{τ_U} ∈ A)| ≤ 12 |b - y| / ρ`. The proof bounds the
  circle average of `|P(y, y, ·) - P(y, b, ·)|` (Poisson kernel of the disc `B_ρ(y)`) pointwise.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric InnerProductSpace
open scoped ENNReal NNReal Topology ComplexConjugate
open HarmonicBalls HarmonicBalls.Section6

namespace MatedCRT

namespace BlockExit

/-! ## The projection onto a closed half-plane -/

/-- The nearest-point projection of `x` onto the closed half-plane `{z | ⟪z - p, n⟫ ≤ 0}`
(for a unit vector `n`). -/
noncomputable def halfPlaneProj (p n x : ℂ) : ℂ :=
  x - (max 0 ⟪x - p, n⟫_ℝ) • n

theorem continuous_halfPlaneProj (p n : ℂ) : Continuous (halfPlaneProj p n) := by
  unfold halfPlaneProj
  fun_prop

theorem halfPlaneProj_of_inner_nonpos {p n x : ℂ} (h : ⟪x - p, n⟫_ℝ ≤ 0) :
    halfPlaneProj p n x = x := by
  rw [halfPlaneProj, max_eq_left h, zero_smul, sub_zero]

theorem inner_halfPlaneProj_sub {p n : ℂ} (hn : ‖n‖ = 1) (x : ℂ) :
    ⟪halfPlaneProj p n x - p, n⟫_ℝ = min ⟪x - p, n⟫_ℝ 0 := by
  have hnn : ⟪n, n⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
  have : halfPlaneProj p n x - p = (x - p) - (max 0 ⟪x - p, n⟫_ℝ) • n := by
    simp only [halfPlaneProj]; abel
  rw [this, inner_sub_left, real_inner_smul_left, hnn, mul_one]
  rcases le_total ⟪x - p, n⟫_ℝ 0 with h | h
  · rw [max_eq_left h, min_eq_left h, sub_zero]
  · rw [max_eq_right h, min_eq_right h, sub_self]

theorem norm_sub_halfPlaneProj_le {p n : ℂ} (hn : ‖n‖ = 1) (x : ℂ) :
    ‖x - halfPlaneProj p n x‖ ≤ ‖x - p‖ := by
  have : x - halfPlaneProj p n x = (max 0 ⟪x - p, n⟫_ℝ) • n := by
    simp only [halfPlaneProj]; abel
  rw [this, norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
  refine max_le (norm_nonneg _) ?_
  have := real_inner_le_norm (x - p) n
  rwa [hn, mul_one] at this

/-! ## The shifted half-plane Poisson kernel -/

/-- The real part of `n / w` is `⟪w, n⟫ / ‖w‖²`. -/
theorem re_div_eq_inner_div_sq (n w : ℂ) : (n / w).re = ⟪w, n⟫_ℝ / ‖w‖ ^ 2 := by
  rw [Complex.inner, Complex.div_re, Complex.sq_norm, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  ring

/-- If `⟪w, n⟫ > 0` for a unit vector `n`, then `⟪w, n⟫ / ‖w‖² ≤ 1 / ⟪w, n⟫`. -/
theorem inner_div_sq_le {n w : ℂ} (hn : ‖n‖ = 1) (hw : 0 < ⟪w, n⟫_ℝ) :
    ⟪w, n⟫_ℝ / ‖w‖ ^ 2 ≤ 1 / ⟪w, n⟫_ℝ := by
  have hle : ⟪w, n⟫_ℝ ≤ ‖w‖ := by
    have := real_inner_le_norm w n
    rwa [hn, mul_one] at this
  have hw' : 0 < ‖w‖ := hw.trans_le hle
  rw [div_le_div_iff₀ (by positivity) hw]
  nlinarith

/-- The comparison function: the shifted half-plane Poisson kernel `Re (n / (ξ - x))`,
`ξ = p + r n`, composed with the projection onto the closed half-plane `⟪x - p, n⟫ ≤ 0`. -/
noncomputable def halfPlaneComparison (p n : ℂ) (r : ℝ) (x : ℂ) : ℝ :=
  (n / ((p + r • n) - halfPlaneProj p n x)).re

theorem le_inner_halfPlaneComparison_denom {p n : ℂ} (hn : ‖n‖ = 1) (r : ℝ) (x : ℂ) :
    r ≤ ⟪(p + r • n) - halfPlaneProj p n x, n⟫_ℝ := by
  have hnn : ⟪n, n⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
  have : (p + r • n) - halfPlaneProj p n x = r • n - (halfPlaneProj p n x - p) := by abel
  rw [this, inner_sub_left, real_inner_smul_left, hnn, mul_one, inner_halfPlaneProj_sub hn]
  linarith [min_le_right ⟪x - p, n⟫_ℝ 0]

theorem halfPlaneComparison_denom_ne_zero {p n : ℂ} (hn : ‖n‖ = 1) {r : ℝ} (hr : 0 < r)
    (x : ℂ) : (p + r • n) - halfPlaneProj p n x ≠ 0 := by
  intro h
  have := le_inner_halfPlaneComparison_denom (p := p) hn r x
  rw [h, inner_zero_left] at this
  linarith

theorem continuous_halfPlaneComparison {p n : ℂ} (hn : ‖n‖ = 1) {r : ℝ} (hr : 0 < r) :
    Continuous (halfPlaneComparison p n r) := by
  unfold halfPlaneComparison
  exact Complex.continuous_re.comp (continuous_const.div
    (continuous_const.sub (continuous_halfPlaneProj p n))
    (halfPlaneComparison_denom_ne_zero hn hr))

theorem halfPlaneComparison_eq {p n : ℂ} (r : ℝ) (x : ℂ) :
    halfPlaneComparison p n r x = ⟪(p + r • n) - halfPlaneProj p n x, n⟫_ℝ /
      ‖(p + r • n) - halfPlaneProj p n x‖ ^ 2 := by
  rw [halfPlaneComparison, re_div_eq_inner_div_sq]

theorem halfPlaneComparison_nonneg {p n : ℂ} (hn : ‖n‖ = 1) {r : ℝ} (hr : 0 < r) (x : ℂ) :
    0 ≤ halfPlaneComparison p n r x := by
  rw [halfPlaneComparison_eq]
  exact div_nonneg (hr.le.trans (le_inner_halfPlaneComparison_denom hn r x)) (sq_nonneg _)

theorem halfPlaneComparison_le {p n : ℂ} (hn : ‖n‖ = 1) {r : ℝ} (hr : 0 < r) (x : ℂ) :
    halfPlaneComparison p n r x ≤ 1 / ⟪(p + r • n) - halfPlaneProj p n x, n⟫_ℝ := by
  rw [halfPlaneComparison_eq]
  exact inner_div_sq_le hn (hr.trans_le (le_inner_halfPlaneComparison_denom hn r x))

theorem abs_halfPlaneComparison_le {p n : ℂ} (hn : ‖n‖ = 1) {r : ℝ} (hr : 0 < r) (x : ℂ) :
    ‖halfPlaneComparison p n r x‖ ≤ 1 / r := by
  rw [Real.norm_eq_abs, abs_of_nonneg (halfPlaneComparison_nonneg hn hr x)]
  refine (halfPlaneComparison_le hn hr x).trans ?_
  exact one_div_le_one_div_of_le hr (le_inner_halfPlaneComparison_denom hn r x)

/-- On the ball `B_r(p)` the comparison function is at least `1 / (9 r)`. -/
theorem one_le_mul_halfPlaneComparison {p n : ℂ} (hn : ‖n‖ = 1) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ ball p r) : 1 ≤ 9 * r * halfPlaneComparison p n r z := by
  set w := (p + r • n) - halfPlaneProj p n z with hw
  have hzp : ‖z - p‖ < r := by rwa [mem_ball, dist_eq_norm] at hz
  have hwn : r ≤ ⟪w, n⟫_ℝ := le_inner_halfPlaneComparison_denom hn r z
  have hwle : ‖w‖ < 3 * r := by
    have h1 : w = r • n + (p - z) + (z - halfPlaneProj p n z) := by rw [hw]; abel
    rw [h1]
    have h2 : ‖r • n‖ = r := by rw [norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos hr]
    have h3 : ‖p - z‖ = ‖z - p‖ := norm_sub_rev _ _
    have h4 := norm_sub_halfPlaneProj_le (p := p) hn z
    calc ‖r • n + (p - z) + (z - halfPlaneProj p n z)‖
        ≤ ‖r • n‖ + ‖p - z‖ + ‖z - halfPlaneProj p n z‖ := norm_add₃_le
      _ < 3 * r := by linarith
  have hw0 : 0 < ‖w‖ := (hr.trans_le hwn).trans_le (by
    have := real_inner_le_norm w n
    rwa [hn, mul_one] at this)
  rw [halfPlaneComparison_eq]
  change 1 ≤ 9 * r * (⟪w, n⟫_ℝ / ‖w‖ ^ 2)
  rw [mul_div_assoc', le_div_iff₀ (pow_pos hw0 2), one_mul]
  nlinarith [norm_nonneg w]

/-- The comparison function is harmonic on every open set inside the closed half-plane. -/
theorem harmonicOnNhd_halfPlaneComparison {U : Set ℂ} (hU : IsOpen U) {p n : ℂ}
    (hn : ‖n‖ = 1) {r : ℝ} (hr : 0 < r) (hUH : ∀ x ∈ U, ⟪x - p, n⟫_ℝ ≤ 0) :
    HarmonicOnNhd (halfPlaneComparison p n r) U := by
  intro x hx
  have heq : halfPlaneComparison p n r =ᶠ[𝓝 x] fun z => (n / ((p + r • n) - z)).re := by
    filter_upwards [hU.mem_nhds hx] with z hz
    rw [halfPlaneComparison, halfPlaneProj_of_inner_nonpos (hUH z hz)]
  refine (harmonicAt_congr_nhds heq).2 ?_
  have hne : (p + r • n) - x ≠ 0 := by
    have := halfPlaneComparison_denom_ne_zero (p := p) hn hr x
    rwa [halfPlaneProj_of_inner_nonpos (hUH x hx)] at this
  exact (analyticAt_const.div (analyticAt_const.sub analyticAt_id) hne).harmonicAt_re

/-! ## Half-plane comparison for the exit point -/

/-- **Half-plane comparison.** Let `U` be a bounded open set inside the closed half-plane
`{x | ⟪x - p, n⟫ ≤ 0}`, `‖n‖ = 1`, and `y ∈ U`. Brownian motion from `y` leaves `U` in the ball
`B_r(p)` with probability at most `9 r / (r + ⟪p - y, n⟫)`. -/
theorem planarBrownian_exitPoint_mem_ball_le {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {p n y : ℂ} (hn : ‖n‖ = 1)
    (hUH : ∀ x ∈ U, ⟪x - p, n⟫_ℝ ≤ 0) (hy : y ∈ U) {r : ℝ} (hr : 0 < r) :
    planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ ball p r} ≤
      ENNReal.ofReal (9 * r / (r + ⟪p - y, n⟫_ℝ)) := by
  set q := halfPlaneComparison p n r with hq
  have hmU : Measurable (fun ω : ContinuousPath ℂ =>
      ω ((ContinuousPath.exitTime U ω).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime U) (ContinuousPath.isStoppingTime_exitTime U hU)
  have hqc : Continuous q := continuous_halfPlaneComparison hn hr
  have hqm : Measurable (fun ω : ContinuousPath ℂ =>
      q (ω ((ContinuousPath.exitTime U ω).toNNReal))) := hqc.measurable.comp hmU
  have hint : Integrable (fun ω : ContinuousPath ℂ =>
      9 * r * q (ω ((ContinuousPath.exitTime U ω).toNNReal))) (planarBrownianMotion y) := by
    refine (Integrable.of_bound hqm.aestronglyMeasurable (1 / r)
      (Eventually.of_forall fun ω => abs_halfPlaneComparison_le hn hr _)).const_mul (9 * r)
  have he := harmonic_eq_integral_planarBrownian_exitTime hU hUb hqc
    (harmonicOnNhd_halfPlaneComparison hU hn hr hUH) (abs_halfPlaneComparison_le hn hr) hy
  have hE : MeasurableSet {ω : ContinuousPath ℂ |
      ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ ball p r} := hmU isOpen_ball.measurableSet
  calc planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ ball p r}
      = ∫⁻ ω, Set.indicator {ω : ContinuousPath ℂ |
          ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ ball p r} 1 ω
            ∂(planarBrownianMotion y) := (lintegral_indicator_one hE).symm
    _ ≤ ∫⁻ ω, ENNReal.ofReal (9 * r * q (ω ((ContinuousPath.exitTime U ω).toNNReal)))
          ∂(planarBrownianMotion y) := by
        refine lintegral_mono fun ω => ?_
        by_cases hω : ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ ball p r
        · rw [Set.indicator_of_mem (show ω ∈ {ω : ContinuousPath ℂ |
            ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ ball p r} from hω), Pi.one_apply,
            ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (one_le_mul_halfPlaneComparison hn hr hω)
        · rw [Set.indicator_of_notMem (show ω ∉ {ω : ContinuousPath ℂ |
            ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ ball p r} from hω)]
          simp
    _ = ENNReal.ofReal (∫ ω, 9 * r * q (ω ((ContinuousPath.exitTime U ω).toNNReal))
          ∂(planarBrownianMotion y)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω =>
          mul_nonneg (by positivity) (halfPlaneComparison_nonneg hn hr _))]
    _ = ENNReal.ofReal (9 * r * q y) := by rw [integral_const_mul, ← he]
    _ ≤ ENNReal.ofReal (9 * r / (r + ⟪p - y, n⟫_ℝ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hqy := halfPlaneComparison_le (p := p) hn hr y
        rw [halfPlaneProj_of_inner_nonpos (hUH y hy)] at hqy
        have hden : ⟪(p + r • n) - y, n⟫_ℝ = r + ⟪p - y, n⟫_ℝ := by
          have hnn : ⟪n, n⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
          rw [show (p + r • n) - y = r • n + (p - y) by abel, inner_add_left,
            real_inner_smul_left, hnn, mul_one]
        rw [hden] at hqy
        calc 9 * r * q y ≤ 9 * r * (1 / (r + ⟪p - y, n⟫_ℝ)) :=
              mul_le_mul_of_nonneg_left hqy (by positivity)
          _ = 9 * r / (r + ⟪p - y, n⟫_ℝ) := by rw [mul_one_div]

/-! ## Lipschitz bound for harmonic measure in the base point -/

/-- Pointwise bound on the Poisson kernel of the disc `B_ρ(y)` against its value `1` at the
centre: for `‖b - y‖ ≤ ρ / 2` and `ζ` on the circle, `|P(y, y, ζ) - P(y, b, ζ)| ≤ 12 ‖b - y‖ / ρ`. -/
theorem abs_poissonKernel_center_sub_le {y b ζ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hζ : ‖ζ - y‖ = ρ) (hb : ‖b - y‖ ≤ ρ / 2) :
    |poissonKernel y y ζ - poissonKernel y b ζ| ≤ 12 * ‖b - y‖ / ρ := by
  set t := ‖b - y‖ with ht
  set D := ‖ζ - b‖ with hDdef
  have ht0 : 0 ≤ t := norm_nonneg _
  have hDlo : ρ - t ≤ D := by
    have := norm_sub_norm_le (ζ - y) (b - y)
    rw [hζ, sub_sub_sub_cancel_right] at this
    linarith
  have hDhi : D ≤ ρ + t := by
    have := norm_sub_le (ζ - y) (b - y)
    rw [hζ, sub_sub_sub_cancel_right] at this
    linarith
  have hD0 : 0 < D := by linarith
  have h1 : poissonKernel y y ζ = 1 := by
    rw [poissonKernel_def, sub_self, norm_zero, sub_zero, hζ]
    field_simp
    simp
  have h2 : poissonKernel y b ζ = (ρ ^ 2 - t ^ 2) / D ^ 2 := by
    rw [poissonKernel_def, hζ, sub_sub_sub_cancel_right]
  rw [h1, h2, show (1 : ℝ) - (ρ ^ 2 - t ^ 2) / D ^ 2 = (D ^ 2 - (ρ ^ 2 - t ^ 2)) / D ^ 2 by
    field_simp, abs_div, abs_of_pos (by positivity : (0 : ℝ) < D ^ 2),
    div_le_div_iff₀ (by positivity) hρ]
  have hsq1 : D ^ 2 ≤ (ρ + t) ^ 2 := pow_le_pow_left₀ hD0.le hDhi 2
  have hsq2 : (ρ - t) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (by linarith) hDlo 2
  have hsq3 : ρ ^ 2 / 4 ≤ D ^ 2 := by nlinarith
  have k1 := mul_le_mul_of_nonneg_left hsq1 hρ.le
  have k2 := mul_le_mul_of_nonneg_left hsq2 hρ.le
  have k3 := mul_le_mul_of_nonneg_left hsq3 ht0
  have k4 := mul_le_mul_of_nonneg_left hb (mul_nonneg hρ.le ht0)
  rcases abs_cases (D ^ 2 - (ρ ^ 2 - t ^ 2)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
    nlinarith [mul_nonneg (mul_nonneg ht0 ht0) hρ.le]

/-- **Lipschitz bound for harmonic measure in the base point.** For a bounded open `U` with
`closedBall y ρ ⊆ U`, every base point `b` and every Borel set `A`,
`|P_y(B_{τ_U} ∈ A) - P_b(B_{τ_U} ∈ A)| ≤ 12 |b - y| / ρ`. -/
theorem abs_planarBrownian_exitPoint_sub_le_dist {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {y : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hsub : closedBall y ρ ⊆ U)
    (b : ℂ) {A : Set ℂ} (hA : MeasurableSet A) :
    |(planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A}).toReal -
      (planarBrownianMotion b {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A}).toReal| ≤
      12 * dist b y / ρ := by
  by_cases ht : dist b y ≤ ρ / 2
  · have hb : b ∈ ball y ρ := mem_ball.2 (by linarith)
    refine (abs_planarBrownian_exitPoint_sub_le hU hUb hsub (mem_ball_self hρ) hb hA).trans ?_
    by_cases hci : CircleIntegrable
        (fun ζ => |poissonKernel y y ζ - poissonKernel y b ζ|) y ρ
    · refine Real.circleAverage_mono_on_of_le_circle hci fun ζ hζ => ?_
      rw [abs_of_pos hρ, mem_sphere, dist_eq_norm] at hζ
      rw [dist_eq_norm] at ht ⊢
      exact abs_poissonKernel_center_sub_le hρ hζ ht
    · rw [Real.circleAverage.integral_undef hci]
      positivity
  · have h1 : ∀ z : ℂ, (planarBrownianMotion z
        {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A}).toReal ∈ Set.Icc (0 : ℝ) 1 :=
      fun z => ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by rw [ENNReal.ofReal_one]; exact prob_le_one)⟩
    have hy1 := h1 y
    have hb1 := h1 b
    have : (6 : ℝ) ≤ 12 * dist b y / ρ := by
      rw [le_div_iff₀ hρ]
      linarith
    rw [abs_le]
    constructor <;> linarith [hy1.1, hy1.2, hb1.1, hb1.2]

/-- One-sided form of the Lipschitz bound, as an inequality of measures. -/
theorem planarBrownian_exitPoint_le_add_dist {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {y : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hsub : closedBall y ρ ⊆ U)
    (b : ℂ) {A : Set ℂ} (hA : MeasurableSet A) :
    planarBrownianMotion b {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A} ≤
        planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A} +
          ENNReal.ofReal (12 * dist b y / ρ) ∧
      planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A} ≤
        planarBrownianMotion b {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A} +
          ENNReal.ofReal (12 * dist b y / ρ) := by
  have h := abs_planarBrownian_exitPoint_sub_le_dist hU hUb hρ hsub b hA
  rw [abs_le] at h
  have hC : 0 ≤ 12 * dist b y / ρ := by positivity
  constructor
  · rw [← ENNReal.ofReal_toReal (measure_ne_top (planarBrownianMotion b) _),
      ← ENNReal.ofReal_toReal (measure_ne_top (planarBrownianMotion y) _),
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg hC]
    exact ENNReal.ofReal_le_ofReal (by linarith [h.1])
  · rw [← ENNReal.ofReal_toReal (measure_ne_top (planarBrownianMotion b) _),
      ← ENNReal.ofReal_toReal (measure_ne_top (planarBrownianMotion y) _),
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg hC]
    exact ENNReal.ofReal_le_ofReal (by linarith [h.2])

end BlockExit

end MatedCRT
