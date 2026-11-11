import MatedCRT.Proofs.Field.WholePlaneLQGCont

/-!
# The Weyl scaling of the LQG measure under a logarithmic shift (deterministic part)

For a sample `h` of circle averages and `α ∈ ℝ`, let `wShift α h ε x = h ε x - α · avg_{y ∈ ∂B_ε(x)} log|y|`, the
circle averages of `h - α log|·|` (the cone shift of Duplantier-Sheffield 2011, eq:gff, with `α = γ`). By the mean
value property of `log|·|`, `avg_{y ∈ ∂B_ε(x)} log|y| = log|x|` when `ε ≤ |x|`. Hence, away from the origin,
`ε^{γ²/2} e^{γ (h - γ log|·|)_ε(x)} = |x|^{-γ²} ε^{γ²/2} e^{γ h_ε(x)}`: the approximations of the shifted field are the
approximations of `h` weighted by `|x|^{-γ²}` (the Weyl scaling, Duplantier-Sheffield 2011, Proposition 1.2; Fact 2.2(iii)).
This file proves the identity for the approximations and its vague limit on test functions vanishing near `0`.
-/

namespace MatedCRT.Field

open MeasureTheory Filter Topology HarmonicBalls

/-- The circle averages of `h - α log|·|`. -/
noncomputable def wShift (α : ℝ) (h : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun ε x => h ε x - α * Real.circleAverage (fun y => Real.log ‖y‖) x ε

/-- Closed form of the circle average of `log|·|`: `avg_{∂B_ε(x)} log|y| = log ε + log⁺(|x|/ε)`. -/
theorem circleAverage_log_norm_closed (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Real.circleAverage (fun y => Real.log ‖y‖) x ε = Real.log ε + Real.posLog (ε⁻¹ * ‖x‖) := by
  simpa [sub_zero] using circleAverage_log_norm_eq x 0 hε

/-- **Mean value property of `log|·|`**: for `ε ≤ |x|`, `avg_{∂B_ε(x)} log|y| = log|x|`. -/
theorem circleAverage_log_norm_of_le (x : ℂ) {ε : ℝ} (hε : 0 < ε) (hx : ε ≤ ‖x‖) :
    Real.circleAverage (fun y => Real.log ‖y‖) x ε = Real.log ‖x‖ := by
  rw [circleAverage_log_norm_closed x hε]
  have hx0 : ‖x‖ ≠ 0 := (lt_of_lt_of_le hε hx).ne'
  have h1 : 1 ≤ ε⁻¹ * ‖x‖ := by
    rw [← div_eq_inv_mul]
    exact (one_le_div hε).2 hx
  have hpos : Real.posLog (ε⁻¹ * ‖x‖) = Real.log (ε⁻¹ * ‖x‖) := by
    unfold Real.posLog
    exact max_eq_right (Real.log_nonneg h1)
  rw [hpos, Real.log_mul (inv_ne_zero hε.ne') hx0, Real.log_inv]
  ring

/-- The circle averages of the shifted field are continuous in `x` for each positive radius. -/
theorem continuous_wShift_slice (α : ℝ) (h : ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) (hc : Continuous (h ε)) :
    Continuous (wShift α h ε) := by
  have hfun : wShift α h ε = fun x => h ε x - α * (Real.log ε + Real.posLog (ε⁻¹ * ‖x‖)) :=
    funext fun x => by unfold wShift; rw [circleAverage_log_norm_closed x hε]
  rw [hfun]
  exact hc.sub (continuous_const.mul (continuous_const.add
    (Real.continuous_posLog.comp (continuous_const.mul continuous_norm))))

/-- **Weyl scaling, pointwise.** For `ε ≤ |x|`: `ε^{γ²/2} e^{γ (h - γ log|·|)_ε(x)} = |x|^{-γ²} ε^{γ²/2} e^{γ h_ε(x)}`. -/
theorem shift_density (γ : ℝ) (h : ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) (x : ℂ) (hx : ε ≤ ‖x‖) :
    ε ^ (γ ^ 2 / 2) * Real.exp (γ * wShift γ h ε x)
      = ‖x‖ ^ (-γ ^ 2) * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * h ε x)) := by
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le hε hx
  have hpow : ‖x‖ ^ (-γ ^ 2) = Real.exp (-γ ^ 2 * Real.log ‖x‖) := by
    rw [Real.rpow_def_of_pos hx0]
    ring_nf
  unfold wShift
  rw [circleAverage_log_norm_of_le x hε hx, hpow]
  have : γ * (h ε x - γ * Real.log ‖x‖) = γ * h ε x + -γ ^ 2 * Real.log ‖x‖ := by ring
  rw [this, Real.exp_add]
  ring

/-- **Approximation identity under the shift.** For a test function `g` vanishing on the ball of radius `δ` and
`ε < δ`: `∫ g d(lqgApprox γ (wShift γ h) ε) = ∫ (g |·|^{-γ²}) d(lqgApprox γ h ε)`. -/
theorem integral_lqgApprox_shift (γ : ℝ) (h : ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) (hc : Continuous (h ε))
    (g : ℂ → ℝ) (hg : ∀ x, g x ≠ 0 → ε ≤ ‖x‖) :
    ∫ x, g x ∂(lqgApprox γ (wShift γ h) ε) = ∫ x, (g x * ‖x‖ ^ (-γ ^ 2)) ∂(lqgApprox γ h ε) := by
  rw [integral_lqgApprox γ (wShift γ h) hε (continuous_wShift_slice γ h hε hc) g,
    integral_lqgApprox γ h hε hc (fun x => g x * ‖x‖ ^ (-γ ^ 2))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  by_cases hg0 : g x = 0
  · simp [hg0]
  · rw [shift_density γ h hε x (hg x hg0)]
    ring

/-- A function `g` vanishing on `‖x‖ < δ` makes `g |·|^s` continuous. -/
theorem continuous_mul_rpow_of_vanish {g : ℂ → ℝ} (hg : Continuous g) {δ : ℝ} (hδ : 0 < δ)
    (hgv : ∀ x : ℂ, ‖x‖ < δ → g x = 0) (s : ℝ) :
    Continuous fun x => g x * ‖x‖ ^ s := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    have hmem : Metric.ball (0 : ℂ) δ ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hδ
    filter_upwards [hmem] with y hy
    have hy' : ‖y‖ < δ := by simpa [Metric.mem_ball, dist_zero_right] using hy
    simp [hgv y hy']
  · have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    exact (hg.continuousAt).mul ((continuous_norm.continuousAt).rpow_const (Or.inl hx0))

/-- **Weyl scaling of the LQG measure, vague form.** If `μ` is the continuum LQG measure of `h`, the approximations
of the shifted field `h - γ log|·|` converge vaguely to `|x|^{-γ²} μ(dx)` on test functions vanishing near `0`. -/
theorem tendsto_lqgApprox_shift (γ : ℝ) (h : ℝ → ℂ → ℝ) (hc : ∀ ε : ℝ, 0 < ε → Continuous (h ε))
    (μ : Measure ℂ) (hμ : IsLQGLimitCont γ h μ) (g : ℂ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    {δ : ℝ} (hδ : 0 < δ) (hgv : ∀ x : ℂ, ‖x‖ < δ → g x = 0) :
    Tendsto (fun ε : ℝ => ∫ x, g x ∂(lqgApprox γ (wShift γ h) ε)) (𝓝[Set.Ioi 0] 0)
      (𝓝 (∫ x, (g x * ‖x‖ ^ (-γ ^ 2)) ∂μ)) := by
  have hf : Continuous fun x => g x * ‖x‖ ^ (-γ ^ 2) :=
    continuous_mul_rpow_of_vanish hg hδ hgv _
  have hfc : HasCompactSupport fun x => g x * ‖x‖ ^ (-γ ^ 2) := hgc.mul_right
  have hlim := hμ.2 _ hf hfc
  refine Tendsto.congr' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  have hgε : ∀ x : ℂ, g x ≠ 0 → ε ≤ ‖x‖ := fun x hx => by
    by_contra hlt
    exact hx (hgv x (lt_trans (not_le.1 hlt) hε.2))
  exact (integral_lqgApprox_shift γ h hε.1 (hc ε hε.1) g hgε).symm

end MatedCRT.Field

