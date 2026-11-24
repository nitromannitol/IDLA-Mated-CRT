import MatedCRT.FirstPass.Derived.ChartClockTransport
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The transported clock of an integral clock under an inverse chart

Change-of-variables part of step R1 of the Revuz route to Berestycki (2015), Theorem 1.3. For an open set `U`, a map
`ψ`, a rate `ρ : ℂ → ℝ` and a path `w`, the *exit-rate clock* `exitRateClock D ρ w` has rate `ρ(w_r)` before the
exit time of `w` from `D` and rate `1` afterwards (the conformal clock is `exitRateClock U |ψ'|²`). The
*transported rate* of `ρ` under an inverse chart `ψ` of `U` is `ρ(φ v) / |ψ'(φ v)|²` on the unit disc, with
`φ = chartMap U ψ` the conformal map (`chartTransportRate`).

Let `b` be a path which starts in `U`, leaves it at the time `τ`, and along which the conformal rate is locally
integrable, `A` its conformal clock and `W = ψ ∘ (b ∘ A⁻¹ stopped at its exit from U)`. Then for `σ ≤ A τ`
(`exitRateClock_chartTransportRate_eq`):

`∫_0^σ (transported rate of ρ along W, until W leaves the disc) = ∫_0^{A⁻¹ σ} ρ(b_s) ds`,

by the change of variables `r = A(s)`, `dr = |ψ'(b_s)|² ds` (`integral_image_eq_integral_abs_deriv_smul`). This is
the hypothesis `G W σ = F b (A⁻¹ σ)` of `chartStopPath_lbmContinuousPath_eq` for the clock `F b = ∫_0^· ρ(b_s) ds`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT

open Classical in
/-- The rate `ρ(w_r)` before the exit time of the path `w` from `D`, and `1` from the exit time on (for `r < 0`, the
value at `0`). -/
noncomputable def exitRate (D : Set ℂ) (ρ : ℂ → ℝ) (w : ContinuousPath ℂ) (r : ℝ) : ℝ :=
  if ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D w then ρ (w r.toNNReal) else 1

/-- **The exit-rate clock** `∫_0^σ (exit rate)`: rate `ρ(w_r)` until the exit time of `w` from `D`, unit rate
afterwards. -/
noncomputable def exitRateClock (D : Set ℂ) (ρ : ℂ → ℝ) (w : ContinuousPath ℂ) (σ : ℝ≥0) : ℝ :=
  ∫ r in (0 : ℝ)..(σ : ℝ), exitRate D ρ w r

/-- **The transported rate** `ρ(φ v) / |ψ'(φ v)|²` of a rate `ρ` on `U`, as a rate on the unit disc, with
`φ = chartMap U ψ` the conformal map of the inverse chart `ψ`. -/
noncomputable def chartTransportRate (U : Set ℂ) (ψ : C(ℂ, ℂ)) (ρ : ℂ → ℝ) (v : ℂ) : ℝ :=
  ρ (chartMap U ψ v) / ‖deriv ψ (chartMap U ψ v)‖ ^ 2

/-- The real primitive `x ↦ ∫_0^x (conformal rate)` of the conformal rate. -/
noncomputable def chartPrimitive (U : Set ℂ) (ψ : ℂ → ℂ) (b : ContinuousPath ℂ) (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..x, chartRate U ψ b s

/-- The conformal rate is the exit rate of `|ψ'|²`. -/
theorem chartRate_eq_exitRate (U : Set ℂ) (ψ : ℂ → ℂ) :
    chartRate U ψ = exitRate U (fun x => ‖deriv ψ x‖ ^ 2) :=
  rfl

/-- The conformal clock is the exit-rate clock of `|ψ'|²`. -/
theorem chartClock_eq_exitRateClock (U : Set ℂ) (ψ : ℂ → ℂ) :
    chartClock U ψ = exitRateClock U (fun x => ‖deriv ψ x‖ ^ 2) :=
  rfl

/-- Before the exit time, the exit rate is `ρ(w_r)`. -/
theorem exitRate_of_lt_exitTime {D : Set ℂ} {ρ : ℂ → ℝ} {w : ContinuousPath ℂ} {r : ℝ}
    (h : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D w) : exitRate D ρ w r = ρ (w r.toNNReal) := by
  unfold exitRate
  exact ite_eq_left h

/-- From the exit time on, the exit rate is `1`. -/
theorem exitRate_of_exitTime_le {D : Set ℂ} {ρ : ℂ → ℝ} {w : ContinuousPath ℂ} {r : ℝ}
    (h : ContinuousPath.exitTime D w ≤ ((r.toNNReal : ℝ≥0) : ℝ≥0∞)) : exitRate D ρ w r = 1 := by
  unfold exitRate
  exact ite_eq_right (not_lt.2 h)

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-- The conformal map of an inverse chart inverts it on `U`. -/
theorem IsInverseChart.chartMap_apply (hψ : IsInverseChart U z ψ) {x : ℂ} (hx : x ∈ U) :
    chartMap U ψ (ψ x) = x :=
  (hψ.injOn.mono subset_closure).leftInvOn_invFunOn hx

/-- An inverse chart maps `U` into the unit disc. -/
theorem IsInverseChart.mapsTo_ball (hψ : IsInverseChart U z ψ) : MapsTo ψ U (Metric.ball (0 : ℂ) 1) :=
  fun _ hx => hψ.image_eq ▸ mem_image_of_mem ψ hx

/-- **Change of variables for the transported clock.** Let `ψ` be an inverse chart of the open set `U`, `b` a path
which starts in `U` and leaves it at the time `τ`, along which the conformal rate is locally integrable, and
`W` the chart image of `b` run with its conformal clock `A` and stopped at its exit from `U`. For any rate `ρ` and
`σ ≤ A τ`, the exit-rate clock of the transported rate along `W` at time `σ` is `∫_0^{A⁻¹ σ} ρ(b_s) ds`. -/
theorem exitRateClock_chartTransportRate_eq (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    {b : ContinuousPath ℂ} (hb0 : b 0 ∈ U) {τ : ℝ≥0} (hτ : ContinuousPath.exitTime U b = τ)
    (hint : ∀ T : ℝ, IntervalIntegrable (chartRate U ψ b) volume 0 T) (ρ : ℂ → ℝ) {σ : ℝ≥0}
    (hσ : (σ : ℝ) ≤ chartClock U ψ b τ) :
    exitRateClock (Metric.ball (0 : ℂ) 1) (chartTransportRate U ψ ρ)
        (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) σ =
      ∫ s in (0 : ℝ)..((_root_.HarmonicBalls.clockInverse (chartClock U ψ b) σ : ℝ≥0) : ℝ),
        ρ (b s.toNNReal) := by
  have hfin : ContinuousPath.exitTime U b ≠ ⊤ := by
    rw [hτ]
    exact ENNReal.coe_ne_top
  have hA : IsTimeChangeClock (chartClock U ψ b) := isTimeChangeClock_chartClock hψ hU hint hfin
  set W := chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b) with hW
  set u := _root_.HarmonicBalls.clockInverse (chartClock U ψ b) σ
  have hAu : chartClock U ψ b u = σ := IsTimeChangeClock.apply_clockInverse_eq hA σ
  have huτ : u ≤ τ := (clockInverse_le_iff_of_isTimeChangeClock hA σ τ).2 hσ
  have hint' : ∀ a c : ℝ, IntervalIntegrable (chartRate U ψ b) volume a c :=
    fun a c => (hint a).symm.trans (hint c)
  -- the real primitive of the conformal rate
  have hmono : StrictMono (chartPrimitive U ψ b) := by
    intro x y hxy
    have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on (hint' x y)
      (fun s _ => chartRate_pos hψ hU b s) hxy
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint' 0 x) (hint' x y)
    simp only [chartPrimitive]
    linarith
  have hcont : Continuous (chartPrimitive U ψ b) := intervalIntegral.continuous_primitive hint' 0
  have hP0 : chartPrimitive U ψ b 0 = 0 := intervalIntegral.integral_same
  have hPu : chartPrimitive U ψ b u = σ := hAu
  -- before the exit time
  have hlt_exit : ∀ x ∈ Ioo (0 : ℝ) τ,
      ((x.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime U b := by
    intro x hx
    rw [hτ, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hx.1.le]
    exact hx.2
  have hdψ : ContinuousOn (deriv ψ) U := (hψ.differentiableOn.deriv hU).continuousOn
  have hcontAt : ∀ x ∈ Ioo (0 : ℝ) τ, ContinuousAt (chartRate U ψ b) x := by
    intro x hx
    have hmem : b x.toNNReal ∈ U := ContinuousPath.mem_of_lt_exitTime U b _ (hlt_exit x hx)
    have h1 : ContinuousAt (fun y : ℝ => b y.toNNReal) x :=
      (b.continuous.comp continuous_real_toNNReal).continuousAt
    have h2 : ContinuousAt (deriv ψ) (b x.toNNReal) := hdψ.continuousAt (hU.mem_nhds hmem)
    have h3 : ContinuousAt (fun y : ℝ => ‖deriv ψ (b y.toNNReal)‖ ^ 2) x :=
      ((ContinuousAt.comp (f := fun y : ℝ => b y.toNNReal) h2 h1).norm).pow 2
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact chartRate_of_lt_exitTime (hlt_exit y hy)
  have hsm : ∀ x ∈ Ioo (0 : ℝ) τ, StronglyMeasurableAtFilter (chartRate U ψ b) (𝓝 x) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hcontAt
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) τ, HasDerivAt (chartPrimitive U ψ b) (chartRate U ψ b x) x :=
    fun x hx => intervalIntegral.integral_hasDerivAt_right (hint' 0 x) (hsm x hx) (hcontAt x hx)
  have hsub : Ioo (0 : ℝ) u ⊆ Ioo (0 : ℝ) τ :=
    Ioo_subset_Ioo_right (NNReal.coe_le_coe.2 huτ)
  -- the image of `(0, u)` under the primitive is `(0, σ)`
  have himage : chartPrimitive U ψ b '' Ioo (0 : ℝ) u = Ioo (0 : ℝ) σ := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hP0]
        exact hmono hx.1
      · rw [← hPu]
        exact hmono hx.2
    · have h := intermediate_value_Ioo (NNReal.coe_nonneg u) (hcont.continuousOn (s := Icc (0 : ℝ) u))
      rwa [hP0, hPu] at h
  -- the change of variables `r = A(s)`
  have hcov := integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) u))
    (fun x hx => (hderiv x (hsub hx)).hasDerivWithinAt) (fun x _ y _ hxy => hmono.injective hxy)
    (fun r : ℝ => chartTransportRate U ψ ρ (W r.toNNReal))
  -- the integrands
  have hexit : ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) W =
      ((Real.toNNReal (chartClock U ψ b τ) : ℝ≥0) : ℝ≥0∞) :=
    exitTime_chartStopPath_lbmContinuousPath hU hψ.mapsTo_ball hψ.mapsTo_frontier hA hb0 hτ
  have hpt : ∀ x ∈ Ioo (0 : ℝ) u, |chartRate U ψ b x| •
      chartTransportRate U ψ ρ (W (chartPrimitive U ψ b x).toNNReal) = ρ (b x.toNNReal) := by
    intro x hx
    have hxτ := hsub hx
    have hx0 : 0 ≤ x := hx.1.le
    have hmem : b x.toNNReal ∈ U := ContinuousPath.mem_of_lt_exitTime U b _ (hlt_exit x hxτ)
    have hxle : x.toNNReal ≤ τ := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx0]
      exact hxτ.2.le
    have hPx : chartPrimitive U ψ b x = chartClock U ψ b x.toNNReal := by
      show chartPrimitive U ψ b x = chartPrimitive U ψ b (x.toNNReal : ℝ)
      rw [Real.coe_toNNReal _ hx0]
    have hWx : W (chartPrimitive U ψ b x).toNNReal = ψ (b x.toNNReal) := by
      rw [hPx, hW, chartStopPath_lbmContinuousPath_apply hA hτ,
        clockInverse_clockValue hA.map_zero hA.strictMono, min_eq_left hxle]
    have hd : ‖deriv ψ (b x.toNNReal)‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.2 (hψ.deriv_ne_zero hU hmem))
    rw [chartRate_of_lt_exitTime (hlt_exit x hxτ), abs_of_nonneg (sq_nonneg _), smul_eq_mul, hWx,
      chartTransportRate, hψ.chartMap_apply hmem, mul_comm]
    exact div_mul_cancel₀ _ hd
  have hpt0 : ∀ r ∈ Ioo (0 : ℝ) σ, exitRate (Metric.ball (0 : ℂ) 1) (chartTransportRate U ψ ρ) W r =
      chartTransportRate U ψ ρ (W r.toNNReal) := by
    intro r hr
    refine exitRate_of_lt_exitTime ?_
    rw [hexit, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr.1.le,
      Real.coe_toNNReal _ (IsTimeChangeClock.clock_nonneg hA τ)]
    exact lt_of_lt_of_le hr.2 hσ
  calc exitRateClock (Metric.ball (0 : ℂ) 1) (chartTransportRate U ψ ρ) W σ
      = ∫ r in Ioo (0 : ℝ) σ, chartTransportRate U ψ ρ (W r.toNNReal) := by
        rw [exitRateClock, intervalIntegral.integral_of_le (NNReal.coe_nonneg σ),
          integral_Ioc_eq_integral_Ioo]
        exact setIntegral_congr_fun measurableSet_Ioo hpt0
    _ = ∫ r in chartPrimitive U ψ b '' Ioo (0 : ℝ) u, chartTransportRate U ψ ρ (W r.toNNReal) := by
        rw [himage]
    _ = ∫ x in Ioo (0 : ℝ) u,
          |chartRate U ψ b x| • chartTransportRate U ψ ρ (W (chartPrimitive U ψ b x).toNNReal) := hcov
    _ = ∫ x in Ioo (0 : ℝ) u, ρ (b x.toNNReal) := setIntegral_congr_fun measurableSet_Ioo hpt
    _ = ∫ s in (0 : ℝ)..(u : ℝ), ρ (b s.toNNReal) := by
        rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg u), integral_Ioc_eq_integral_Ioo]

end MatedCRT
