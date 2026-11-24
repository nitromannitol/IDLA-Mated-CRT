import MatedCRT.FirstPass.Derived.ChartClockChangeOfVariables
import MatedCRT.FirstPass.Derived.PlanarBrownianBoundedExit
import MatedCRT.Proofs.LBM.DirichletDiscExit

/-!
# The law of the chart image of time-changed planar Brownian motion

Law-level part of steps R1–R2 of the Revuz route to Berestycki (2015), Theorem 1.3. Let `ψ` be an inverse chart of
the bounded open set `U` and `w ∈ U`. Assume the law form of Lévy's conformal invariance at `w` (the content of
`LevyConformalChartStmt`, together with the almost sure local integrability of the conformal rate): the chart image
`T b` of Brownian motion from `w` run with its conformal clock and stopped at its exit from `U` has the law of
Brownian motion from `ψ(w)` stopped at its exit from the unit disc.

* `map_chartStopPath_lbmContinuousPath_eq`: for any clock functional `F` and any clock functional `G` on paths of
  the disc with `G (T b) σ = F b (A⁻¹ σ)` before the exit, the chart image of Brownian motion run with the clock `F`
  and stopped at its exit from `U` has the law of disc Brownian motion run with the clock `G` and stopped at its exit
  from the disc.
* `isTimeChangeClock_exitRateClock_chartTransportRate`: for a continuous positive rate `ρ`, the transported clock
  (the exit-rate clock of `ρ(φ v) / |ψ'(φ v)|²`) along `T b` is a time-change clock.
* `map_chartStopPath_lbmContinuousPath_integralClock`: the law identity for integral clocks `F b t = ∫_0^t ρ(b_s) ds`
  with `G` the transported clock.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT

/-! ### Exit-rate clocks -/

theorem exitRateClock_zero (D : Set ℂ) (ρ : ℂ → ℝ) (w : ContinuousPath ℂ) : exitRateClock D ρ w 0 = 0 := by
  simp [exitRateClock]

/-- An exit rate whose rate is positive on `D` is positive. -/
theorem exitRate_pos {D : Set ℂ} {ρ : ℂ → ℝ} (hρ : ∀ v ∈ D, 0 < ρ v) (w : ContinuousPath ℂ) (r : ℝ) :
    0 < exitRate D ρ w r := by
  by_cases h : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D w
  · rw [exitRate_of_lt_exitTime h]
    exact hρ _ (ContinuousPath.mem_of_lt_exitTime D w _ h)
  · rw [exitRate_of_exitTime_le (not_lt.1 h)]
    exact one_pos

/-- **The exit-rate clock is a time-change clock.** For a rate positive on `D` and a path which leaves `D` and along
which the exit rate is locally integrable, the exit-rate clock starts at `0`, is continuous, strictly increasing and
unbounded. -/
theorem isTimeChangeClock_exitRateClock {D : Set ℂ} {ρ : ℂ → ℝ} (hρ : ∀ v ∈ D, 0 < ρ v)
    {w : ContinuousPath ℂ} (hint : ∀ T : ℝ, IntervalIntegrable (exitRate D ρ w) volume 0 T)
    (hfin : ContinuousPath.exitTime D w ≠ ⊤) : IsTimeChangeClock (exitRateClock D ρ w) := by
  have hint' : ∀ a c : ℝ, IntervalIntegrable (exitRate D ρ w) volume a c :=
    fun a c => (hint a).symm.trans (hint c)
  refine ⟨exitRateClock_zero D ρ w, ?_, ?_, ?_⟩
  · exact (intervalIntegral.continuous_primitive hint' 0).comp NNReal.continuous_coe
  · intro s t hst
    have hst' : (s : ℝ) < t := NNReal.coe_lt_coe.2 hst
    have hpos : 0 < ∫ x in (s : ℝ)..(t : ℝ), exitRate D ρ w x :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hint' s t) (fun x _ => exitRate_pos hρ w x) hst'
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint' 0 s) (hint' s t)
    simp only [exitRateClock]
    linarith
  · set τ : ℝ≥0 := (ContinuousPath.exitTime D w).toNNReal with hτ
    have hτe : ContinuousPath.exitTime D w = (τ : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin).symm
    have hlow : ∀ t : ℝ≥0, τ ≤ t → (t : ℝ) + -(τ : ℝ) ≤ exitRateClock D ρ w t := by
      intro t hτt
      have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint' 0 τ) (hint' τ t)
      have h0 : 0 ≤ ∫ x in (0 : ℝ)..(τ : ℝ), exitRate D ρ w x :=
        intervalIntegral.integral_nonneg (NNReal.coe_nonneg τ) (fun x _ => (exitRate_pos hρ w x).le)
      have hcongr : EqOn (exitRate D ρ w) (fun _ => (1 : ℝ)) (uIcc (τ : ℝ) t) := by
        intro x hx
        rw [Set.uIcc_of_le (NNReal.coe_le_coe.2 hτt)] at hx
        have h2 : τ ≤ x.toNNReal := by
          have h3 := Real.toNNReal_le_toNNReal hx.1
          rwa [Real.toNNReal_coe] at h3
        apply exitRate_of_exitTime_le
        rw [hτe]
        exact ENNReal.coe_le_coe.2 h2
      have h1 : ∫ x in (τ : ℝ)..(t : ℝ), exitRate D ρ w x = (t : ℝ) - τ := by
        rw [intervalIntegral.integral_congr hcongr]
        simp
      simp only [exitRateClock]
      linarith
    have hlin : Tendsto (fun t : ℝ≥0 => (t : ℝ) + -(τ : ℝ)) atTop atTop :=
      (NNReal.tendsto_coe_atTop.2 tendsto_id).atTop_add tendsto_const_nhds
    refine tendsto_atTop_mono' atTop ?_ hlin
    filter_upwards [eventually_ge_atTop τ] with t ht
    exact hlow t ht

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-- The conformal map of an inverse chart maps the unit disc into `U`. -/
theorem IsInverseChart.chartMap_mem (hψ : IsInverseChart U z ψ) {v : ℂ} (hv : v ∈ Metric.ball (0 : ℂ) 1) :
    chartMap U ψ v ∈ U := by
  rw [← hψ.image_eq] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  rw [hψ.chartMap_apply hx]
  exact hx

/-- The transported rate of a positive rate is positive on the unit disc. -/
theorem chartTransportRate_pos (hψ : IsInverseChart U z ψ) (hU : IsOpen U) {ρ : ℂ → ℝ} (hρ : ∀ x, 0 < ρ x)
    {v : ℂ} (hv : v ∈ Metric.ball (0 : ℂ) 1) : 0 < chartTransportRate U ψ ρ v :=
  div_pos (hρ _) (pow_pos (norm_pos_iff.2 (hψ.deriv_ne_zero hU (hψ.chartMap_mem hv))) 2)

/-- **The transported rate is locally integrable along the chart image.** Let `b` start in `U`, leave it at the
time `τ`, and let the conformal rate along `b` be locally integrable. For a continuous positive rate `ρ`, along the
chart image `W` of `b` run with its conformal clock and stopped at its exit from `U`, the exit rate of the transported
rate is locally integrable: before the exit time of `W` from the disc, the change of variables gives the positive
value `∫_0^τ ρ(b_s) ds` to its integral; afterwards it is `1`. -/
theorem intervalIntegrable_exitRate_chartTransportRate (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    {b : ContinuousPath ℂ} (hb0 : b 0 ∈ U) {τ : ℝ≥0} (hτ : ContinuousPath.exitTime U b = τ)
    (hint : ∀ T : ℝ, IntervalIntegrable (chartRate U ψ b) volume 0 T) {ρ : ℂ → ℝ} (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x) (T : ℝ) :
    IntervalIntegrable (exitRate (Metric.ball (0 : ℂ) 1) (chartTransportRate U ψ ρ)
      (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))) volume 0 T := by
  have hfin : ContinuousPath.exitTime U b ≠ ⊤ := by
    rw [hτ]
    exact ENNReal.coe_ne_top
  have hA : IsTimeChangeClock (chartClock U ψ b) := isTimeChangeClock_chartClock hψ hU hint hfin
  have ha0 : 0 ≤ chartClock U ψ b τ := IsTimeChangeClock.clock_nonneg hA τ
  have hexit : ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1)
      (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) =
      ((Real.toNNReal (chartClock U ψ b τ) : ℝ≥0) : ℝ≥0∞) :=
    exitTime_chartStopPath_lbmContinuousPath hU hψ.mapsTo_ball hψ.mapsTo_frontier hA hb0 hτ
  -- integrability up to the exit time of the chart image from the disc
  have h0a : IntervalIntegrable (exitRate (Metric.ball (0 : ℂ) 1) (chartTransportRate U ψ ρ)
      (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))) volume 0 (chartClock U ψ b τ) := by
    rcases ha0.eq_or_lt with h | h
    · rw [← h]
    · by_contra hni
      have hτpos : 0 < (τ : ℝ) := by
        by_contra hle
        have hτ0 : τ = 0 := NNReal.coe_eq_zero.1 (le_antisymm (not_lt.1 hle) τ.2)
        rw [hτ0, chartClock_zero] at h
        exact lt_irrefl _ h
      have hσ : ((Real.toNNReal (chartClock U ψ b τ) : ℝ≥0) : ℝ) ≤ chartClock U ψ b τ := by
        rw [Real.coe_toNNReal _ ha0]
      have hcov := exitRateClock_chartTransportRate_eq hψ hU hb0 hτ hint ρ hσ
      rw [clockInverse_clockValue hA.map_zero hA.strictMono τ, exitRateClock, Real.coe_toNNReal _ ha0,
        intervalIntegral.integral_undef hni] at hcov
      have hpos : 0 < ∫ s in (0 : ℝ)..(τ : ℝ), ρ (b s.toNNReal) :=
        intervalIntegral.intervalIntegral_pos_of_pos_on
          ((hρ.comp (b.continuous.comp continuous_real_toNNReal)).intervalIntegrable 0 τ)
          (fun s _ => hρpos _) hτpos
      rw [← hcov] at hpos
      exact lt_irrefl _ hpos
  have hint' : ∀ T : ℝ, IntervalIntegrable (exitRate (Metric.ball (0 : ℂ) 1) (chartTransportRate U ψ ρ)
      (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))) volume 0 T := by
    intro T
    rcases le_total T 0 with hT | hT
    · refine ContinuousOn.intervalIntegrable ?_
      refine (continuousOn_const (c := exitRate (Metric.ball (0 : ℂ) 1) (chartTransportRate U ψ ρ)
        (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) 0)).congr fun r hr => ?_
      rw [uIcc_of_ge hT] at hr
      simp only [exitRate, Real.toNNReal_of_nonpos hr.2, Real.toNNReal_zero]
    · rcases le_total T (chartClock U ψ b τ) with hTa | hTa
      · refine h0a.mono_set ?_
        rw [uIcc_of_le hT, uIcc_of_le ha0]
        exact Icc_subset_Icc_right hTa
      · refine h0a.trans (ContinuousOn.intervalIntegrable ?_)
        refine (continuousOn_const (c := (1 : ℝ))).congr fun r hr => ?_
        rw [uIcc_of_le hTa] at hr
        apply exitRate_of_exitTime_le
        rw [hexit]
        exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal hr.1)
  exact hint' T

/-- **The transported clock is a time-change clock.** Under the hypotheses of
`intervalIntegrable_exitRate_chartTransportRate`, the exit-rate clock of the transported rate along the chart image
of `b` is a time-change clock (the chart image leaves the disc at the time `A_b(τ)`). -/
theorem isTimeChangeClock_exitRateClock_chartTransportRate (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    {b : ContinuousPath ℂ} (hb0 : b 0 ∈ U) {τ : ℝ≥0} (hτ : ContinuousPath.exitTime U b = τ)
    (hint : ∀ T : ℝ, IntervalIntegrable (chartRate U ψ b) volume 0 T) {ρ : ℂ → ℝ} (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x) :
    IsTimeChangeClock (exitRateClock (Metric.ball (0 : ℂ) 1) (chartTransportRate U ψ ρ)
      (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))) := by
  have hfin : ContinuousPath.exitTime U b ≠ ⊤ := by
    rw [hτ]
    exact ENNReal.coe_ne_top
  have hA : IsTimeChangeClock (chartClock U ψ b) := isTimeChangeClock_chartClock hψ hU hint hfin
  refine isTimeChangeClock_exitRateClock (fun v hv => chartTransportRate_pos hψ hU hρpos hv)
    (intervalIntegrable_exitRate_chartTransportRate hψ hU hb0 hτ hint hρ hρpos) ?_
  rw [exitTime_chartStopPath_lbmContinuousPath hU hψ.mapsTo_ball hψ.mapsTo_frontier hA hb0 hτ]
  exact ENNReal.coe_ne_top

/-- **Law of the chart image of time-changed Brownian motion.** Let `ψ` be an inverse chart of the bounded open set
`U`, `w ∈ U`, and assume Lévy's conformal invariance at `w` in law form: the chart image `T b` of Brownian motion `b`
from `w` run with its conformal clock and stopped at its exit from `U` is a.e. measurable with the law of Brownian
motion from `ψ(w)` stopped at its exit from the unit disc, and the conformal rate is almost surely locally
integrable. Let `F` be a clock functional and `G` a clock functional on disc paths such that, almost surely,
`F b` and `G (T b)` are time-change clocks with `G (T b) σ = F b (A⁻¹ σ)` before the exit (`A` the conformal clock).
Then the chart image of `b` run with the clock `F` and stopped at its exit from `U` has the law of the stopped disc
Brownian motion run with the clock `G` and stopped at its exit from the disc. -/
theorem map_chartStopPath_lbmContinuousPath_eq (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {w : ℂ} (hw : w ∈ U)
    (hTm : AEMeasurable (fun b => chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))
      (planarBrownianMotion w))
    (hTmap : (planarBrownianMotion w).map
        (fun b => chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) =
      (planarBrownianMotion (ψ w)).map (stopAtExitTime (Metric.ball 0 1)))
    (hint : ∀ᵐ b ∂planarBrownianMotion w, ∀ T : ℝ, IntervalIntegrable (chartRate U ψ b) volume 0 T)
    {F G : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hGm : AEMeasurable (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1) (lbmContinuousPath G W))
      ((planarBrownianMotion (ψ w)).map (stopAtExitTime (Metric.ball 0 1))))
    (hFG : ∀ᵐ b ∂planarBrownianMotion w, ∀ τ : ℝ≥0, ContinuousPath.exitTime U b = τ →
      IsTimeChangeClock (chartClock U ψ b) →
      IsTimeChangeClock (F b) ∧
      IsTimeChangeClock (G (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))) ∧
      ∀ σ : ℝ≥0, (σ : ℝ) ≤ chartClock U ψ b τ →
        G (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) σ =
          F b (_root_.HarmonicBalls.clockInverse (chartClock U ψ b) σ)) :
    (planarBrownianMotion w).map (fun b => chartStopPath U ψ (lbmContinuousPath F b)) =
      ((planarBrownianMotion (ψ w)).map (stopAtExitTime (Metric.ball 0 1))).map
        (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1) (lbmContinuousPath G W)) := by
  have hae : (fun b => chartStopPath U ψ (lbmContinuousPath F b)) =ᵐ[planarBrownianMotion w]
      (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1) (lbmContinuousPath G W)) ∘
        (fun b => chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) := by
    filter_upwards [ae_planarBrownianMotion_eval_zero w, ae_planarBrownianMotion_exit_all_bounded w, hint, hFG]
      with b hb0 hexit hb hfg
    have hτ : ContinuousPath.exitTime U b = ((ContinuousPath.exitTime U b).toNNReal : ℝ≥0∞) :=
      (ENNReal.coe_toNNReal (hexit U hUb).ne).symm
    have hA : IsTimeChangeClock (chartClock U ψ b) := isTimeChangeClock_chartClock hψ hU hb (hexit U hUb).ne
    obtain ⟨hF, hG, hGF⟩ := hfg _ hτ hA
    have hb0U : b 0 ∈ U := by
      rw [hb0]
      exact hw
    exact chartStopPath_lbmContinuousPath_eq hU hψ.mapsTo_ball hψ.mapsTo_frontier hA hF hb0U hτ hG hGF
  have hGm' : AEMeasurable (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1) (lbmContinuousPath G W))
      ((planarBrownianMotion w).map (fun b => chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))) := by
    rw [hTmap]
    exact hGm
  rw [Measure.map_congr hae, ← hGm'.map_map_of_aemeasurable hTm, hTmap]

/-- **Law of the chart image for integral clocks.** Under the hypotheses of `map_chartStopPath_lbmContinuousPath_eq`
on `ψ`, `U` and `w`, let `F` be a family of time-change clocks with `F b t = ∫_0^t ρ(b_s) ds` for a continuous
positive rate `ρ`. Then the chart image of Brownian motion from `w` run with the clock `F` and stopped at its exit
from `U` has the law of Brownian motion from `ψ(w)` stopped at its exit from the disc, run with the transported clock
of `ρ` and stopped at its exit from the disc. -/
theorem map_chartStopPath_lbmContinuousPath_integralClock (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {w : ℂ} (hw : w ∈ U)
    (hTm : AEMeasurable (fun b => chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))
      (planarBrownianMotion w))
    (hTmap : (planarBrownianMotion w).map
        (fun b => chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) =
      (planarBrownianMotion (ψ w)).map (stopAtExitTime (Metric.ball 0 1)))
    (hint : ∀ᵐ b ∂planarBrownianMotion w, ∀ T : ℝ, IntervalIntegrable (chartRate U ψ b) volume 0 T)
    {ρ : ℂ → ℝ} (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : ∀ b, IsTimeChangeClock (F b)) (hFρ : ∀ b t, F b t = ∫ s in (0 : ℝ)..(t : ℝ), ρ (b s.toNNReal))
    (hGm : AEMeasurable (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1)
        (lbmContinuousPath (exitRateClock (Metric.ball (0 : ℂ) 1) (chartTransportRate U ψ ρ)) W))
      ((planarBrownianMotion (ψ w)).map (stopAtExitTime (Metric.ball 0 1)))) :
    (planarBrownianMotion w).map (fun b => chartStopPath U ψ (lbmContinuousPath F b)) =
      ((planarBrownianMotion (ψ w)).map (stopAtExitTime (Metric.ball 0 1))).map
        (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1)
          (lbmContinuousPath (exitRateClock (Metric.ball (0 : ℂ) 1) (chartTransportRate U ψ ρ)) W)) := by
  refine map_chartStopPath_lbmContinuousPath_eq hψ hU hUb hw hTm hTmap hint hGm ?_
  filter_upwards [ae_planarBrownianMotion_eval_zero w, hint] with b hb0 hb τ hτ _
  have hb0U : b 0 ∈ U := by
    rw [hb0]
    exact hw
  refine ⟨hF b, isTimeChangeClock_exitRateClock_chartTransportRate hψ hU hb0U hτ hb hρ hρpos, fun σ hσ => ?_⟩
  rw [exitRateClock_chartTransportRate_eq hψ hU hb0U hτ hb ρ hσ, hFρ]

/-- `map_chartStopPath_lbmContinuousPath_eq` from Lévy's conformal invariance (`LevyConformalChartStmt`). -/
theorem map_chartStopPath_lbmContinuousPath_eq_of_levy (hLevy : LevyConformalChartStmt)
    (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U) {w : ℂ} (hw : w ∈ U)
    {F G : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hGm : AEMeasurable (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1) (lbmContinuousPath G W))
      ((planarBrownianMotion (ψ w)).map (stopAtExitTime (Metric.ball 0 1))))
    (hFG : ∀ᵐ b ∂planarBrownianMotion w, ∀ τ : ℝ≥0, ContinuousPath.exitTime U b = τ →
      IsTimeChangeClock (chartClock U ψ b) →
      IsTimeChangeClock (F b) ∧
      IsTimeChangeClock (G (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))) ∧
      ∀ σ : ℝ≥0, (σ : ℝ) ≤ chartClock U ψ b τ →
        G (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) σ =
          F b (_root_.HarmonicBalls.clockInverse (chartClock U ψ b) σ)) :
    (planarBrownianMotion w).map (fun b => chartStopPath U ψ (lbmContinuousPath F b)) =
      ((planarBrownianMotion (ψ w)).map (stopAtExitTime (Metric.ball 0 1))).map
        (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1) (lbmContinuousPath G W)) := by
  obtain ⟨hint, hTm, hTmap⟩ := hLevy U z ψ hU hUb hψ w hw
  exact map_chartStopPath_lbmContinuousPath_eq hψ hU hUb hw hTm hTmap hint hGm hFG

end MatedCRT
