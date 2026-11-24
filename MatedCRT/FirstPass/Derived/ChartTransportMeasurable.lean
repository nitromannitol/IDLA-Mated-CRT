import MatedCRT.FirstPass.Derived.ChartLevyLawTransport

/-!
# Measurability of the transported time change, and the chart image of the approximating LBM

Completes the law-level step of the Revuz route to Berestycki (2015), Theorem 1.3, for integral clocks.

* The conformal map `φ = chartMap U ψ` of an inverse chart of a bounded open set is continuous on the unit disc
  (`IsInverseChart.continuousOn_chartMap`: `ψ` is injective and continuous on the compact closure of `U`), so the
  transported rate of a continuous rate is continuous on the disc.
* For a rate `ρ` continuous on the open set `D`, the exit rate is jointly Borel in the path and the time, the exit-rate
  clock is Borel in the path, and on the Borel set `exitRateGoodSet D ρ` of paths which leave `D` and along which the
  exit rate is locally integrable, it is a time-change clock; hence the time-changed path is almost everywhere
  measurable for every law carried by that set (`aemeasurable_lbmContinuousPath_exitRateClock`).
* `map_chartStopPath_lbmContinuousPath_integralClock_of_levy`: from Lévy's conformal invariance, the chart image of
  planar Brownian motion from `w` run with an integral clock of continuous positive rate `ρ` and stopped at its exit
  from `U` has the law of Brownian motion from `ψ(w)` stopped at its exit from the disc, run with the transported clock
  of `ρ` and stopped at its exit from the disc.
* `map_chartStopPath_lbmContinuousPath_lqgApproxClockPlus_of_levy`: the instance of the approximating LQG clock
  `A_n(b, t) = ∫_0^t (ε_n^{γ²/2} e^{γ h_{ε_n}(b_s)} + ε_n) ds`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT

/-! ### Exit rates: negative times and joint measurability -/

theorem exitRate_of_nonpos (D : Set ℂ) (ρ : ℂ → ℝ) (w : ContinuousPath ℂ) {r : ℝ} (hr : r ≤ 0) :
    exitRate D ρ w r = exitRate D ρ w 0 := by
  simp only [exitRate, Real.toNNReal_of_nonpos hr, Real.toNNReal_zero]

theorem intervalIntegrable_exitRate_of_nonpos (D : Set ℂ) (ρ : ℂ → ℝ) (w : ContinuousPath ℂ) {T : ℝ}
    (hT : T ≤ 0) : IntervalIntegrable (exitRate D ρ w) volume 0 T := by
  refine ContinuousOn.intervalIntegrable ?_
  refine (continuousOn_const (c := exitRate D ρ w 0)).congr fun r hr => ?_
  rw [uIcc_of_ge hT] at hr
  exact exitRate_of_nonpos D ρ w hr.2

/-- The exit rate only uses the values of the rate on `D`. -/
theorem exitRate_piecewise (D : Set ℂ) (ρ : ℂ → ℝ) [DecidablePred (· ∈ D)] :
    exitRate D (D.piecewise ρ fun _ => 1) = exitRate D ρ := by
  funext w r
  by_cases h : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D w
  · rw [exitRate_of_lt_exitTime h, exitRate_of_lt_exitTime h,
      piecewise_eq_of_mem _ _ _ (ContinuousPath.mem_of_lt_exitTime D w _ h)]
  · rw [exitRate_of_exitTime_le (not_lt.1 h), exitRate_of_exitTime_le (not_lt.1 h)]

/-- For a rate continuous on the open set `D`, the exit rate is jointly Borel in the path and the time. -/
theorem measurable_exitRate_uncurry {D : Set ℂ} (hD : IsOpen D) {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ D) :
    Measurable fun p : ContinuousPath ℂ × ℝ => exitRate D ρ p.1 p.2 := by
  classical
  rw [← exitRate_piecewise D ρ]
  have hpw : Measurable (D.piecewise ρ fun _ => (1 : ℝ)) :=
    hρ.measurable_piecewise continuousOn_const hD.measurableSet
  have hev : Measurable fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal :=
    (ContinuousEval.continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hset : MeasurableSet {p : ContinuousPath ℂ × ℝ |
      ((p.2.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D p.1} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp (measurable_real_toNNReal.comp measurable_snd))
      ((ContinuousPath.measurable_exitTime D hD).comp measurable_fst)
  unfold exitRate
  exact Measurable.ite hset (hpw.comp hev) measurable_const

/-- For a rate continuous on the open set `D`, the exit-rate clock at a fixed time is Borel in the path. -/
theorem measurable_exitRateClock {D : Set ℂ} (hD : IsOpen D) {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ D) (s : ℝ≥0) :
    Measurable fun W : ContinuousPath ℂ => exitRateClock D ρ W s := by
  have h : (fun W : ContinuousPath ℂ => exitRateClock D ρ W s) =
      fun W => ∫ r, exitRate D ρ W r ∂(volume.restrict (Ioc (0 : ℝ) s)) := by
    funext W
    rw [exitRateClock, intervalIntegral.integral_of_le (NNReal.coe_nonneg s)]
  rw [h]
  exact ((measurable_exitRate_uncurry hD hρ).stronglyMeasurable.integral_prod_right').measurable

/-! ### The good set of paths -/

/-- The paths which leave `D` and along which the exit rate is locally integrable on `[0, ∞)`. -/
def exitRateGoodSet (D : Set ℂ) (ρ : ℂ → ℝ) : Set (ContinuousPath ℂ) :=
  {W | ContinuousPath.exitTime D W < ⊤} ∩
    ⋂ n : ℕ, {W | ∫⁻ r in Ioc (0 : ℝ) n, ‖exitRate D ρ W r‖ₑ < ⊤}

theorem measurableSet_exitRateGoodSet {D : Set ℂ} (hD : IsOpen D) {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ D) :
    MeasurableSet (exitRateGoodSet D ρ) := by
  refine (measurableSet_lt (ContinuousPath.measurable_exitTime D hD) measurable_const).inter ?_
  refine MeasurableSet.iInter fun n => ?_
  exact measurableSet_lt ((measurable_exitRate_uncurry hD hρ).enorm.lintegral_prod_right') measurable_const

theorem intervalIntegrable_exitRate_of_mem_exitRateGoodSet {D : Set ℂ} (hD : IsOpen D) {ρ : ℂ → ℝ}
    (hρ : ContinuousOn ρ D) {W : ContinuousPath ℂ} (hW : W ∈ exitRateGoodSet D ρ) (T : ℝ) :
    IntervalIntegrable (exitRate D ρ W) volume 0 T := by
  rcases le_total T 0 with hT | hT
  · exact intervalIntegrable_exitRate_of_nonpos D ρ W hT
  · obtain ⟨n, hn⟩ := exists_nat_ge T
    have hm : Measurable (exitRate D ρ W) :=
      (measurable_exitRate_uncurry hD hρ).comp measurable_prodMk_left
    have hI : IntegrableOn (exitRate D ρ W) (Ioc (0 : ℝ) n) :=
      ⟨hm.aestronglyMeasurable, mem_iInter.1 hW.2 n⟩
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact hI.mono_set (Ioc_subset_Ioc_right hn)

theorem isTimeChangeClock_exitRateClock_of_mem_exitRateGoodSet {D : Set ℂ} (hD : IsOpen D) {ρ : ℂ → ℝ}
    (hρ : ContinuousOn ρ D) (hρpos : ∀ v ∈ D, 0 < ρ v) {W : ContinuousPath ℂ} (hW : W ∈ exitRateGoodSet D ρ) :
    IsTimeChangeClock (exitRateClock D ρ W) :=
  isTimeChangeClock_exitRateClock hρpos (intervalIntegrable_exitRate_of_mem_exitRateGoodSet hD hρ hW) hW.1.ne

/-- **The time-changed path is almost everywhere measurable.** For a rate continuous and positive on the open set
`D`, and a law of paths carried by the good set, the path run with the exit-rate clock is almost everywhere
measurable (it is Borel on the good set, where all the clocks are time-change clocks). -/
theorem aemeasurable_lbmContinuousPath_exitRateClock {D : Set ℂ} (hD : IsOpen D) {ρ : ℂ → ℝ}
    (hρ : ContinuousOn ρ D) (hρpos : ∀ v ∈ D, 0 < ρ v) {μ : Measure (ContinuousPath ℂ)}
    (hμ : ∀ᵐ W ∂μ, W ∈ exitRateGoodSet D ρ) :
    AEMeasurable (lbmContinuousPath (exitRateClock D ρ)) μ := by
  classical
  set S := exitRateGoodSet D ρ
  have hSm : MeasurableSet S := measurableSet_exitRateGoodSet hD hρ
  have hgood : ∀ y : S, IsTimeChangeClock (exitRateClock D ρ y.1) :=
    fun y => isTimeChangeClock_exitRateClock_of_mem_exitRateGoodSet hD hρ hρpos y.2
  have hmS : Measurable fun y : S => lbmContinuousPath (exitRateClock D ρ) y.1 := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    have hinv : Measurable fun y : S => _root_.HarmonicBalls.clockInverse (exitRateClock D ρ y.1) t :=
      measurable_clockInverse_of_isTimeChangeClock hgood
        (fun s => (measurable_exitRateClock hD hρ s).comp measurable_subtype_coe) t
    have heq : (fun y : S => lbmContinuousPath (exitRateClock D ρ) y.1 t) =
        fun y : S => (y.1 : ContinuousPath ℂ) (_root_.HarmonicBalls.clockInverse (exitRateClock D ρ y.1) t) := by
      funext y
      rw [lbmContinuousPath_of_isTimeChangeClock (hgood y)]
      rfl
    rw [heq]
    exact (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp
      (measurable_subtype_coe.prodMk hinv)
  let f : ContinuousPath ℂ → ContinuousPath ℂ := S.piecewise (lbmContinuousPath (exitRateClock D ρ)) id
  have hf : Measurable f := by
    refine measurable_of_restrict_of_restrict_compl hSm ?_ ?_
    · have h : S.domRestrict f = fun y : S => lbmContinuousPath (exitRateClock D ρ) y.1 := by
        funext y
        exact piecewise_eq_of_mem _ _ _ y.2
      rw [h]
      exact hmS
    · have h : Sᶜ.domRestrict f = fun y : (Sᶜ : Set (ContinuousPath ℂ)) => y.1 := by
        funext y
        exact piecewise_eq_of_notMem _ _ _ y.2
      rw [h]
      exact measurable_subtype_coe
  refine ⟨f, hf, ?_⟩
  filter_upwards [hμ] with W hW
  exact (piecewise_eq_of_mem _ _ _ hW).symm

/-! ### Continuity of the conformal map and of the transported rate -/

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-- An inverse chart inverts its conformal map on the unit disc. -/
theorem IsInverseChart.apply_chartMap (hψ : IsInverseChart U z ψ) {v : ℂ} (hv : v ∈ Metric.ball (0 : ℂ) 1) :
    ψ (chartMap U ψ v) = v := by
  rw [← hψ.image_eq] at hv
  exact Function.invFunOn_eq hv

/-- A point of the closure of `U` mapped into the unit disc lies in `U`. -/
theorem IsInverseChart.mem_of_mem_closure (hψ : IsInverseChart U z ψ) (hU : IsOpen U) {x : ℂ}
    (hx : x ∈ closure U) (hψx : ψ x ∈ Metric.ball (0 : ℂ) 1) : x ∈ U := by
  by_contra hxU
  have hxf : x ∈ frontier U := by
    rw [hU.frontier_eq]
    exact ⟨hx, hxU⟩
  exact hψ.mapsTo_frontier hxf hψx

/-- **The conformal map is continuous on the unit disc.** The preimage of a closed set `C` under `φ` on the disc is
the trace on the disc of the compact set `ψ(C ∩ closure U)`. -/
theorem IsInverseChart.continuousOn_chartMap (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) : ContinuousOn (chartMap U ψ) (Metric.ball (0 : ℂ) 1) := by
  rw [continuousOn_iff_isClosed]
  intro C hC
  have hK : IsCompact (C ∩ closure U) := hUb.isCompact_closure.inter_left hC
  refine ⟨ψ '' (C ∩ closure U), (hK.image ψ.continuous).isClosed, ?_⟩
  ext v
  simp only [mem_inter_iff, mem_preimage, mem_image]
  constructor
  · rintro ⟨hvC, hv⟩
    exact ⟨⟨chartMap U ψ v, ⟨hvC, subset_closure (hψ.chartMap_mem hv)⟩, hψ.apply_chartMap hv⟩, hv⟩
  · rintro ⟨⟨x, ⟨hxC, hxK⟩, rfl⟩, hv⟩
    refine ⟨?_, hv⟩
    rw [hψ.chartMap_apply (hψ.mem_of_mem_closure hU hxK hv)]
    exact hxC

/-- The transported rate of a continuous rate is continuous on the unit disc. -/
theorem continuousOn_chartTransportRate (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {ρ : ℂ → ℝ} (hρ : Continuous ρ) :
    ContinuousOn (chartTransportRate U ψ ρ) (Metric.ball (0 : ℂ) 1) := by
  have hφ := hψ.continuousOn_chartMap hU hUb
  have hmaps : MapsTo (chartMap U ψ) (Metric.ball (0 : ℂ) 1) U := fun v hv => hψ.chartMap_mem hv
  have hdψ : ContinuousOn (deriv ψ) U := (hψ.differentiableOn.deriv hU).continuousOn
  show ContinuousOn (fun v => ρ (chartMap U ψ v) / ‖deriv ψ (chartMap U ψ v)‖ ^ 2) _
  refine (hρ.comp_continuousOn hφ).div ((hdψ.comp hφ hmaps).norm.pow 2) fun v hv => ?_
  exact pow_ne_zero 2 (norm_ne_zero_iff.2 (hψ.deriv_ne_zero hU (hψ.chartMap_mem hv)))

/-! ### The law identity for integral clocks -/

/-- Under Brownian motion from `w ∈ U` (with locally integrable conformal rate), the chart image `T b` lies almost
surely in the good set of the transported rate of a continuous positive rate. -/
theorem ae_mem_exitRateGoodSet_chartTransportRate (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {w : ℂ} (hw : w ∈ U)
    (hTm : AEMeasurable (fun b => chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))
      (planarBrownianMotion w))
    (hint : ∀ᵐ b ∂planarBrownianMotion w, ∀ T : ℝ, IntervalIntegrable (chartRate U ψ b) volume 0 T)
    {ρ : ℂ → ℝ} (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    ∀ᵐ W ∂(planarBrownianMotion w).map
        (fun b => chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)),
      W ∈ exitRateGoodSet (Metric.ball (0 : ℂ) 1) (chartTransportRate U ψ ρ) := by
  refine (ae_map_iff hTm (p := fun W => W ∈ exitRateGoodSet (Metric.ball (0 : ℂ) 1) (chartTransportRate U ψ ρ))
    (measurableSet_exitRateGoodSet Metric.isOpen_ball (continuousOn_chartTransportRate hψ hU hUb hρ))).2 ?_
  filter_upwards [ae_planarBrownianMotion_eval_zero w, ae_planarBrownianMotion_exit_all_bounded w, hint]
    with b hb0 hexit hb
  have hb0U : b 0 ∈ U := by
    rw [hb0]
    exact hw
  have hτ : ContinuousPath.exitTime U b = ((ContinuousPath.exitTime U b).toNNReal : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal (hexit U hUb).ne).symm
  have hA : IsTimeChangeClock (chartClock U ψ b) := isTimeChangeClock_chartClock hψ hU hb (hexit U hUb).ne
  refine ⟨?_, mem_iInter.2 fun n => ?_⟩
  · show ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1)
      (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) < ⊤
    rw [exitTime_chartStopPath_lbmContinuousPath hU hψ.mapsTo_ball hψ.mapsTo_frontier hA hb0U hτ]
    exact ENNReal.coe_lt_top
  · have hI := intervalIntegrable_exitRate_chartTransportRate hψ hU hb0U hτ hb hρ hρpos (n : ℝ)
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).1 hI).2

/-- **Law of the chart image for integral clocks, from Lévy's conformal invariance.** For an inverse chart `ψ` of
the bounded open set `U`, `w ∈ U`, a continuous positive rate `ρ` and time-change clocks
`F b t = ∫_0^t ρ(b_s) ds`: the chart image of Brownian motion from `w` run with the clock `F` and stopped at its exit
from `U` has the law of Brownian motion from `ψ(w)` stopped at its exit from the unit disc, run with the transported
clock of `ρ` and stopped at its exit from the disc. -/
theorem map_chartStopPath_lbmContinuousPath_integralClock_of_levy (hLevy : LevyConformalChartStmt)
    (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U) {w : ℂ} (hw : w ∈ U)
    {ρ : ℂ → ℝ} (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : ∀ b, IsTimeChangeClock (F b)) (hFρ : ∀ b t, F b t = ∫ s in (0 : ℝ)..(t : ℝ), ρ (b s.toNNReal)) :
    (planarBrownianMotion w).map (fun b => chartStopPath U ψ (lbmContinuousPath F b)) =
      ((planarBrownianMotion (ψ w)).map (stopAtExitTime (Metric.ball 0 1))).map
        (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1)
          (lbmContinuousPath (exitRateClock (Metric.ball (0 : ℂ) 1) (chartTransportRate U ψ ρ)) W)) := by
  obtain ⟨hint, hTm, hTmap⟩ := hLevy U z ψ hU hUb hψ w hw
  have hae := ae_mem_exitRateGoodSet_chartTransportRate hψ hU hUb hw hTm hint hρ hρpos
  rw [hTmap] at hae
  have hGm := (measurable_stopAtExitTime (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball).comp_aemeasurable
    (aemeasurable_lbmContinuousPath_exitRateClock (D := Metric.ball (0 : ℂ) 1) Metric.isOpen_ball
      (continuousOn_chartTransportRate hψ hU hUb hρ) (fun v hv => chartTransportRate_pos hψ hU hρpos hv) hae)
  exact map_chartStopPath_lbmContinuousPath_integralClock hψ hU hUb hw hTm hTmap hint hρ hρpos hF hFρ hGm

/-! ### The approximating LQG clock -/

/-- The rate `ε_n^{γ²/2} e^{γ h_{ε_n}} + ε_n` of the approximating LQG clock `lqgApproxClockPlus` at the dyadic
scale `ε_n = 2^{-n}`. -/
noncomputable def lqgApproxRate (γ : ℝ) (hε : ℝ → ℂ → ℝ) (n : ℕ) (y : ℂ) : ℝ :=
  dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale n) y) + dyadicScale n

section ApproxRate

variable {γ : ℝ} {hε : ℝ → ℂ → ℝ} {n : ℕ}

theorem continuous_lqgApproxRate (hcont : Continuous (hε (dyadicScale n))) : Continuous (lqgApproxRate γ hε n) :=
  (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcont))).add continuous_const

theorem lqgApproxRate_pos (y : ℂ) : 0 < lqgApproxRate γ hε n y :=
  add_pos_of_nonneg_of_pos
    (mul_nonneg (Real.rpow_nonneg (HarmonicBalls.dyadicScale_pos n).le _) (Real.exp_pos _).le)
    (HarmonicBalls.dyadicScale_pos n)

/-- The approximating LQG clock is the integral clock of `lqgApproxRate`. -/
theorem lqgApproxClockPlus_eq_integral (hcont : Continuous (hε (dyadicScale n))) (b : ContinuousPath ℂ)
    (t : ℝ≥0) :
    lqgApproxClockPlus γ hε n b t = ∫ s in (0 : ℝ)..(t : ℝ), lqgApproxRate γ hε n (b s.toNNReal) := by
  have hc : Continuous fun s : ℝ =>
      dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale n) (b s.toNNReal)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (hcont.comp (b.continuous.comp continuous_real_toNNReal))))
  simp only [lqgApproxRate]
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, lqgApproxClockPlus, lqgClockApprox,
    mul_comm (dyadicScale n) (t : ℝ)]

/-- **The chart image of the approximating Liouville Brownian motion, from Lévy's conformal invariance.** For an
inverse chart `ψ` of the bounded open set `U` and `w ∈ U`, the chart image of Brownian motion from `w` run with the
approximating LQG clock `A_n` and stopped at its exit from `U` has the law of Brownian motion from `ψ(w)` stopped at
its exit from the unit disc, run with the transported clock of the rate `ε_n^{γ²/2} e^{γ h_{ε_n}} + ε_n` (that is,
with rate `(ε_n^{γ²/2} e^{γ h_{ε_n}(φ v)} + ε_n) |φ'(v)|²` at `v`) and stopped at its exit from the disc. -/
theorem map_chartStopPath_lbmContinuousPath_lqgApproxClockPlus_of_levy (hLevy : LevyConformalChartStmt)
    (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U) {w : ℂ} (hw : w ∈ U)
    (hcont : Continuous (hε (dyadicScale n))) :
    (planarBrownianMotion w).map
        (fun b => chartStopPath U ψ (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)) =
      ((planarBrownianMotion (ψ w)).map (stopAtExitTime (Metric.ball 0 1))).map
        (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1)
          (lbmContinuousPath (exitRateClock (Metric.ball (0 : ℂ) 1)
            (chartTransportRate U ψ (lqgApproxRate γ hε n))) W)) :=
  map_chartStopPath_lbmContinuousPath_integralClock_of_levy hLevy hψ hU hUb hw (continuous_lqgApproxRate hcont)
    lqgApproxRate_pos (isTimeChangeClock_lqgApproxClockPlus hcont) (lqgApproxClockPlus_eq_integral hcont)

end ApproxRate

end MatedCRT
