import MatedCRT.FirstPass.Derived.ChartLimitTransport
import MatedCRT.FirstPass.Derived.ProbabilityMeasurePolish

/-!
# The time change of Brownian motion in the unit disc by a rate, and its measurability in the rate

For a rate `g` on the unit disc `𝔻`, `discTimeChangeLaw g` is the law of planar Brownian motion from `0` stopped at its
exit from `𝔻`, run with the exit-rate clock `σ ↦ ∫_0^σ g(W_r) dr` (rate `g` before the exit from `𝔻`, unit rate
afterwards) and stopped at its exit from `𝔻`: the time change of Brownian motion killed on exiting `𝔻` by the
additive functional of density `g`. The transported approximating laws of the chart images of the Liouville Brownian
motion are of this form (`chartTransportApproxLaw_zero_eq_discTimeChangeLaw`).

For a family `g x` of rates, jointly Borel in the parameter `x` and the point, positive and bounded on `𝔻`, the path
run with the clock of `g x` is jointly Borel in `x` and the path on the paths which leave `𝔻`
(`measurable_exitRateTimeChange`), and the law `discTimeChangeProbLaw (g x)` is a Borel function of `x`
(`measurable_discTimeChangeProbLaw`). This gives the Borel dependence on the Revuz measure of the time change of killed
Brownian motion (Fukushima–Oshima–Takeda (2011), §6.2) through its approximations by absolutely continuous additive
functionals.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT

/-- **The time change of Brownian motion in the unit disc with rate `g`.** The law of planar Brownian motion from `0`
stopped at its exit from the unit disc, run with the exit-rate clock of `g` and stopped at its exit from the disc. -/
noncomputable def discTimeChangeLaw (g : ℂ → ℝ) : Measure (ContinuousPath ℂ) :=
  ((planarBrownianMotion 0).map (stopAtExitTime (Metric.ball 0 1))).map
    (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1)
      (lbmContinuousPath (exitRateClock (Metric.ball (0 : ℂ) 1) g) W))

/-- The transported approximating law from the center of the chart is the disc time-change law of the transported
rate. -/
theorem chartTransportApproxLaw_zero_eq_discTimeChangeLaw (γ : ℝ) (hε : ℝ → ℂ → ℝ) (n : ℕ) (U : Set ℂ)
    (ψ : C(ℂ, ℂ)) :
    chartTransportApproxLaw γ hε n U ψ 0 = discTimeChangeLaw (chartTransportRate U ψ (lqgApproxRate γ hε n)) :=
  rfl

open Classical in
/-- The disc time-change law as a law of paths (the law of the stopped disc Brownian motion if `discTimeChangeLaw g`
is not a probability measure). -/
noncomputable def discTimeChangeProbLaw (g : ℂ → ℝ) : ProbabilityMeasure (ContinuousPath ℂ) :=
  if h : IsProbabilityMeasure (discTimeChangeLaw g) then ⟨discTimeChangeLaw g, h⟩
  else ⟨planarBrownianMotion 0, inferInstance⟩

theorem discTimeChangeProbLaw_eq {g : ℂ → ℝ} (h : IsProbabilityMeasure (discTimeChangeLaw g)) :
    discTimeChangeProbLaw g = ⟨discTimeChangeLaw g, h⟩ := by
  unfold discTimeChangeProbLaw
  exact dite_eq_left_of_eq_true (eq_true h)

theorem discTimeChangeProbLaw_coe {g : ℂ → ℝ} (h : IsProbabilityMeasure (discTimeChangeLaw g)) :
    (discTimeChangeProbLaw g : Measure (ContinuousPath ℂ)) = discTimeChangeLaw g := by
  rw [discTimeChangeProbLaw_eq h]
  rfl

/-- Brownian motion from `0` stopped at its exit from the unit disc leaves the disc almost surely. -/
theorem ae_exitTime_stopAtExitTime_lt_top :
    ∀ᵐ W ∂(planarBrownianMotion 0).map (stopAtExitTime (Metric.ball 0 1)),
      ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) W < ⊤ := by
  refine (ae_map_iff (measurable_stopAtExitTime _ Metric.isOpen_ball).aemeasurable
    (p := fun W => ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) W < ⊤)
    (measurableSet_lt (ContinuousPath.measurable_exitTime _ Metric.isOpen_ball) measurable_const)).2 ?_
  filter_upwards [ae_planarBrownianMotion_eval_zero 0, ae_planarBrownianMotion_exit_all_bounded 0]
    with b hb0 hexit
  have hfin := hexit (Metric.ball 0 1) Metric.isBounded_ball
  have hfr := ContinuousPath.coordinate_exitTime_mem_frontier (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball b
    (by rw [hb0]; exact Metric.mem_ball_self one_pos) hfin.ne
  rw [Metric.isOpen_ball.frontier_eq] at hfr
  refine lt_of_le_of_lt (ContinuousPath.exitTime_le_of_notMem _ _
    (ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) b).toNNReal ?_) ENNReal.coe_lt_top
  simp only [stopAtExitTime, ContinuousMap.comp_apply, exitClamp_apply, hfin.ne, ↓reduceIte, min_self]
  exact hfr.2

/-! ### Families of rates -/

section Param

variable {X : Type*} [MeasurableSpace X] {D : Set ℂ} {g : X → ℂ → ℝ}

/-- For a jointly Borel family of rates, the exit rate is jointly Borel in the parameter, the path and the time. -/
theorem measurable_exitRate_param (hD : IsOpen D) (hg : Measurable (Function.uncurry g)) :
    Measurable fun p : (X × ContinuousPath ℂ) × ℝ => exitRate D (g p.1.1) p.1.2 p.2 := by
  have hev0 : Measurable fun q : ContinuousPath ℂ × ℝ => q.1 q.2.toNNReal :=
    (ContinuousEval.continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hev : Measurable fun p : (X × ContinuousPath ℂ) × ℝ => p.1.2 p.2.toNNReal :=
    hev0.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hval : Measurable fun p : (X × ContinuousPath ℂ) × ℝ => g p.1.1 (p.1.2 p.2.toNNReal) :=
    hg.comp ((measurable_fst.comp measurable_fst).prodMk hev)
  have hset : MeasurableSet {p : (X × ContinuousPath ℂ) × ℝ |
      ((p.2.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D p.1.2} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp (measurable_real_toNNReal.comp measurable_snd))
      ((ContinuousPath.measurable_exitTime D hD).comp (measurable_snd.comp measurable_fst))
  unfold exitRate
  exact Measurable.ite hset hval measurable_const

/-- For a jointly Borel family of rates, the exit-rate clock at a fixed time is jointly Borel in the parameter and
the path. -/
theorem measurable_exitRateClock_param (hD : IsOpen D) (hg : Measurable (Function.uncurry g)) (s : ℝ≥0) :
    Measurable fun p : X × ContinuousPath ℂ => exitRateClock D (g p.1) p.2 s := by
  have h : (fun p : X × ContinuousPath ℂ => exitRateClock D (g p.1) p.2 s) =
      fun p => ∫ r, exitRate D (g p.1) p.2 r ∂(volume.restrict (Ioc (0 : ℝ) s)) := by
    funext p
    rw [exitRateClock, intervalIntegral.integral_of_le (NNReal.coe_nonneg s)]
  rw [h]
  exact ((measurable_exitRate_param hD hg).stronglyMeasurable.integral_prod_right').measurable

/-- A rate bounded on `D` has a bounded exit rate. -/
theorem abs_exitRate_le {ρ : ℂ → ℝ} {C : ℝ} (hC : ∀ v ∈ D, |ρ v| ≤ C) (w : ContinuousPath ℂ) (r : ℝ) :
    |exitRate D ρ w r| ≤ max C 1 := by
  by_cases h : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D w
  · rw [exitRate_of_lt_exitTime h]
    exact (hC _ (ContinuousPath.mem_of_lt_exitTime D w _ h)).trans (le_max_left _ _)
  · rw [exitRate_of_exitTime_le (not_lt.1 h), abs_one]
    exact le_max_right _ _

/-- For a positive rate bounded on the open set `D`, the exit-rate clock along a path which leaves `D` is a
time-change clock. -/
theorem isTimeChangeClock_exitRateClock_of_bounded (hD : IsOpen D) (hg : Measurable (Function.uncurry g))
    (hpos : ∀ x, ∀ v ∈ D, 0 < g x v) (hbd : ∀ x, ∃ C, ∀ v ∈ D, |g x v| ≤ C) (x : X)
    {W : ContinuousPath ℂ} (hW : ContinuousPath.exitTime D W < ⊤) :
    IsTimeChangeClock (exitRateClock D (g x) W) := by
  obtain ⟨C, hC⟩ := hbd x
  have hm : Measurable (exitRate D (g x) W) :=
    (measurable_exitRate_param hD hg).comp (measurable_prodMk_left (x := (x, W)))
  refine isTimeChangeClock_exitRateClock (hpos x) (fun T => ?_) hW.ne
  refine (intervalIntegrable_const (c := max C 1)).mono_fun hm.aestronglyMeasurable
    (ae_of_all _ fun r => ?_)
  simp only [Real.norm_eq_abs]
  exact (abs_exitRate_le hC W r).trans (le_abs_self _)

open Classical in
/-- The path `W` run with the exit-rate clock of `g x` if `W` leaves `D`, and `W` itself otherwise. -/
noncomputable def exitRateTimeChange (D : Set ℂ) (g : X → ℂ → ℝ) (p : X × ContinuousPath ℂ) : ContinuousPath ℂ :=
  if ContinuousPath.exitTime D p.2 < ⊤ then lbmContinuousPath (exitRateClock D (g p.1)) p.2 else p.2

/-- **The time-changed path is jointly Borel in the rate parameter and the path.** -/
theorem measurable_exitRateTimeChange (hD : IsOpen D) (hg : Measurable (Function.uncurry g))
    (hpos : ∀ x, ∀ v ∈ D, 0 < g x v) (hbd : ∀ x, ∃ C, ∀ v ∈ D, |g x v| ≤ C) :
    Measurable (exitRateTimeChange D g) := by
  set S : Set (X × ContinuousPath ℂ) := {p | ContinuousPath.exitTime D p.2 < ⊤}
  have hSm : MeasurableSet S :=
    measurableSet_lt ((ContinuousPath.measurable_exitTime D hD).comp measurable_snd) measurable_const
  have hgood : ∀ y : S, IsTimeChangeClock (exitRateClock D (g y.1.1) y.1.2) :=
    fun y => isTimeChangeClock_exitRateClock_of_bounded hD hg hpos hbd y.1.1 y.2
  refine measurable_of_restrict_of_restrict_compl hSm ?_ ?_
  · have h : S.domRestrict (exitRateTimeChange D g) =
        fun y : S => lbmContinuousPath (exitRateClock D (g y.1.1)) y.1.2 := by
      funext y
      simp only [Set.domRestrict_apply, exitRateTimeChange,
        show ContinuousPath.exitTime D (y : X × ContinuousPath ℂ).2 < ⊤ from y.2, ↓reduceIte]
    rw [h]
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    have hinv : Measurable fun y : S =>
        _root_.HarmonicBalls.clockInverse (exitRateClock D (g y.1.1) y.1.2) t :=
      measurable_clockInverse_of_isTimeChangeClock hgood
        (fun s => (measurable_exitRateClock_param hD hg s).comp measurable_subtype_coe) t
    have heq : (fun y : S => lbmContinuousPath (exitRateClock D (g y.1.1)) y.1.2 t) =
        fun y : S => (y.1.2 : ContinuousPath ℂ)
          (_root_.HarmonicBalls.clockInverse (exitRateClock D (g y.1.1) y.1.2) t) := by
      funext y
      rw [lbmContinuousPath_of_isTimeChangeClock (hgood y)]
      rfl
    rw [heq]
    exact (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp
      ((measurable_snd.comp measurable_subtype_coe).prodMk hinv)
  · have h : Sᶜ.domRestrict (exitRateTimeChange D g) = fun y : (Sᶜ : Set (X × ContinuousPath ℂ)) => y.1.2 := by
      funext y
      simp only [Set.domRestrict_apply, exitRateTimeChange,
        show ¬ ContinuousPath.exitTime D (y : X × ContinuousPath ℂ).2 < ⊤ from y.2, ↓reduceIte]
    rw [h]
    exact measurable_snd.comp measurable_subtype_coe

omit [MeasurableSpace X] in
/-- The disc time-change law of `g x` is the image of the stopped disc Brownian motion under the jointly Borel time
change `exitRateTimeChange` (they agree on the paths which leave the disc). -/
theorem discTimeChangeLaw_eq_map_exitRateTimeChange (x : X) :
    discTimeChangeLaw (g x) = ((planarBrownianMotion 0).map (stopAtExitTime (Metric.ball 0 1))).map
      (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1) (exitRateTimeChange (Metric.ball 0 1) g (x, W))) := by
  refine Measure.map_congr ?_
  filter_upwards [ae_exitTime_stopAtExitTime_lt_top] with W hW
  show stopAtExitTime (Metric.ball (0 : ℂ) 1)
      (lbmContinuousPath (exitRateClock (Metric.ball (0 : ℂ) 1) (g x)) W) =
    stopAtExitTime (Metric.ball (0 : ℂ) 1) (exitRateTimeChange (Metric.ball 0 1) g (x, W))
  simp only [exitRateTimeChange, hW, ↓reduceIte]

/-- **The disc time-change law is a Borel function of the rate parameter.** For a family of rates jointly Borel in
the parameter and the point, positive and bounded on the unit disc, `x ↦ discTimeChangeProbLaw (g x)` is Borel. -/
theorem measurable_discTimeChangeProbLaw (hg : Measurable (Function.uncurry g))
    (hpos : ∀ x, ∀ v ∈ Metric.ball (0 : ℂ) 1, 0 < g x v)
    (hbd : ∀ x, ∃ C, ∀ v ∈ Metric.ball (0 : ℂ) 1, |g x v| ≤ C) :
    Measurable fun x => discTimeChangeProbLaw (g x) := by
  set μ₀ := (planarBrownianMotion 0).map (stopAtExitTime (Metric.ball (0 : ℂ) 1))
  have hstop := measurable_stopAtExitTime (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball
  have hμ₀P : IsProbabilityMeasure μ₀ :=
    (Measure.isProbabilityMeasure_map_iff hstop.aemeasurable).mpr inferInstance
  have hΦ : Measurable fun p : X × ContinuousPath ℂ =>
      stopAtExitTime (Metric.ball (0 : ℂ) 1) (exitRateTimeChange (Metric.ball 0 1) g p) :=
    hstop.comp (measurable_exitRateTimeChange Metric.isOpen_ball hg hpos hbd)
  have hP : ∀ x, IsProbabilityMeasure (discTimeChangeLaw (g x)) := fun x => by
    rw [discTimeChangeLaw_eq_map_exitRateTimeChange x]
    exact (Measure.isProbabilityMeasure_map_iff (hΦ.comp measurable_prodMk_left).aemeasurable).mpr hμ₀P
  have hcoe : (fun x => discTimeChangeLaw (g x)) =
      fun x => μ₀.map (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1)
        (exitRateTimeChange (Metric.ball 0 1) g (x, W))) := by
    funext x
    rw [discTimeChangeLaw_eq_map_exitRateTimeChange x]
  have hmeas : Measurable fun x => discTimeChangeLaw (g x) := by
    rw [hcoe]
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have hset : MeasurableSet ((fun p : X × ContinuousPath ℂ =>
        stopAtExitTime (Metric.ball (0 : ℂ) 1) (exitRateTimeChange (Metric.ball 0 1) g p)) ⁻¹' A) := hΦ hA
    have h : (fun x => μ₀.map (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1)
        (exitRateTimeChange (Metric.ball 0 1) g (x, W))) A) =
        fun x => μ₀ (Prod.mk x ⁻¹' ((fun p : X × ContinuousPath ℂ =>
          stopAtExitTime (Metric.ball (0 : ℂ) 1) (exitRateTimeChange (Metric.ball 0 1) g p)) ⁻¹' A)) := by
      funext x
      exact Measure.map_apply (hΦ.comp measurable_prodMk_left) hA
    rw [h]
    exact measurable_measure_prodMk_left hset
  have heq : (fun x => discTimeChangeProbLaw (g x)) =
      fun x => (⟨discTimeChangeLaw (g x), hP x⟩ : ProbabilityMeasure (ContinuousPath ℂ)) := by
    funext x
    exact discTimeChangeProbLaw_eq (hP x)
  rw [heq]
  exact Measurable.subtype_mk hmeas

end Param

end MatedCRT
