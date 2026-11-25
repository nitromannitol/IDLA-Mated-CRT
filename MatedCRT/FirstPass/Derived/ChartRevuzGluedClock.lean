import MatedCRT.FirstPass.Derived.ChartRevuzClockComparison
import MatedCRT.FirstPass.Derived.DiscTimeChangeLaw

/-!
# The canonical disc time changes of the transported LQG measure and the chart image of the Liouville Brownian motion

Let `ψ` be an inverse chart of the bounded open set `U` at `z`, `A` the conformal clock and
`T b = ψ ∘ (b ∘ A_b⁻¹ stopped at its exit from U)` the chart image of planar Brownian motion `b` from `z`, which by
Lévy's conformal invariance (`LevyConformalChartStmt`) is Brownian motion from `0` stopped at its exit from the unit
disc. For a clock `G` of disc paths and a clock `F` of planar paths, the glued clock
`chartGluedClock U ψ G F b t = G(T b)(A_b(t ∧ τ)) + F b (t ∨ τ) - F b τ` (`τ` the exit time of `b` from `U`) runs the
pulled-back disc clock up to `τ` and the clock `F` afterwards; the chart image of `b` run with the glued clock is the
disc path `T b` run with `G` (`chartStopPath_lbmContinuousPath_chartGluedClock`).

For an LQG clock `F` of Brownian motion from `z` and `G = D_k` the exit-rate clock of the canonical rate
`g_k = discCanonicalRate k ν₀` of the image `ν₀ = ψ_*(μ|_U)` of the LQG measure, the glued clocks converge to `F` in
probability uniformly on compact time intervals (`tendsto_measure_exists_le_abs_chartGluedClock_sub`): before `τ` the
glued clock is `D_k(T b)(A_b t)`, the transported approximating clocks satisfy `C_n(T b)(A_b t) = A_n(b)(t)`
(the change of variables `exitRateClock_chartTransportRate_eq`), `C_n` and `D_k` are uniformly close in probability
(`tendsto_measure_exists_lt_abs_exitRateClock_chartTransportRate_sub`) and `A_n → F`. Hence the disc time-change laws
of the canonical rates `g_k` converge to the chart image of Brownian motion from `z` run with `F`
(`tendsto_integral_discTimeChangeLaw_discCanonicalRate`): the time change of killed disc Brownian motion by the
additive functional with Revuz measure `ν₀` (Fukushima–Oshima–Takeda (2011), §5.1, §6.2) is the chart image of the
Liouville Brownian motion (Berestycki (2015), Theorem 1.3).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Metric Topology MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT

/-! ### Glued clocks -/

/-- A time-change clock is nonnegative. -/
theorem isTimeChangeClock_nonneg {a : ℝ≥0 → ℝ} (ha : IsTimeChangeClock a) (t : ℝ≥0) : 0 ≤ a t := by
  simpa [ha.map_zero] using ha.strictMono.monotone (show 0 ≤ t from bot_le)

/-- A time-change clock evaluated at its inverse. -/
theorem apply_clockInverse_of_isTimeChangeClock {a : ℝ≥0 → ℝ} (ha : IsTimeChangeClock a) (σ : ℝ≥0) :
    a (_root_.HarmonicBalls.clockInverse a σ) = σ := by
  obtain ⟨u, hu⟩ := IsTimeChangeClock.surjective_toNNReal ha σ
  change Real.toNNReal (a u) = σ at hu
  subst hu
  rw [clockInverse_clockValue ha.map_zero ha.strictMono, Real.coe_toNNReal _ (isTimeChangeClock_nonneg ha u)]

/-- The glued clock `g(a(t ∧ τ)) + f(t ∨ τ) - f(τ)`: the clock `g` read through `a` up to the time `τ`, then the
increments of `f`. -/
noncomputable def glueClock (a g f : ℝ≥0 → ℝ) (τ : ℝ≥0) (t : ℝ≥0) : ℝ :=
  g (a (min t τ)).toNNReal + (f (max t τ) - f τ)

/-- The glued clock of three time-change clocks is a time-change clock. -/
theorem isTimeChangeClock_glueClock {a g f : ℝ≥0 → ℝ} (ha : IsTimeChangeClock a) (hg : IsTimeChangeClock g)
    (hf : IsTimeChangeClock f) (τ : ℝ≥0) : IsTimeChangeClock (glueClock a g f τ) where
  map_zero := by
    simp only [glueClock, min_eq_left (zero_le : (0 : ℝ≥0) ≤ τ), max_eq_right (zero_le : (0 : ℝ≥0) ≤ τ),
      ha.map_zero, Real.toNNReal_zero, hg.map_zero, sub_self, add_zero]
  continuous := by
    unfold glueClock
    exact (hg.continuous.comp (continuous_real_toNNReal.comp (ha.continuous.comp
      (continuous_id.min continuous_const)))).add
      ((hf.continuous.comp (continuous_id.max continuous_const)).sub continuous_const)
  strictMono := by
    intro s t hst
    unfold glueClock
    have hmono_g : Monotone fun u : ℝ≥0 => g (a (min u τ)).toNNReal := fun u v huv =>
      hg.strictMono.monotone (Real.toNNReal_le_toNNReal (ha.strictMono.monotone (min_le_min huv le_rfl)))
    have hmono_f : Monotone fun u : ℝ≥0 => f (max u τ) - f τ := fun u v huv =>
      sub_le_sub_right (hf.strictMono.monotone (max_le_max huv le_rfl)) _
    rcases lt_or_ge s τ with hsτ | hτs
    · have h1 : min s τ < min t τ := by
        rw [min_eq_left hsτ.le]
        exact lt_min hst hsτ
      have h2 : g (a (min s τ)).toNNReal < g (a (min t τ)).toNNReal := by
        refine hg.strictMono ?_
        exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (isTimeChangeClock_nonneg ha _)).2 (ha.strictMono h1)
      exact add_lt_add_of_lt_of_le h2 (hmono_f hst.le)
    · have h1 : max s τ < max t τ := by
        rw [max_eq_left hτs, max_eq_left (hτs.trans hst.le)]
        exact hst
      exact add_lt_add_of_le_of_lt (hmono_g hst.le) (sub_lt_sub_right (hf.strictMono h1) _)
  tendsto_atTop := by
    have h : (fun t => glueClock a g f τ t) =ᶠ[atTop] fun t => (g (a τ).toNNReal - f τ) + f t := by
      filter_upwards [eventually_ge_atTop τ] with t ht
      simp only [glueClock, min_eq_right ht, max_eq_left ht]
      ring
    exact (tendsto_atTop_add_const_left _ _ hf.tendsto_atTop).congr' h.symm

/-- Before `a τ`, the glued clock at the inverse of `a` is `g`. -/
theorem glueClock_clockInverse {a g f : ℝ≥0 → ℝ} (ha : IsTimeChangeClock a) {τ σ : ℝ≥0}
    (hσ : (σ : ℝ) ≤ a τ) : glueClock a g f τ (_root_.HarmonicBalls.clockInverse a σ) = g σ := by
  obtain ⟨u, hu⟩ := IsTimeChangeClock.surjective_toNNReal ha σ
  change Real.toNNReal (a u) = σ at hu
  subst hu
  rw [clockInverse_clockValue ha.map_zero ha.strictMono]
  have hu : u ≤ τ := by
    rw [Real.coe_toNNReal _ (isTimeChangeClock_nonneg ha u)] at hσ
    exact ha.strictMono.le_iff_le.1 hσ
  simp only [glueClock, min_eq_left hu, max_eq_right hu, sub_self, add_zero]

/-- The glued clock minus `f` only depends on the time `t ∧ τ`. -/
theorem glueClock_sub (a g f : ℝ≥0 → ℝ) (τ t : ℝ≥0) :
    glueClock a g f τ t - f t = g (a (min t τ)).toNNReal - f (min t τ) := by
  unfold glueClock
  rcases le_total t τ with h | h
  · rw [min_eq_left h, max_eq_right h]
    ring
  · rw [min_eq_right h, max_eq_left h]
    ring

/-! ### The glued clock of a chart -/

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-- **The glued clock of a chart.** For a clock `G` of disc paths and a clock `F` of planar paths, the clock of the
path `b` that runs `G` along the chart image `T b` of `b` (run with its conformal clock `A_b` and stopped at its exit
from `U`) read through `A_b` up to the exit time `τ` of `b` from `U`, and the increments of `F b` afterwards. -/
noncomputable def chartGluedClock (U : Set ℂ) (ψ : C(ℂ, ℂ)) (G F : ContinuousPath ℂ → ℝ≥0 → ℝ)
    (b : ContinuousPath ℂ) : ℝ≥0 → ℝ :=
  glueClock (chartClock U ψ b) (G (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))) (F b)
    (ContinuousPath.exitTime U b).toNNReal

theorem chartGluedClock_eq {G F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ} {τ : ℝ≥0}
    (hτ : ContinuousPath.exitTime U b = τ) :
    chartGluedClock U ψ G F b =
      glueClock (chartClock U ψ b) (G (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))) (F b) τ := by
  rw [chartGluedClock, hτ, ENNReal.toNNReal_coe]

/-- **The chart image of a path run with the glued clock.** If `b` starts in `U` and leaves it at the time `τ`, and
the conformal clock `A_b`, `F b` and `G (T b)` are time-change clocks, then the chart image of `b` run with the glued
clock and stopped at its exit from `U` is the chart image `T b` run with `G` and stopped at its exit from the disc. -/
theorem chartStopPath_lbmContinuousPath_chartGluedClock (hU : IsOpen U)
    (hψU : MapsTo ψ U (ball (0 : ℂ) 1)) (hψf : MapsTo ψ (frontier U) (ball (0 : ℂ) 1)ᶜ)
    {G F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ} (hA : IsTimeChangeClock (chartClock U ψ b))
    (hF : IsTimeChangeClock (F b)) (hb0 : b 0 ∈ U) {τ : ℝ≥0} (hτ : ContinuousPath.exitTime U b = τ)
    (hG : IsTimeChangeClock (G (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)))) :
    chartStopPath U ψ (lbmContinuousPath (chartGluedClock U ψ G F) b) =
      stopAtExitTime (ball (0 : ℂ) 1)
        (lbmContinuousPath G (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))) := by
  have hQ : IsTimeChangeClock (chartGluedClock U ψ G F b) := by
    rw [chartGluedClock_eq hτ]
    exact isTimeChangeClock_glueClock hA hG hF τ
  refine chartStopPath_lbmContinuousPath_eq (A := chartClock U ψ) hU hψU hψf hA hQ hb0 hτ hG fun σ hσ => ?_
  rw [chartGluedClock_eq hτ, glueClock_clockInverse hA hσ]

/-! ### The disc time-change laws of the canonical rates -/

/-- The disc time change by the canonical rate `g_k(ν)` (the time-changed path if the path leaves the disc, the path
itself otherwise), stopped at the exit from the disc, is a Borel function of the path. -/
theorem measurable_stopAtExitTime_exitRateTimeChange_discCanonicalRate (k : ℕ) (ν : Measure ℂ) :
    Measurable fun W => stopAtExitTime (ball (0 : ℂ) 1)
      (exitRateTimeChange (ball 0 1) (discCanonicalRate k) (ν, W)) :=
  (measurable_stopAtExitTime _ isOpen_ball).comp
    ((measurable_exitRateTimeChange isOpen_ball (measurable_discCanonicalRate k)
      (fun ν' v _ => discCanonicalRate_pos k ν' v)
      (fun ν' => ⟨_, fun v _ => abs_discCanonicalRate_le k ν' v⟩)).comp measurable_prodMk_left)

/-- The disc time-change law of a canonical rate is a probability measure. -/
theorem isProbabilityMeasure_discTimeChangeLaw_discCanonicalRate (k : ℕ) (ν : Measure ℂ) :
    IsProbabilityMeasure (discTimeChangeLaw (discCanonicalRate k ν)) := by
  have hP0 : IsProbabilityMeasure ((planarBrownianMotion 0).map (stopAtExitTime (ball (0 : ℂ) 1))) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_stopAtExitTime _ isOpen_ball).aemeasurable).2
      inferInstance
  rw [discTimeChangeLaw_eq_map_exitRateTimeChange (g := discCanonicalRate k) ν]
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_stopAtExitTime_exitRateTimeChange_discCanonicalRate k ν).aemeasurable).2 hP0

/-! ### Convergence of the glued clocks -/

section Convergence

variable {γ : ℝ} {hε : ℝ → ℂ → ℝ} {μ : Measure ℂ} {R₁ β t₀ : ℝ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}

/-- **The glued clocks of the canonical rates converge to the LQG clock in probability.** Let `ψ` be an inverse chart
of the bounded open set `U ⊆ B̄(0, R₁)` at `z`, `μ` the LQG limit of the approximations `μ_{ε_n}` (continuous at the
dyadic scales, with `μ_{ε_n}(B(x, t)) ≤ t^β` for all `n`, `x ∈ B̄(0, R₁)`, `t < t₀`), `F` an LQG clock of Brownian
motion from `z`, and `ν₀ = ψ_*(μ|_U)`. Assuming Lévy's conformal invariance, the glued clocks of the exit-rate clocks
of the canonical rates `g_k = discCanonicalRate k ν₀` and of `F` converge to `F` in probability uniformly on `[0, T]`. -/
theorem tendsto_measure_exists_le_abs_chartGluedClock_sub (hLevy : LevyConformalChartStmt)
    (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hμ : IsLQGLimit γ hε μ)
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) (hβ : 0 < β) (ht₀ : 0 < t₀) (hU₁ : U ⊆ closedBall 0 R₁)
    (hpow : ∀ n : ℕ, ∀ x ∈ closedBall (0 : ℂ) R₁, ∀ t, 0 < t → t < t₀ →
      lqgApprox γ hε (dyadicScale n) (ball x t) ≤ ENNReal.ofReal (t ^ β))
    (hF : IsLQGClock planarBrownianMotion γ hε z F) (T : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun k : ℕ => planarBrownianMotion z {b | ∃ t ≤ T, η ≤
      |chartGluedClock U ψ (exitRateClock (ball 0 1) (discCanonicalRate k ((μ.restrict U).map ψ))) F b t -
        F b t|}) atTop (𝓝 0) := by
  obtain ⟨hint, hTm, hTmap⟩ := hLevy U z ψ hU hUb hψ z hψ.mem
  rw [hψ.apply_point] at hTmap
  have hcmp := tendsto_measure_exists_lt_abs_exitRateClock_chartTransportRate_sub hψ hU hUb hμ hcont hβ ht₀ hU₁
    hpow hTm hTmap (half_pos hη)
  have hgood : ∀ᵐ b ∂planarBrownianMotion z, b 0 = z ∧ ContinuousPath.exitTime U b < ⊤ ∧
      ∀ T' : ℝ, IntervalIntegrable (chartRate U ψ b) volume 0 T' := by
    filter_upwards [ae_planarBrownianMotion_eval_zero z, ae_planarBrownianMotion_exit_all_bounded z, hint]
      with b h0 hex hb
    exact ⟨h0, hex U hUb, hb⟩
  have hbad := ae_iff.1 hgood
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.1 hcmp) (δ / 2) (ENNReal.half_pos hδ.ne')
  obtain ⟨M, hM⟩ := (ENNReal.tendsto_atTop_zero.1
      (MatedCRT.IsLQGClock.tendsto_measure_lqgApproxClockPlus hF T (half_pos hη)))
    (δ / 2) (ENNReal.half_pos hδ.ne')
  refine ⟨N.2, fun k hk => ?_⟩
  set n := max N.1 M with hn
  have hsub : {b | ∃ t ≤ T, η ≤
      |chartGluedClock U ψ (exitRateClock (ball 0 1) (discCanonicalRate k ((μ.restrict U).map ψ))) F b t -
        F b t|} ⊆
      {b | ¬ (b 0 = z ∧ ContinuousPath.exitTime U b < ⊤ ∧
        ∀ T' : ℝ, IntervalIntegrable (chartRate U ψ b) volume 0 T')} ∪
      {b | ∃ σ : ℝ≥0, η / 2 <
        |exitRateClock (ball 0 1) (chartTransportRate U ψ (lqgApproxRate γ hε n))
            (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) σ -
          exitRateClock (ball 0 1) (discCanonicalRate k ((μ.restrict U).map ψ))
            (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) σ|} ∪
      {b | ∃ t ≤ T, η / 2 ≤ |lqgApproxClockPlus γ hε n b t - F b t|} := by
    rintro b ⟨t, htT, ht⟩
    by_cases hg : b 0 = z ∧ ContinuousPath.exitTime U b < ⊤ ∧
        ∀ T' : ℝ, IntervalIntegrable (chartRate U ψ b) volume 0 T'
    swap
    · exact Or.inl (Or.inl hg)
    obtain ⟨hb0, hfin, hb⟩ := hg
    obtain ⟨τ, hτ⟩ : ∃ τ : ℝ≥0, ContinuousPath.exitTime U b = τ :=
      ⟨_, (ENNReal.coe_toNNReal hfin.ne).symm⟩
    have hA : IsTimeChangeClock (chartClock U ψ b) := isTimeChangeClock_chartClock hψ hU hb hfin.ne
    have hb0U : b 0 ∈ U := by
      rw [hb0]
      exact hψ.mem
    have hσ : (((chartClock U ψ b (min t τ)).toNNReal : ℝ≥0) : ℝ) ≤ chartClock U ψ b τ := by
      rw [Real.coe_toNNReal _ (isTimeChangeClock_nonneg hA _)]
      exact hA.strictMono.monotone (min_le_right t τ)
    have hC : exitRateClock (ball 0 1) (chartTransportRate U ψ (lqgApproxRate γ hε n))
        (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) (chartClock U ψ b (min t τ)).toNNReal =
        lqgApproxClockPlus γ hε n b (min t τ) := by
      rw [exitRateClock_chartTransportRate_eq hψ hU hb0U hτ hb _ hσ,
        clockInverse_clockValue hA.map_zero hA.strictMono, lqgApproxClockPlus_eq_integral (hcont n)]
    have hQ := glueClock_sub (chartClock U ψ b)
      (exitRateClock (ball 0 1) (discCanonicalRate k ((μ.restrict U).map ψ))
        (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))) (F b) τ t
    rw [← chartGluedClock_eq hτ] at hQ
    rw [hQ] at ht
    rcases lt_or_ge (η / 2)
        |exitRateClock (ball 0 1) (chartTransportRate U ψ (lqgApproxRate γ hε n))
            (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) (chartClock U ψ b (min t τ)).toNNReal -
          exitRateClock (ball 0 1) (discCanonicalRate k ((μ.restrict U).map ψ))
            (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))
            (chartClock U ψ b (min t τ)).toNNReal| with h1 | h1
    · exact Or.inl (Or.inr ⟨_, h1⟩)
    · refine Or.inr ⟨min t τ, (min_le_left t τ).trans htT, ?_⟩
      rw [hC] at h1
      have h2 := abs_sub_le
        (exitRateClock (ball 0 1) (discCanonicalRate k ((μ.restrict U).map ψ))
          (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) (chartClock U ψ b (min t τ)).toNNReal)
        (lqgApproxClockPlus γ hε n b (min t τ)) (F b (min t τ))
      rw [abs_sub_comm] at h1
      linarith
  calc planarBrownianMotion z {b | ∃ t ≤ T, η ≤
        |chartGluedClock U ψ (exitRateClock (ball 0 1) (discCanonicalRate k ((μ.restrict U).map ψ))) F b t -
          F b t|}
      ≤ planarBrownianMotion z ({b | ¬ (b 0 = z ∧ ContinuousPath.exitTime U b < ⊤ ∧
          ∀ T' : ℝ, IntervalIntegrable (chartRate U ψ b) volume 0 T')} ∪
        {b | ∃ σ : ℝ≥0, η / 2 <
          |exitRateClock (ball 0 1) (chartTransportRate U ψ (lqgApproxRate γ hε n))
              (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) σ -
            exitRateClock (ball 0 1) (discCanonicalRate k ((μ.restrict U).map ψ))
              (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) σ|} ∪
        {b | ∃ t ≤ T, η / 2 ≤ |lqgApproxClockPlus γ hε n b t - F b t|}) := measure_mono hsub
    _ ≤ planarBrownianMotion z {b | ¬ (b 0 = z ∧ ContinuousPath.exitTime U b < ⊤ ∧
          ∀ T' : ℝ, IntervalIntegrable (chartRate U ψ b) volume 0 T')} +
        planarBrownianMotion z {b | ∃ σ : ℝ≥0, η / 2 <
          |exitRateClock (ball 0 1) (chartTransportRate U ψ (lqgApproxRate γ hε n))
              (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) σ -
            exitRateClock (ball 0 1) (discCanonicalRate k ((μ.restrict U).map ψ))
              (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) σ|} +
        planarBrownianMotion z {b | ∃ t ≤ T, η / 2 ≤ |lqgApproxClockPlus γ hε n b t - F b t|} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ 0 + δ / 2 + δ / 2 := by
        rw [hbad]
        exact add_le_add (add_le_add le_rfl (hN (n, k) (Prod.le_def.2 ⟨le_max_left _ _, hk⟩)))
          (hM n (le_max_right _ _))
    _ = δ := by rw [zero_add, ENNReal.add_halves]

/-- **The disc time-change laws of the canonical rates of `ψ_*(μ|_U)` converge to the chart image of the Liouville
Brownian motion.** Under the hypotheses of `tendsto_measure_exists_le_abs_chartGluedClock_sub`, for an LQG clock `F`
of Brownian motion from `z` which is almost surely a time-change clock and every bounded continuous `f` on paths,
`∫ f d(discTimeChangeLaw g_k) → E_z[f(ψ ∘ (b ∘ F(b)⁻¹ stopped at its exit from U))]`. -/
theorem tendsto_integral_discTimeChangeLaw_discCanonicalRate (hLevy : LevyConformalChartStmt)
    (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hμ : IsLQGLimit γ hε μ)
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) (hβ : 0 < β) (ht₀ : 0 < t₀) (hU₁ : U ⊆ closedBall 0 R₁)
    (hpow : ∀ n : ℕ, ∀ x ∈ closedBall (0 : ℂ) R₁, ∀ t, 0 < t → t < t₀ →
      lqgApprox γ hε (dyadicScale n) (ball x t) ≤ ENNReal.ofReal (t ^ β))
    (hF : IsLQGClock planarBrownianMotion γ hε z F)
    (hFc : ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b)) (f : ContinuousPath ℂ →ᵇ ℝ) :
    Tendsto (fun k : ℕ => ∫ W, f W ∂discTimeChangeLaw (discCanonicalRate k ((μ.restrict U).map ψ))) atTop
      (𝓝 (∫ b, f (chartStopPath U ψ (lbmContinuousPath F b)) ∂planarBrownianMotion z)) := by
  obtain ⟨hint, hTm, hTmap⟩ := hLevy U z ψ hU hUb hψ z hψ.mem
  rw [hψ.apply_point] at hTmap
  have hΦ := fun k : ℕ =>
    measurable_stopAtExitTime_exitRateTimeChange_discCanonicalRate k ((μ.restrict U).map ψ)
  have hint_eq : ∀ k : ℕ, ∫ W, f W ∂discTimeChangeLaw (discCanonicalRate k ((μ.restrict U).map ψ)) =
      ∫ b, f (stopAtExitTime (ball (0 : ℂ) 1) (exitRateTimeChange (ball 0 1) (discCanonicalRate k)
        ((μ.restrict U).map ψ, chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))))
        ∂planarBrownianMotion z := by
    intro k
    rw [discTimeChangeLaw_eq_map_exitRateTimeChange (g := discCanonicalRate k) ((μ.restrict U).map ψ),
      integral_map (hΦ k).aemeasurable f.continuous.aestronglyMeasurable, ← hTmap]
    exact integral_map hTm (f.continuous.measurable.comp (hΦ k)).aestronglyMeasurable
  refine Tendsto.congr (fun k => (hint_eq k).symm) ?_
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨φ, -, hae⟩ := exists_strictMono_ae_forall_eventually_close (planarBrownianMotion z)
    (fun j b t => chartGluedClock U ψ
      (exitRateClock (ball 0 1) (discCanonicalRate (ns j) ((μ.restrict U).map ψ))) F b t) F
    (fun T η hη => (tendsto_measure_exists_le_abs_chartGluedClock_sub hLevy hψ hU hUb hμ hcont hβ ht₀ hU₁
      hpow hF T hη).comp hns)
  refine ⟨φ, ?_⟩
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    (fun j => ((f.continuous.measurable.comp (hΦ (ns (φ j)))).comp_aemeasurable hTm).aestronglyMeasurable)
    (integrable_const _) (fun j => ae_of_all _ fun b => f.norm_coe_le_norm _) ?_
  filter_upwards [hae, hFc, ae_planarBrownianMotion_eval_zero z, ae_planarBrownianMotion_exit_all_bounded z,
    hint] with b hb hFb hb0 hexit hbi
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ≥0, ContinuousPath.exitTime U b = τ :=
    ⟨_, (ENNReal.coe_toNNReal (hexit U hUb).ne).symm⟩
  have hA : IsTimeChangeClock (chartClock U ψ b) := isTimeChangeClock_chartClock hψ hU hbi (hexit U hUb).ne
  have hb0U : b 0 ∈ U := by
    rw [hb0]
    exact hψ.mem
  have hTexit : ContinuousPath.exitTime (ball (0 : ℂ) 1)
      (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b)) < ⊤ := by
    rw [exitTime_chartStopPath_lbmContinuousPath hU hψ.mapsTo_ball hψ.mapsTo_frontier hA hb0U hτ]
    exact ENNReal.coe_lt_top
  have hD : ∀ k : ℕ, IsTimeChangeClock (exitRateClock (ball 0 1)
      (discCanonicalRate k ((μ.restrict U).map ψ)) (chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))) :=
    fun k => isTimeChangeClock_exitRateClock_of_bounded isOpen_ball (measurable_discCanonicalRate k)
      (fun ν v _ => discCanonicalRate_pos k ν v) (fun ν => ⟨_, fun v _ => abs_discCanonicalRate_le k ν v⟩)
      ((μ.restrict U).map ψ) hTexit
  have hQ : ∀ k : ℕ, IsTimeChangeClock (chartGluedClock U ψ
      (exitRateClock (ball 0 1) (discCanonicalRate k ((μ.restrict U).map ψ))) F b) := by
    intro k
    rw [chartGluedClock_eq hτ]
    exact isTimeChangeClock_glueClock hA (hD k) hFb τ
  have heq : ∀ k : ℕ, stopAtExitTime (ball (0 : ℂ) 1) (exitRateTimeChange (ball 0 1) (discCanonicalRate k)
      ((μ.restrict U).map ψ, chartStopPath U ψ (lbmContinuousPath (chartClock U ψ) b))) =
      chartStopPath U ψ (lbmContinuousPath (chartGluedClock U ψ
        (exitRateClock (ball 0 1) (discCanonicalRate k ((μ.restrict U).map ψ))) F) b) := by
    intro k
    rw [chartStopPath_lbmContinuousPath_chartGluedClock hU hψ.mapsTo_ball hψ.mapsTo_frontier hA hFb hb0U hτ
      (hD k)]
    simp only [exitRateTimeChange, hTexit, ↓reduceIte]
  simp only [heq]
  exact (f.continuous.tendsto _).comp (tendsto_chartStopPath_lbmContinuousPath
    (Fs := fun j => chartGluedClock U ψ
      (exitRateClock (ball 0 1) (discCanonicalRate (ns (φ j)) ((μ.restrict U).map ψ))) F)
    (fun j => hQ (ns (φ j))) hFb hτ hb)

end Convergence

end MatedCRT
