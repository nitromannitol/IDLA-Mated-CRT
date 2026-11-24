import MatedCRT.FirstPass.Derived.ChartTransportMeasurable
import MatedCRT.FirstPass.Derived.LQGApproxPathKernel
import MatedCRT.FirstPass.Derived.PlanarBrownianBoundedExit
import MatedCRT.Proofs.LBM.TimeChangeContinuity
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxClockSubsequence
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ClockInverseUniform

/-!
# The chart image of Liouville Brownian motion as a limit of transported approximations

Step P4 of the Revuz route to Berestycki (2015), Theorem 1.3, for the Liouville Brownian motion of the repository.

* `tendsto_chartStopPath_lbmContinuousPath`: if the clocks `F_i b` converge to the time-change clock `F b` uniformly
  on compact time intervals, the chart images of `b` run with the clocks `F_i` and stopped at the exit from `U`
  converge in the compact-open topology. The chart image at time `σ` is `ψ(b(min(F_i⁻¹ σ, τ_U)))`, with the exit time
  `τ_U` read off the Brownian path `b` itself, so no continuity of exit times is needed.
* `chartTransportApproxLaw`: the law of Brownian motion from `v` stopped at its exit from the unit disc, run with the
  transported approximating LQG clock (rate `(ε_n^{γ²/2} e^{γ h_{ε_n}(φ x)} + ε_n) |φ'(x)|²` at `x`, with
  `φ = chartMap U ψ`) and stopped at its exit from the disc.
* `tendsto_integral_chartTransportApproxLaw_of_levy`: from Lévy's conformal invariance, for an LQG clock `F` of
  Brownian motion from `w` (`IsLQGClock`, almost surely a time-change clock), the bounded continuous tests of the
  transported approximating laws from `ψ(w)` converge to those of the chart image of Brownian motion from `w` run with
  the clock `F` and stopped at its exit from `U`.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-! ### Pathwise convergence of the chart images -/

/-- **Convergence of the chart images under convergence of the clocks.** Let the path `b` leave `U` at the time `τ`,
and let the time-change clocks `F_i b` converge to the time-change clock `F b` uniformly on every `[0, T]`. Then the
chart images of `b` run with the clocks `F_i` and stopped at the exit from `U` converge, in the compact-open topology,
to the chart image of `b` run with the clock `F` and stopped at the exit from `U`. -/
theorem tendsto_chartStopPath_lbmContinuousPath {ι : Type*} {l : Filter ι}
    {Fs : ι → ContinuousPath ℂ → ℝ≥0 → ℝ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ}
    (hFs : ∀ i, IsTimeChangeClock (Fs i b)) (hF : IsTimeChangeClock (F b))
    {τ : ℝ≥0} (hτ : ContinuousPath.exitTime U b = τ)
    (hconv : ∀ (T : ℝ≥0) (η : ℝ), 0 < η → ∀ᶠ i in l, ∀ t ≤ T, |Fs i b t - F b t| < η) :
    Tendsto (fun i => chartStopPath U ψ (lbmContinuousPath (Fs i) b)) l
      (𝓝 (chartStopPath U ψ (lbmContinuousPath F b))) := by
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly, tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨T, hT⟩ := hK.bddAbove
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set S : ℝ≥0 := _root_.HarmonicBalls.clockInverse (F b) T + 1 with hS
  have hh : Continuous fun s : ℝ≥0 => ψ (b (min s τ)) :=
    ψ.continuous.comp (b.continuous.comp (continuous_id.min continuous_const))
  obtain ⟨δ, hδ, hδh⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ≥0)) (b := S)).uniformContinuousOn_of_continuous hh.continuousOn) ε hε
  have hinv := clockInverse_tendsto_uniform (l := l) (F := fun i => Fs i b) hF (fun i => (hFs i).strictMono) T
    (Eventually.of_forall fun i u _ => ((hFs i).tendsto_atTop.eventually_gt_atTop (u : ℝ)).exists)
    hconv (min δ 1) (lt_min hδ one_pos)
  filter_upwards [hinv] with i hi σ hσ
  have hσT : σ ≤ T := hT hσ
  have hd : |((_root_.HarmonicBalls.clockInverse (Fs i b) σ : ℝ≥0) : ℝ) -
      ((_root_.HarmonicBalls.clockInverse (F b) σ : ℝ≥0) : ℝ)| < min δ 1 := hi σ hσT
  have hc : _root_.HarmonicBalls.clockInverse (F b) σ ≤ _root_.HarmonicBalls.clockInverse (F b) T :=
    (IsTimeChangeClock.strictMono_clockInverse hF).monotone hσT
  have hc' : ((_root_.HarmonicBalls.clockInverse (F b) σ : ℝ≥0) : ℝ) ≤
      ((_root_.HarmonicBalls.clockInverse (F b) T : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 hc
  have hlt : ((_root_.HarmonicBalls.clockInverse (Fs i b) σ : ℝ≥0) : ℝ) -
      ((_root_.HarmonicBalls.clockInverse (F b) σ : ℝ≥0) : ℝ) < min δ 1 := (abs_lt.1 hd).2
  have hmin : min δ 1 ≤ 1 := min_le_right δ 1
  simp only [chartStopPath_lbmContinuousPath_apply hF hτ, chartStopPath_lbmContinuousPath_apply (hFs i) hτ]
  refine hδh _ ⟨zero_le, ?_⟩ _ ⟨zero_le, ?_⟩ ?_
  · rw [hS]
    exact hc.trans (le_add_of_nonneg_right zero_le)
  · rw [hS, ← NNReal.coe_le_coe, NNReal.coe_add, NNReal.coe_one]
    linarith
  · rw [NNReal.dist_eq, abs_sub_comm]
    exact hd.trans_le (min_le_left _ _)

/-! ### Convergence of the chart images of the approximating Liouville Brownian motions -/

section Approx

variable {γ : ℝ} {hε : ℝ → ℂ → ℝ}

/-- **Bounded continuous tests of the chart images converge.** Let `F` be an LQG clock of planar Brownian motion from
`w` (`IsLQGClock`) that is almost surely a time-change clock, for circle averages continuous at every dyadic radius,
and let `U` be a bounded open set. Then for every bounded continuous `f` on paths,
`E_w[f(ψ ∘ (b ∘ A_n(b)⁻¹ stopped at its exit from U))] → E_w[f(ψ ∘ (b ∘ F(b)⁻¹ stopped at its exit from U))]`: every
subsequence has a further subsequence along which the clocks converge almost surely uniformly on compacts, the chart
images then converge (`tendsto_chartStopPath_lbmContinuousPath`), and dominated convergence applies. -/
theorem tendsto_integral_chartStopPath_lbmContinuousPath_lqgApproxClockPlus (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {w : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock planarBrownianMotion γ hε w F)
    (hFc : ∀ᵐ b ∂planarBrownianMotion w, IsTimeChangeClock (F b))
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) (f : ContinuousPath ℂ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ b, f (chartStopPath U ψ (lbmContinuousPath (lqgApproxClockPlus γ hε n) b))
        ∂planarBrownianMotion w)
      atTop (𝓝 (∫ b, f (chartStopPath U ψ (lbmContinuousPath F b)) ∂planarBrownianMotion w)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨φ, -, hae⟩ := exists_strictMono_ae_forall_eventually_close (planarBrownianMotion w)
    (fun k b t => lqgApproxClockPlus γ hε (ns k) b t) F
    (fun T η hη => (IsLQGClock.tendsto_measure_lqgApproxClockPlus hF T hη).comp hns)
  refine ⟨φ, ?_⟩
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    (fun j => (f.continuous.measurable.comp ((measurable_chartStopPath U hU ψ).comp
      (measurable_lbmContinuousPath_lqgApproxClockPlus (γ := γ) (hcont (ns (φ j)))))).aestronglyMeasurable)
    (integrable_const _) (fun j => ae_of_all _ fun b => f.norm_coe_le_norm _) ?_
  filter_upwards [hae, hFc, ae_planarBrownianMotion_exit_all_bounded w] with b hb hFb hexit
  have hτ : ContinuousPath.exitTime U b = ((ContinuousPath.exitTime U b).toNNReal : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal (hexit U hUb).ne).symm
  exact (f.continuous.tendsto _).comp
    (tendsto_chartStopPath_lbmContinuousPath (Fs := fun j => lqgApproxClockPlus γ hε (ns (φ j)))
      (fun j => isTimeChangeClock_lqgApproxClockPlus (hcont (ns (φ j))) b) hFb hτ hb)

/-- **The transported approximating law.** The law of Brownian motion from `v` stopped at its exit from the unit
disc, run with the exit-rate clock of the transported rate of `ε_n^{γ²/2} e^{γ h_{ε_n}} + ε_n` (that is, with rate
`(ε_n^{γ²/2} e^{γ h_{ε_n}(φ x)} + ε_n) |φ'(x)|²` at `x`, `φ = chartMap U ψ`) and stopped at its exit from the disc. -/
noncomputable def chartTransportApproxLaw (γ : ℝ) (hε : ℝ → ℂ → ℝ) (n : ℕ) (U : Set ℂ) (ψ : C(ℂ, ℂ)) (v : ℂ) :
    Measure (ContinuousPath ℂ) :=
  ((planarBrownianMotion v).map (stopAtExitTime (Metric.ball 0 1))).map
    (fun W => stopAtExitTime (Metric.ball (0 : ℂ) 1)
      (lbmContinuousPath (exitRateClock (Metric.ball (0 : ℂ) 1)
        (chartTransportRate U ψ (lqgApproxRate γ hε n))) W))

/-- From Lévy's conformal invariance, the chart image of Brownian motion from `w ∈ U` run with the approximating LQG
clock `A_n` and stopped at its exit from `U` has the transported approximating law from `ψ(w)`. -/
theorem map_chartStopPath_lqgApproxClockPlus_eq_chartTransportApproxLaw (hLevy : LevyConformalChartStmt)
    (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U) {w : ℂ} (hw : w ∈ U) {n : ℕ}
    (hcont : Continuous (hε (dyadicScale n))) :
    (planarBrownianMotion w).map
        (fun b => chartStopPath U ψ (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)) =
      chartTransportApproxLaw γ hε n U ψ (ψ w) :=
  map_chartStopPath_lbmContinuousPath_lqgApproxClockPlus_of_levy hLevy hψ hU hUb hw hcont

/-- **The chart image of the Liouville Brownian motion is the limit of the transported approximating laws.** From
Lévy's conformal invariance: for an inverse chart `ψ` of the bounded open set `U`, `w ∈ U`, and an LQG clock `F` of
planar Brownian motion from `w` (`IsLQGClock`) that is almost surely a time-change clock, for circle averages
continuous at every dyadic radius, the bounded continuous tests of the transported approximating laws from `ψ(w)`
converge to those of the chart image of Brownian motion from `w` run with the clock `F` and stopped at its exit from
`U`. -/
theorem tendsto_integral_chartTransportApproxLaw_of_levy (hLevy : LevyConformalChartStmt)
    (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U) {w : ℂ} (hw : w ∈ U)
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : IsLQGClock planarBrownianMotion γ hε w F)
    (hFc : ∀ᵐ b ∂planarBrownianMotion w, IsTimeChangeClock (F b))
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) (f : ContinuousPath ℂ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ W, f W ∂chartTransportApproxLaw γ hε n U ψ (ψ w)) atTop
      (𝓝 (∫ b, f (chartStopPath U ψ (lbmContinuousPath F b)) ∂planarBrownianMotion w)) := by
  have h := tendsto_integral_chartStopPath_lbmContinuousPath_lqgApproxClockPlus (ψ := ψ) hU hUb hF hFc hcont f
  refine Tendsto.congr (fun n => ?_) h
  rw [← map_chartStopPath_lqgApproxClockPlus_eq_chartTransportApproxLaw hLevy hψ hU hUb hw (hcont n)]
  exact (integral_map
    (φ := fun b => chartStopPath U ψ (lbmContinuousPath (lqgApproxClockPlus γ hε n) b))
    ((measurable_chartStopPath U hU ψ).comp
      (measurable_lbmContinuousPath_lqgApproxClockPlus (γ := γ) (hcont n))).aemeasurable
    f.continuous.measurable.aestronglyMeasurable).symm

end Approx

end MatedCRT
