import MatedCRT.FirstPass.Derived.LQGClockInverseConvergence
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxPathMeasurable
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ApproxClockSubsequence
import LatticeProb.Prob.PathSpaceDUnif

/-!
# Approximating LQG clocks and the laws of the time-changed Brownian paths for a fixed field

Fix a field through its circle averages `hε ε z = h_ε(z)`, continuous in `z` at every dyadic radius `ε_n = 2^{-n}`.
The approximating clock

  `A_n(b, t) = ∫_0^t ε_n^{γ²/2} e^{γ h_{ε_n}(b_s)} ds + 2^{-n} t`     (`lqgApproxClockPlus`)

is a time-change clock for every continuous path `b` (`isTimeChangeClock_lqgApproxClockPlus`): the added linear
term makes it strictly increasing and unbounded, and it disappears uniformly on bounded time intervals, so the
convergence in probability of the circle-average clocks to the LQG clock `F` (`IsLQGClock`) passes to `A_n`
(`IsLQGClock.tendsto_measure_lqgApproxClockPlus`).

The time-changed path `t ↦ b (F⁻¹(t))` is a continuous path whenever `F b` is a time-change clock
(`lbmContinuousPath`; we use the path `b` itself otherwise). For the approximating clocks it depends continuously on
the Brownian path `b` for the compact-open topology (`continuous_lbmContinuousPath_lqgApproxClockPlus`): the clocks
`A_n(b', ·)` converge to `A_n(b, ·)` locally uniformly as `b' → b`, hence so do their inverses, and composition is
jointly continuous. Along a subsequence chosen by Borel–Cantelli the clocks `A_n(b, ·)` converge to `F b`
locally uniformly for almost every `b`, so the time-changed paths converge almost surely
(`tendsto_lbmContinuousPath_of_forall_eventually_close`). The subsequence characterization of convergence in
probability then gives the weak convergence of the laws under planar Brownian motion started at `z`
(`tendsto_planarBrownianPathLaw_lqgApproxClockPlus`): the law of the time-changed path with clock `A_n` converges
to the law of Liouville Brownian motion `t ↦ b (F⁻¹(t))` from `z`. The latter law is defined because the
time-changed path is an almost sure limit of continuous maps (`aemeasurable_lbmContinuousPath`); no measurability
of `F` in the path is used.

Terminology: positive continuous additive functional (the LQG clock), its right-continuous inverse, and the time
change `𝓑_{F⁻¹(t)}` of planar Brownian motion (Garban–Rhodes–Vargas, *Liouville Brownian motion*, Definition 2.17;
Berestycki, *Diffusion in planar Liouville quantum gravity*, Section 2).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal BoundedContinuousFunction Interval


/-- The approximating LQG clock `A_n(b, t) = ∫_0^t ε_n^{γ²/2} e^{γ h_{ε_n}(b_s)} ds + 2^{-n} t` at the dyadic scale
`ε_n = 2^{-n}`: the circle-average clock plus a vanishing linear drift, which makes it strictly increasing and
unbounded. -/
noncomputable def lqgApproxClockPlus (γ : ℝ) (hε : ℝ → ℂ → ℝ) (n : ℕ) (b : ContinuousPath ℂ) (t : ℝ≥0) : ℝ :=
  lqgClockApprox γ hε (dyadicScale n) b t + dyadicScale n * t

/-- The time-changed path `t ↦ b (F⁻¹(t))` (Liouville Brownian motion path) as a continuous path, when `F b` is a
time-change clock; the path `b` itself otherwise. -/
noncomputable def lbmContinuousPath (F : ContinuousPath ℂ → ℝ≥0 → ℝ) (b : ContinuousPath ℂ) : ContinuousPath ℂ :=
  open Classical in
  if h : IsTimeChangeClock (F b) then ⟨liouvilleBrownianPath F b, continuous_liouvilleBrownianPath h⟩ else b

theorem lbmContinuousPath_of_isTimeChangeClock {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ}
    (h : IsTimeChangeClock (F b)) :
    lbmContinuousPath F b = ⟨liouvilleBrownianPath F b, continuous_liouvilleBrownianPath h⟩ := by
  rw [lbmContinuousPath, dite_eq_left h]

/-- The circle-average clock vanishes at time `0`. -/
theorem lqgClockApprox_zero (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ) (b : ContinuousPath ℂ) :
    lqgClockApprox γ hε ε b 0 = 0 := by
  simp [lqgClockApprox]

section ApproxClock

variable {γ : ℝ} {hε : ℝ → ℂ → ℝ} {n : ℕ}

/-- For circle averages continuous at the radius `2^{-n}`, the approximating clock `A_n(b, ·)` is a time-change clock
for every continuous path `b`. -/
theorem isTimeChangeClock_lqgApproxClockPlus (hcont : Continuous (hε (dyadicScale n))) (b : ContinuousPath ℂ) :
    IsTimeChangeClock (lqgApproxClockPlus γ hε n b) := by
  have hd : 0 < dyadicScale n := HarmonicBalls.dyadicScale_pos n
  have hsm : StrictMono fun t : ℝ≥0 => lqgClockApprox γ hε (dyadicScale n) b t :=
    strictMono_lqgClockApprox hd hcont b
  have hlin : StrictMono fun t : ℝ≥0 => dyadicScale n * (t : ℝ) :=
    fun s t hst => mul_lt_mul_of_pos_left (NNReal.coe_lt_coe.2 hst) hd
  refine ⟨?_, ?_, hsm.add hlin, ?_⟩
  · simp [lqgApproxClockPlus, lqgClockApprox_zero]
  · exact (continuous_lqgClockApprox_time hcont b).add (continuous_const.mul NNReal.continuous_coe)
  · refine tendsto_atTop_mono (fun t => ?_)
      ((NNReal.tendsto_coe_atTop.2 tendsto_id).const_mul_atTop hd)
    have h1 : lqgClockApprox γ hε (dyadicScale n) b 0 ≤ lqgClockApprox γ hε (dyadicScale n) b t :=
      hsm.monotone zero_le
    rw [lqgClockApprox_zero] at h1
    simp only [lqgApproxClockPlus, id_eq]
    linarith

/-- **The approximating clocks converge to the LQG clock.** If the circle-average clocks converge to `F` in
`Q x`-probability uniformly on `[0, T]` (`IsLQGClock`), so do the clocks `A_n`: the added drift is at most
`2^{-n} T` on `[0, T]`. No measurability is assumed (outer measure). -/
theorem IsLQGClock.tendsto_measure_lqgApproxClockPlus {Q : Kernel ℂ (ContinuousPath ℂ)} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : IsLQGClock Q γ hε x F) (T : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => Q x {b | ∃ t ≤ T, η ≤ |lqgApproxClockPlus γ hε n b t - F b t|}) atTop (𝓝 0) := by
  have hdy : Tendsto dyadicScale atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ n : ℕ in atTop, dyadicScale n * (T : ℝ) < η / 2 := by
    have h : Tendsto (fun n => dyadicScale n * (T : ℝ)) atTop (𝓝 0) := by
      simpa using hdy.mul_const (T : ℝ)
    exact h.eventually (gt_mem_nhds (by linarith))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hF T (η / 2) (by linarith))
    (Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [hsmall] with n hn
  refine measure_mono fun b hb => ?_
  obtain ⟨t, ht, hbt⟩ := hb
  refine ⟨t, ht, ?_⟩
  have hd : 0 < dyadicScale n := HarmonicBalls.dyadicScale_pos n
  have htT : dyadicScale n * (t : ℝ) ≤ dyadicScale n * T :=
    mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 ht) hd.le
  have ht0 : 0 ≤ dyadicScale n * (t : ℝ) := mul_nonneg hd.le (NNReal.coe_nonneg t)
  have hsplit : lqgApproxClockPlus γ hε n b t - F b t =
      (lqgClockApprox γ hε (dyadicScale n) b t - F b t) + dyadicScale n * t := by
    simp only [lqgApproxClockPlus]
    ring
  have habs : |lqgApproxClockPlus γ hε n b t - F b t| ≤
      |lqgClockApprox γ hε (dyadicScale n) b t - F b t| + dyadicScale n * t := by
    rw [hsplit]
    exact (abs_add_le _ _).trans (le_of_eq (by rw [abs_of_nonneg ht0]))
  linarith

/-- **Continuity of the approximating clock in the path.** As `b' → b` for the compact-open topology,
`A_n(b', ·) → A_n(b, ·)` uniformly on `[0, T]`. -/
theorem eventually_abs_lqgApproxClockPlus_sub_lt (hcont : Continuous (hε (dyadicScale n)))
    (b : ContinuousPath ℂ) (T : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ b' in 𝓝 b, ∀ t ≤ T, |lqgApproxClockPlus γ hε n b' t - lqgApproxClockPlus γ hε n b t| < δ := by
  let g : C(ℂ, ℝ) := ⟨fun x => dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale n) x),
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcont))⟩
  have hg : Tendsto (fun b' : ContinuousPath ℂ => g.comp b') (𝓝 b) (𝓝 (g.comp b)) :=
    (ContinuousMap.continuous_postcomp g).tendsto b
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly, tendstoLocallyUniformly_iff_forall_isCompact] at hg
  have hT1 : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hδ' : 0 < δ / ((T : ℝ) + 1) := div_pos hδ hT1
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hg (Icc 0 T) isCompact_Icc) _ hδ'] with b' hb' t ht
  have hint : lqgApproxClockPlus γ hε n b' t - lqgApproxClockPlus γ hε n b t =
      ∫ s in (0 : ℝ)..(t : ℝ), (dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale n) (b' s.toNNReal)) -
        dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale n) (b s.toNNReal))) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_clockDensity (γ := γ) hcont b' _ _)
      (intervalIntegrable_clockDensity (γ := γ) hcont b _ _)]
    simp only [lqgApproxClockPlus, lqgClockApprox]
    ring
  have hbound : ∀ s ∈ Ι (0 : ℝ) (t : ℝ),
      ‖dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale n) (b' s.toNNReal)) -
        dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale n) (b s.toNNReal))‖ ≤
        δ / ((T : ℝ) + 1) := by
    intro s hs
    rw [Set.uIoc_of_le (NNReal.coe_nonneg t)] at hs
    have hsT : s.toNNReal ∈ Icc (0 : ℝ≥0) T :=
      ⟨zero_le, (Real.toNNReal_le_iff_le_coe.2 hs.2).trans ht⟩
    rw [Real.norm_eq_abs, abs_sub_comm, ← Real.dist_eq]
    exact (hb' _ hsT).le
  rw [hint, ← Real.norm_eq_abs]
  calc _ ≤ δ / ((T : ℝ) + 1) * |(t : ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ ≤ δ / ((T : ℝ) + 1) * (T : ℝ) := by
        rw [sub_zero, abs_of_nonneg (NNReal.coe_nonneg t)]
        exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 ht) hδ'.le
    _ < δ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hT1]
        exact mul_lt_mul_of_pos_left (lt_add_one _) hδ

/-- **The approximating time-changed path is continuous in the Brownian path** (compact-open topology on both
sides). -/
theorem continuous_lbmContinuousPath_lqgApproxClockPlus (hcont : Continuous (hε (dyadicScale n))) :
    Continuous (lbmContinuousPath (lqgApproxClockPlus γ hε n)) := by
  have hA : ∀ b, IsTimeChangeClock (lqgApproxClockPlus γ hε n b) :=
    isTimeChangeClock_lqgApproxClockPlus hcont
  let inv : ContinuousPath ℂ → C(ℝ≥0, ℝ≥0) := fun b =>
    ⟨clockInverse (lqgApproxClockPlus γ hε n b), IsTimeChangeClock.continuous_clockInverse (hA b)⟩
  have hX : lbmContinuousPath (lqgApproxClockPlus γ hε n) = fun b => (b : C(ℝ≥0, ℂ)).comp (inv b) := by
    funext b
    rw [lbmContinuousPath_of_isTimeChangeClock (hA b)]
    rfl
  have hinv : Continuous inv := by
    refine continuous_iff_continuousAt.2 fun b => ?_
    rw [ContinuousAt, ContinuousMap.tendsto_iff_tendstoLocallyUniformly,
      tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨U, hU⟩ := hK.bddAbove
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    have hunb : ∀ᶠ b' in 𝓝 b, ∀ u : ℝ≥0, u ≤ U → ∃ s : ℝ≥0, (u : ℝ) < lqgApproxClockPlus γ hε n b' s :=
      Eventually.of_forall fun b' u _ =>
        ((hA b').tendsto_atTop.eventually (eventually_gt_atTop (u : ℝ))).exists
    filter_upwards [clockInverse_tendsto_uniform (hA b) (fun b' => (hA b').strictMono) U hunb
      (fun T δ hδ => eventually_abs_lqgApproxClockPlus_sub_lt hcont b T hδ) η hη] with b' hb' t ht
    rw [NNReal.dist_eq, abs_sub_comm]
    exact hb' t (hU ht)
  rw [hX]
  exact ContinuousMap.continuous_comp'.comp (hinv.prodMk continuous_id)

/-- The approximating time-changed path is Borel measurable in the Brownian path. -/
theorem measurable_lbmContinuousPath_lqgApproxClockPlus (hcont : Continuous (hε (dyadicScale n))) :
    Measurable (lbmContinuousPath (lqgApproxClockPlus γ hε n)) :=
  (continuous_lbmContinuousPath_lqgApproxClockPlus hcont).measurable

end ApproxClock

section Limit

variable {γ : ℝ} {hε : ℝ → ℂ → ℝ}

/-- **Pathwise convergence of the time-changed paths.** If along `ns` the approximating clocks `A_{ns j}(b, ·)`
converge to the time-change clock `F b` uniformly on every `[0, T]`, the time-changed paths converge in the
compact-open topology. -/
theorem tendsto_lbmContinuousPath_of_forall_eventually_close (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n)))
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ} {ns : ℕ → ℕ} (hFb : IsTimeChangeClock (F b))
    (hclose : ∀ (T : ℝ≥0) (η : ℝ), 0 < η →
      ∀ᶠ j in atTop, ∀ t ≤ T, |lqgApproxClockPlus γ hε (ns j) b t - F b t| < η) :
    Tendsto (fun j => lbmContinuousPath (lqgApproxClockPlus γ hε (ns j)) b) atTop
      (𝓝 (lbmContinuousPath F b)) := by
  have hA : ∀ j, IsTimeChangeClock (lqgApproxClockPlus γ hε (ns j) b) :=
    fun j => isTimeChangeClock_lqgApproxClockPlus (hcont (ns j)) b
  have hconv : TendstoLocallyUniformly (fun j => lqgApproxClockPlus γ hε (ns j) b) (F b) atTop := by
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨T, hT⟩ := hK.bddAbove
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    filter_upwards [hclose T η hη] with j hj t ht
    rw [Real.dist_eq, abs_sub_comm]
    exact hj t (hT ht)
  have h := tendstoLocallyUniformly_liouvilleBrownianPath b
    (F := fun j => lqgApproxClockPlus γ hε (ns j)) hA hFb hconv
  rw [lbmContinuousPath_of_isTimeChangeClock hFb]
  refine Tendsto.congr (fun j => (lbmContinuousPath_of_isTimeChangeClock (hA j)).symm) ?_
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly]
  exact h

/-- The compact-open topology on continuous paths is pseudo-metrizable (by the local uniform metric `dUnif`). -/
theorem pseudoMetrizableSpace_continuousPath :
    TopologicalSpace.PseudoMetrizableSpace (ContinuousPath ℂ) := by
  let m : PseudoMetricSpace (ContinuousPath ℂ) := (LatticeProb.dUnifMetricSpace (E := ℂ)).toPseudoMetricSpace
  have h : @TopologicalSpace.PseudoMetrizableSpace (ContinuousPath ℂ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _ m)) := inferInstance
  exact h

/-- **The Liouville Brownian motion path is almost surely measurable.** For an LQG clock `F` of planar Brownian
motion from `z` that is almost surely a time-change clock, the time-changed path `b ↦ (t ↦ b (F⁻¹(t)))` is almost
everywhere measurable: along a subsequence it is the almost sure limit of the continuous approximating paths. -/
theorem aemeasurable_lbmContinuousPath {z : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock planarBrownianMotion γ hε z F)
    (hFc : ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b))
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) :
    AEMeasurable (lbmContinuousPath F) (planarBrownianMotion z) := by
  have := pseudoMetrizableSpace_continuousPath
  obtain ⟨φ, -, hae⟩ := exists_strictMono_ae_forall_eventually_close (planarBrownianMotion z)
    (fun k b t => lqgApproxClockPlus γ hε k b t) F
    (fun T η hη => IsLQGClock.tendsto_measure_lqgApproxClockPlus hF T hη)
  refine aemeasurable_of_tendsto_metrizable_ae atTop
    (fun j => (measurable_lbmContinuousPath_lqgApproxClockPlus (γ := γ) (hcont (φ j))).aemeasurable) ?_
  filter_upwards [hae, hFc] with b hb hFb
  exact tendsto_lbmContinuousPath_of_forall_eventually_close (ns := φ) hcont hFb hb

/-- **Convergence of bounded continuous tests.** Under planar Brownian motion from `z`, for every bounded
continuous `f` on paths, `E[f(b ∘ A_n(b)⁻¹)] → E[f(b ∘ F(b)⁻¹)]`: every subsequence has a further subsequence along
which the time-changed paths converge almost surely (Borel–Cantelli), and dominated convergence applies. -/
theorem tendsto_integral_lbmContinuousPath_lqgApproxClockPlus {z : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock planarBrownianMotion γ hε z F)
    (hFc : ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b))
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) (f : ContinuousPath ℂ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ b, f (lbmContinuousPath (lqgApproxClockPlus γ hε n) b) ∂planarBrownianMotion z)
      atTop (𝓝 (∫ b, f (lbmContinuousPath F b) ∂planarBrownianMotion z)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨φ, -, hae⟩ := exists_strictMono_ae_forall_eventually_close (planarBrownianMotion z)
    (fun k b t => lqgApproxClockPlus γ hε (ns k) b t) F
    (fun T η hη => (IsLQGClock.tendsto_measure_lqgApproxClockPlus hF T hη).comp hns)
  refine ⟨φ, ?_⟩
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    (fun j => (f.continuous.measurable.comp
      (measurable_lbmContinuousPath_lqgApproxClockPlus (γ := γ) (hcont (ns (φ j))))).aestronglyMeasurable)
    (integrable_const _) (fun j => ae_of_all _ fun b => f.norm_coe_le_norm _) ?_
  filter_upwards [hae, hFc] with b hb hFb
  exact (f.continuous.tendsto _).comp
    (tendsto_lbmContinuousPath_of_forall_eventually_close (ns := fun j => ns (φ j)) hcont hFb hb)

/-- The law under planar Brownian motion from `z` of an almost everywhere measurable path-valued map `g`, as a
probability measure on continuous paths. -/
noncomputable def planarBrownianPathLaw (z : ℂ) (g : ContinuousPath ℂ → ContinuousPath ℂ)
    (hg : AEMeasurable g (planarBrownianMotion z)) : ProbabilityMeasure (ContinuousPath ℂ) :=
  ⟨Measure.map g (planarBrownianMotion z), (Measure.isProbabilityMeasure_map_iff hg).2 inferInstance⟩

/-- Integrals of bounded continuous tests against `planarBrownianPathLaw z g` are expectations of `f ∘ g` under
planar Brownian motion from `z`. -/
theorem integral_planarBrownianPathLaw {z : ℂ} {g : ContinuousPath ℂ → ContinuousPath ℂ}
    (hg : AEMeasurable g (planarBrownianMotion z)) (f : ContinuousPath ℂ →ᵇ ℝ) :
    ∫ q, f q ∂(planarBrownianPathLaw z g hg : Measure (ContinuousPath ℂ)) =
      ∫ b, f (g b) ∂planarBrownianMotion z := by
  show ∫ q, f q ∂(Measure.map g (planarBrownianMotion z)) = _
  exact integral_map hg f.continuous.aestronglyMeasurable

/-- **Weak convergence of the approximating path laws (fixed field).** Let `F` be an LQG clock of planar Brownian
motion from `z` (`IsLQGClock`) that is almost surely a time-change clock, for circle averages continuous at every
dyadic radius. Then the laws under planar Brownian motion from `z` of the time-changed paths
`t ↦ b (A_n(b, ·)⁻¹(t))` converge weakly, as `n → ∞`, to the law of the Liouville Brownian motion path
`t ↦ b (F(b)⁻¹(t))`. -/
theorem tendsto_planarBrownianPathLaw_lqgApproxClockPlus {z : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock planarBrownianMotion γ hε z F)
    (hFc : ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (F b))
    (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n))) :
    Tendsto (fun n : ℕ => planarBrownianPathLaw z (lbmContinuousPath (lqgApproxClockPlus γ hε n))
        (measurable_lbmContinuousPath_lqgApproxClockPlus (γ := γ) (hcont n)).aemeasurable) atTop
      (𝓝 (planarBrownianPathLaw z (lbmContinuousPath F) (aemeasurable_lbmContinuousPath hF hFc hcont))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hlim := tendsto_integral_lbmContinuousPath_lqgApproxClockPlus hF hFc hcont f
  rw [← integral_planarBrownianPathLaw (aemeasurable_lbmContinuousPath hF hFc hcont) f] at hlim
  exact Tendsto.congr (fun n => (integral_planarBrownianPathLaw _ f).symm) hlim

end Limit

end MatedCRT
