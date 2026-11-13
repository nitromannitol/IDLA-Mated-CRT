import HarmonicBalls.Proofs.Sec6.BoundedHarmonicExit
import HarmonicBalls.Proofs.Sec6.CompactHittingStopping
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import HarmonicBalls.Proofs.Brownian.PlanarBrownianMotion
import HarmonicBalls.Proofs.Brownian.PlanarHeatFeller
import MarkovProcess.Path.ExitTimeShift
import MarkovProcess.Main

/-!
# Points other than the starting point are polar for planar Brownian motion

For planar Brownian motion `B` started at `y` and a point `x₀ ≠ y`, almost surely `B_t ≠ x₀` for every `t ≥ 0`
(`ae_planarBrownianMotion_ne_of_ne`), and almost surely `B_t ≠ y` for every `t > 0`
(`ae_planarBrownianMotion_ne_self_of_pos`).

The proof is the classical one (Mörters-Peres, *Brownian Motion*, Theorem 3.19 and Corollary 3.20). On the annulus
`A = {ε < |x - x₀| < R}` the function `log |x - x₀|` is harmonic, so the exit identity for bounded harmonic
functions (`HarmonicBalls.Section6.harmonic_eq_integral_planarBrownian_exitTime`, applied to the continuous bounded
function `log (max ε (min R |x - x₀|))`, which agrees with `log |x - x₀|` on the closure of `A`) gives
`P_y(B exits A through the inner circle) = (log R - log |y - x₀|) / (log R - log ε)`
(`planarBrownianMotion_real_exit_inner_annulus`). A path that hits `x₀` before leaving `B_R(x₀)` exits `A` through
the inner circle, for every `ε < |y - x₀|`; letting `ε → 0` and then `R → ∞` gives the claim. For the starting
point itself, the simple Markov property at the times `1/(m+1)` (`planarBrownianMotion_map_shift`) reduces to the
first case, since the planar Gaussian law has no atoms (`planarGaussian_singleton`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess InnerProductSpace
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

open _root_.HarmonicBalls

/-- The annulus `{x : ε < |x - x₀| < R}`. -/
def planarAnnulus (x₀ : ℂ) (ε R : ℝ) : Set ℂ :=
  ball x₀ R ∩ (closedBall x₀ ε)ᶜ

lemma isOpen_planarAnnulus (x₀ : ℂ) (ε R : ℝ) : IsOpen (planarAnnulus x₀ ε R) :=
  isOpen_ball.inter isClosed_closedBall.isOpen_compl

lemma isBounded_planarAnnulus (x₀ : ℂ) (ε R : ℝ) : Bornology.IsBounded (planarAnnulus x₀ ε R) :=
  isBounded_ball.subset inter_subset_left

lemma mem_planarAnnulus {x₀ x : ℂ} {ε R : ℝ} :
    x ∈ planarAnnulus x₀ ε R ↔ ε < ‖x - x₀‖ ∧ ‖x - x₀‖ < R := by
  simp only [planarAnnulus, mem_inter_iff, mem_ball, mem_compl_iff, mem_closedBall, not_le, dist_eq_norm]
  exact and_comm

/-- On the frontier of the annulus, `|x - x₀|` is `ε` or `R`. -/
lemma norm_sub_eq_of_mem_frontier_planarAnnulus {x₀ x : ℂ} {ε R : ℝ}
    (hx : x ∈ frontier (planarAnnulus x₀ ε R)) : ‖x - x₀‖ = ε ∨ ‖x - x₀‖ = R := by
  rw [(isOpen_planarAnnulus x₀ ε R).frontier_eq] at hx
  obtain ⟨hcl, hnot⟩ := hx
  have h1 : x ∈ closedBall x₀ R :=
    closure_ball_subset_closedBall (closure_mono inter_subset_left hcl)
  have h2 : x ∈ (ball x₀ ε)ᶜ := by
    have hsub : (closedBall x₀ ε)ᶜ ⊆ (ball x₀ ε)ᶜ := compl_subset_compl.2 ball_subset_closedBall
    exact (isOpen_ball.isClosed_compl.closure_subset_iff.2 hsub) (closure_mono inter_subset_right hcl)
  rw [mem_closedBall, dist_eq_norm] at h1
  rw [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] at h2
  rw [mem_planarAnnulus] at hnot
  rcases eq_or_lt_of_le h2 with h | h
  · exact Or.inl h.symm
  · exact Or.inr (le_antisymm h1 (not_lt.1 fun h' => hnot ⟨h, h'⟩))

/-- The clamped logarithm `log (max ε (min R |x - x₀|))`: continuous, bounded, and equal to `log |x - x₀|` on the
closure of the annulus. -/
noncomputable def clampedLogDist (x₀ : ℂ) (ε R : ℝ) (x : ℂ) : ℝ :=
  Real.log (max ε (min R ‖x - x₀‖))

lemma continuous_clampedLogDist (x₀ : ℂ) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    Continuous (clampedLogDist x₀ ε R) :=
  (continuous_const.max (continuous_const.min (continuous_id.sub continuous_const).norm)).log
    fun _ => (lt_of_lt_of_le hε (le_max_left _ _)).ne'

lemma clampedLogDist_bounds (x₀ : ℂ) {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (x : ℂ) :
    Real.log ε ≤ clampedLogDist x₀ ε R x ∧ clampedLogDist x₀ ε R x ≤ Real.log R := by
  unfold clampedLogDist
  exact ⟨Real.log_le_log hε (le_max_left _ _),
    Real.log_le_log (lt_of_lt_of_le hε (le_max_left _ _)) (max_le hεR (min_le_left _ _))⟩

lemma norm_clampedLogDist_le (x₀ : ℂ) {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (x : ℂ) :
    ‖clampedLogDist x₀ ε R x‖ ≤ |Real.log ε| + |Real.log R| := by
  obtain ⟨h1, h2⟩ := clampedLogDist_bounds x₀ hε hεR x
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le (Real.log ε), abs_nonneg (Real.log R)]
  · linarith [le_abs_self (Real.log R), abs_nonneg (Real.log ε)]

lemma clampedLogDist_of_le_of_le {x₀ x : ℂ} {ε R : ℝ} (h1 : ε ≤ ‖x - x₀‖) (h2 : ‖x - x₀‖ ≤ R) :
    clampedLogDist x₀ ε R x = Real.log ‖x - x₀‖ := by
  unfold clampedLogDist
  rw [min_eq_right h2, max_eq_right h1]

/-- The clamped logarithm is harmonic on the annulus. -/
lemma harmonicOnNhd_clampedLogDist (x₀ : ℂ) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    HarmonicOnNhd (clampedLogDist x₀ ε R) (planarAnnulus x₀ ε R) := by
  intro x hx
  have hev : clampedLogDist x₀ ε R =ᶠ[𝓝 x] fun w => Real.log ‖w - x₀‖ := by
    filter_upwards [(isOpen_planarAnnulus x₀ ε R).mem_nhds hx] with w hw
    obtain ⟨h1, h2⟩ := mem_planarAnnulus.1 hw
    exact clampedLogDist_of_le_of_le h1.le h2.le
  rw [harmonicAt_congr_nhds hev]
  have hne : x - x₀ ≠ 0 := by
    intro h
    have := (mem_planarAnnulus.1 hx).1
    rw [h, norm_zero] at this
    linarith
  exact AnalyticAt.harmonicAt_log_norm (f := fun w => w - x₀) (analyticAt_id.sub analyticAt_const) hne

/-- **Exit through the inner circle of an annulus.** For planar Brownian motion started at `y` with
`ε < |y - x₀| < R`, the probability of leaving the annulus `{ε < |x - x₀| < R}` through the inner circle is
`(log R - log |y - x₀|) / (log R - log ε)`; in the form
`log |y - x₀| = log R - (log R - log ε) · P_y(|B_τ - x₀| ≤ ε)`. -/
theorem log_norm_sub_eq_exit_inner_annulus {x₀ y : ℂ} {ε R : ℝ} (hε : 0 < ε)
    (hy : y ∈ planarAnnulus x₀ ε R) :
    Real.log ‖y - x₀‖ = Real.log R - (Real.log R - Real.log ε) *
      (planarBrownianMotion y).real (exitPosition (planarAnnulus x₀ ε R) ⁻¹' closedBall x₀ ε) := by
  set A := planarAnnulus x₀ ε R with hA_def
  obtain ⟨hy1, hy2⟩ := mem_planarAnnulus.1 hy
  have hεR : ε ≤ R := (hy1.trans hy2).le
  have hA : IsOpen A := isOpen_planarAnnulus x₀ ε R
  set E := exitPosition A ⁻¹' closedBall x₀ ε with hE_def
  have hEm : MeasurableSet E := measurable_exitPosition hA measurableSet_closedBall
  have hid := Section6.harmonic_eq_integral_planarBrownian_exitTime hA (isBounded_planarAnnulus x₀ ε R)
    (continuous_clampedLogDist x₀ hε R) (harmonicOnNhd_clampedLogDist x₀ hε R)
    (norm_clampedLogDist_le x₀ hε hεR) hy
  rw [clampedLogDist_of_le_of_le hy1.le hy2.le] at hid
  rw [hid]
  have hae : (fun ω : ContinuousPath ℂ =>
      clampedLogDist x₀ ε R (ω ((ContinuousPath.exitTime A ω).toNNReal))) =ᵐ[planarBrownianMotion y]
      fun ω => Real.log R - (Real.log R - Real.log ε) * E.indicator 1 ω := by
    filter_upwards [Section6.ae_planarBrownian_exitTime_bounded_lt_top y (isBounded_planarAnnulus x₀ ε R),
      ae_planarBrownianMotion_eval_zero y] with ω hfin h0
    have hne : ContinuousPath.exitTime A ω ≠ ⊤ := hfin.ne
    have hfr := ContinuousPath.coordinate_exitTime_mem_frontier A hA ω (h0 ▸ hy) hne
    have hpos : exitPosition A ω = ω ((ContinuousPath.exitTime A ω).toNNReal) := exitPosition_eq A ω hne
    rcases norm_sub_eq_of_mem_frontier_planarAnnulus hfr with h | h
    · have hmem : ω ∈ E := by
        show exitPosition A ω ∈ closedBall x₀ ε
        rw [hpos, mem_closedBall, dist_eq_norm, h]
      rw [indicator_of_mem hmem, clampedLogDist_of_le_of_le h.ge (h ▸ hεR), h]
      simp
    · rcases eq_or_lt_of_le hεR with hεR' | hεR'
      · have hmem : ω ∈ E := by
          show exitPosition A ω ∈ closedBall x₀ ε
          rw [hpos, mem_closedBall, dist_eq_norm, h, hεR']
        rw [indicator_of_mem hmem, clampedLogDist_of_le_of_le (h ▸ hεR) h.le, h, hεR']
        simp
      · have hmem : ω ∉ E := by
          show exitPosition A ω ∉ closedBall x₀ ε
          rw [hpos, mem_closedBall, dist_eq_norm, h, not_le]
          exact hεR'
        rw [indicator_of_notMem hmem, clampedLogDist_of_le_of_le (h ▸ hεR) h.le, h]
        simp
  have hint : Integrable (fun ω => (Real.log R - Real.log ε) * E.indicator 1 ω) (planarBrownianMotion y) :=
    ((integrable_const (1 : ℝ)).indicator hEm).const_mul _
  rw [integral_congr_ae hae, integral_sub (integrable_const _) hint, integral_const, integral_const_mul,
    integral_indicator_one hEm]
  simp

/-- **Points are polar for planar Brownian motion (other than the starting point).** For `x₀ ≠ y`, planar Brownian
motion started at `y` almost surely never visits `x₀`. -/
theorem ae_planarBrownianMotion_ne_of_ne {x₀ y : ℂ} (hxy : x₀ ≠ y) :
    ∀ᵐ ω ∂planarBrownianMotion y, ∀ t : ℝ≥0, ω t ≠ x₀ := by
  set d := ‖y - x₀‖ with hd_def
  have hd : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 hxy.symm)
  -- `H R`: the path hits `x₀` while staying in `B_R(x₀)` up to that time.
  set H : ℕ → Set (ContinuousPath ℂ) :=
    fun n => {ω | ∃ t : ℝ≥0, ω t = x₀ ∧ ∀ s ≤ t, ‖ω s - x₀‖ < n} with hH_def
  have hcover : {ω : ContinuousPath ℂ | ∃ t : ℝ≥0, ω t = x₀} ⊆ ⋃ n, H n := by
    rintro ω ⟨t, ht⟩
    obtain ⟨R, hR⟩ := (isCompact_Icc.image ω.continuous).isBounded.subset_ball x₀
    obtain ⟨n, hn⟩ := exists_nat_gt R
    refine mem_iUnion.2 ⟨n, t, ht, fun s hs => ?_⟩
    have hmem := hR ⟨s, ⟨zero_le, hs⟩, rfl⟩
    rw [mem_ball, dist_eq_norm] at hmem
    exact hmem.trans hn
  have hHnull : ∀ n : ℕ, planarBrownianMotion y (H n) = 0 := by
    intro n
    by_cases hn : (n : ℝ) ≤ d
    · -- the path starts at distance `d ≥ n` from `x₀`
      refine measure_mono_null (t := {ω : ContinuousPath ℂ | ω 0 ≠ y}) ?_ ?_
      · rintro ω ⟨t, -, hs⟩ h0
        have := hs 0 zero_le
        rw [h0] at this
        linarith
      · exact ae_iff.1 (ae_planarBrownianMotion_eval_zero y)
    · push Not at hn
      -- for every `ε ∈ (0, d)`, `P(H n) ≤ (log n - log d) / (log n - log ε)`
      have hbound : ∀ ε : ℝ, 0 < ε → ε < d → (planarBrownianMotion y).real (H n) ≤
          (Real.log n - Real.log d) / (Real.log n - Real.log ε) := by
        intro ε hε hεd
        have hyA : y ∈ planarAnnulus x₀ ε n := mem_planarAnnulus.2 ⟨hεd, hn⟩
        have hid := log_norm_sub_eq_exit_inner_annulus hε hyA
        have hc : 0 < Real.log n - Real.log ε :=
          sub_pos.2 (Real.log_lt_log hε (hεd.trans hn))
        have hsub : H n ≤ᵐ[planarBrownianMotion y]
            exitPosition (planarAnnulus x₀ ε n) ⁻¹' closedBall x₀ ε := by
          filter_upwards [ae_planarBrownianMotion_eval_zero y] with ω h0 hω
          obtain ⟨t, ht, hs⟩ := hω
          set A := planarAnnulus x₀ ε n
          have hA : IsOpen A := isOpen_planarAnnulus x₀ ε n
          have hnotA : ω t ∉ A := by
            rw [ht, mem_planarAnnulus, sub_self, norm_zero]
            exact fun h => absurd h.1 (not_lt.2 hε.le)
          have hle : ContinuousPath.exitTime A ω ≤ (t : ℝ≥0∞) :=
            ContinuousPath.exitTime_le_of_notMem A ω t hnotA
          have hne : ContinuousPath.exitTime A ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
          have hfr := ContinuousPath.coordinate_exitTime_mem_frontier A hA ω (h0 ▸ hyA) hne
          have hτt : (ContinuousPath.exitTime A ω).toNNReal ≤ t := by
            rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hne]
            exact hle
          have hlt := hs _ hτt
          show exitPosition A ω ∈ closedBall x₀ ε
          rw [exitPosition_eq A ω hne, mem_closedBall, dist_eq_norm]
          rcases norm_sub_eq_of_mem_frontier_planarAnnulus hfr with h | h
          · exact h.le
          · exact absurd h hlt.ne
        have hmono : (planarBrownianMotion y).real (H n) ≤
            (planarBrownianMotion y).real (exitPosition (planarAnnulus x₀ ε n) ⁻¹' closedBall x₀ ε) :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
        rw [le_div_iff₀ hc]
        nlinarith
      have hlim : Tendsto (fun ε : ℝ => (Real.log n - Real.log d) / (Real.log n - Real.log ε))
          (𝓝[>] 0) (𝓝 0) :=
        have h1 : Tendsto (fun ε : ℝ => Real.log n - Real.log ε) (𝓝[>] 0) atTop := by
          have := Filter.tendsto_atTop_add_const_left (𝓝[>] (0 : ℝ)) (Real.log n)
            (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
          simpa only [Function.comp_def, sub_eq_add_neg] using this
        tendsto_const_nhds.div_atTop h1
      have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (planarBrownianMotion y).real (H n) ≤
          (Real.log n - Real.log d) / (Real.log n - Real.log ε) := by
        filter_upwards [Ioo_mem_nhdsGT hd] with ε hε
        exact hbound ε hε.1 hε.2
      have hle0 := ge_of_tendsto hlim hev
      have h0 : (planarBrownianMotion y).real (H n) = 0 := le_antisymm hle0 measureReal_nonneg
      rwa [measureReal_eq_zero_iff (measure_ne_top _ _)] at h0
  have hnull : planarBrownianMotion y {ω : ContinuousPath ℂ | ∃ t : ℝ≥0, ω t = x₀} = 0 :=
    measure_mono_null hcover (measure_iUnion_null hHnull)
  refine ae_iff.2 ?_
  simpa only [ne_eq, not_forall, not_not] using hnull

/-! ### The starting point is not revisited at positive times -/

/-- The planar Gaussian law with positive variance has no atoms. -/
theorem planarGaussian_singleton (z y : ℂ) {t : ℝ≥0} (ht : t ≠ 0) : planarGaussian z t {y} = 0 := by
  have := nullSingletonClass_gaussianReal (μ := z.re) ht
  rw [planarGaussian, Measure.map_apply Complex.measurableEquivRealProd.symm.measurable
    (measurableSet_singleton y)]
  refine measure_mono_null (t := ({y.re} : Set ℝ) ×ˢ (univ : Set ℝ)) (fun p hp => ?_) ?_
  · have hp' : Complex.measurableEquivRealProd.symm p = y := hp
    refine ⟨?_, mem_univ _⟩
    rw [mem_singleton_iff, ← hp']
    rfl
  · rw [Measure.prod_prod, measure_singleton, zero_mul]

/-- **Simple Markov property of planar Brownian motion at a deterministic time:** the law of the path shifted by
`s` is the mixture of the laws of planar Brownian motion started from the time-`s` position, which has the law
`planarGaussian y s`. -/
theorem planarBrownianMotion_map_shift (y : ℂ) (s : ℝ≥0) :
    (planarBrownianMotion y).map (ContinuousPath.shift s) = (planarGaussian y s).bind planarBrownianMotion := by
  have h := SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_shift planarHeatSemigroup
    isConservative_planarHeatSemigroup isFellerKernelSemigroup_planarHeatSemigroup
    kolmogorovRegular_planarHeatSemigroup s
  rw [← planarBrownianMotion_eq_continuousProcess] at h
  have h2 := DFunLike.congr_fun h y
  rw [Kernel.map_apply _ (ContinuousPath.continuous_shift_fixed s).measurable, Kernel.comp_apply] at h2
  rw [h2]
  change (planarHeatKernel s y).bind planarBrownianMotion = _
  rw [planarHeatKernel_apply]

/-- The paths that visit a point form a measurable set: it is the event that the exit time of the complement of
the point is finite. -/
lemma measurableSet_exists_eq (x₀ : ℂ) : MeasurableSet {ω : ContinuousPath ℂ | ∃ t, ω t = x₀} := by
  have h : {ω : ContinuousPath ℂ | ∃ t, ω t = x₀} = ContinuousPath.exitTime ({x₀}ᶜ) ⁻¹' Iio ⊤ := by
    ext ω
    simp [ContinuousPath.exitTime_lt_top_iff]
  rw [h]
  exact ContinuousPath.measurable_exitTime _ isClosed_singleton.isOpen_compl measurableSet_Iio

/-- **The starting point is polar at positive times.** Planar Brownian motion started at `y` almost surely does
not return to `y` at any positive time: by the simple Markov property at time `1/(m+1)`, the shifted path is planar
Brownian motion started from a point which almost surely differs from `y` (the Gaussian law has no atoms), and such
a path never visits `y` (`ae_planarBrownianMotion_ne_of_ne`). -/
theorem ae_planarBrownianMotion_ne_self_of_pos (y : ℂ) :
    ∀ᵐ ω ∂planarBrownianMotion y, ∀ t : ℝ≥0, 0 < t → ω t ≠ y := by
  have hHm := measurableSet_exists_eq y
  have hstep : ∀ m : ℕ, ∀ᵐ ω ∂planarBrownianMotion y,
      ContinuousPath.shift ((m : ℝ≥0) + 1)⁻¹ ω ∉ {ω : ContinuousPath ℂ | ∃ t, ω t = y} := by
    intro m
    have hs : ((m : ℝ≥0) + 1)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
    have hshift : Measurable (ContinuousPath.shift ((m : ℝ≥0) + 1)⁻¹ : ContinuousPath ℂ → ContinuousPath ℂ) :=
      (ContinuousPath.continuous_shift_fixed _).measurable
    have hae : ∀ᵐ z ∂planarGaussian y ((m : ℝ≥0) + 1)⁻¹,
        planarBrownianMotion z {ω : ContinuousPath ℂ | ∃ t, ω t = y} = 0 := by
      have hz : ∀ᵐ z ∂planarGaussian y ((m : ℝ≥0) + 1)⁻¹, z ≠ y := by
        rw [ae_iff]
        simpa using planarGaussian_singleton y y hs
      refine hz.mono fun z hzy => ?_
      exact measure_eq_zero_iff_ae_notMem.2
        ((ae_planarBrownianMotion_ne_of_ne hzy.symm).mono fun ω hω ⟨t, ht⟩ => hω t ht)
    rw [ae_iff]
    simp only [not_not]
    change planarBrownianMotion y (ContinuousPath.shift ((m : ℝ≥0) + 1)⁻¹ ⁻¹'
      {ω : ContinuousPath ℂ | ∃ t, ω t = y}) = 0
    rw [← Measure.map_apply hshift hHm, planarBrownianMotion_map_shift,
      Measure.bind_apply hHm planarBrownianMotion.aemeasurable, lintegral_congr_ae hae, lintegral_zero]
  refine (ae_all_iff.2 hstep).mono fun ω hω t ht hty => ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt ht
  rw [one_div] at hm
  refine hω m ⟨t - ((m : ℝ≥0) + 1)⁻¹, ?_⟩
  rw [ContinuousPath.shift_apply, add_tsub_cancel_of_le hm.le]
  exact hty

end MatedCRT.KilledOccupation
