import MatedCRT.FirstPass.Derived.ChartGreenFunction
import MatedCRT.FirstPass.Derived.ChartConformalClock
import HarmonicBalls.Proofs.Potential.LBMExpectedExitTimeGreenHolder
import HarmonicBalls.Proofs.Potential.GreenDomainExhaustion
import HarmonicBalls.Proofs.Sec6.ExitTimeExhaustion
import HarmonicBalls.Proofs.Sec6.BrownianAvoidance
import HarmonicBalls.FirstPass.S11d.SmoothCutoff

/-!
# The Green identity for Liouville Brownian motion killed on exiting a chart window

Step R4 of the Revuz route to Berestycki (2015), Theorem 1.3, for Brownian motion killed on exiting a bounded open
set `U` with an inverse chart `ψ` (a conformal map of `U` onto the unit disc, injective on `closure U`): the expected
exit time of Liouville Brownian motion from `U` is the Green potential of the LQG measure,

  `E_x[τ^{LBM}_U] = ∫ 2 G_U(x, y) μ(dy)`,   `x ∈ U`.

The harmonic-balls formalization proves this identity for smooth bounded open sets
(`HarmonicBalls.ae_forall_expectedLBMExitTime_eq_green`, Proposition 2.5 of the harmonic-balls paper). A chart window
need not be smooth; it is exhausted by the smooth chart sub-windows `U ∩ ψ⁻¹(B(0, r))`, `r ↑ 1`
(`IsInverseChart.isSmoothBoundedOpen_chartSubWindow`: the defining function is `‖ψ‖² - r²` near the sub-window,
glued to `1` by a smooth cutoff). Along the exhaustion the exit times of Liouville Brownian motion increase to the
exit time from `U` (monotone convergence of the expectations), and the Green kernels increase to the Green kernel
of `U` (`HarmonicBalls.tendsto_greenFunction_of_exhaustion`).

## Main statements

* `IsInverseChart.isSmoothBoundedOpen_chartSubWindow`: the chart sub-windows are smooth bounded open sets.
* `expectedLBMExitTime_eq_lintegral_green_of_inverseChart`: from the Green identity on smooth bounded open sets, the
  Green identity on every chart window.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT

/-! ### Smooth chart sub-windows -/

/-- The chart sub-window `U ∩ ψ⁻¹(B(0, r))` of radius `r`. -/
def chartSubWindow (U : Set ℂ) (ψ : C(ℂ, ℂ)) (r : ℝ) : Set ℂ :=
  U ∩ ψ ⁻¹' ball 0 r

theorem isOpen_chartSubWindow {U : Set ℂ} (hU : IsOpen U) (ψ : C(ℂ, ℂ)) (r : ℝ) :
    IsOpen (chartSubWindow U ψ r) :=
  hU.inter (isOpen_ball.preimage ψ.continuous)

theorem chartSubWindow_subset (U : Set ℂ) (ψ : C(ℂ, ℂ)) (r : ℝ) : chartSubWindow U ψ r ⊆ U :=
  inter_subset_left

theorem chartSubWindow_mono (U : Set ℂ) (ψ : C(ℂ, ℂ)) {r s : ℝ} (hrs : r ≤ s) :
    chartSubWindow U ψ r ⊆ chartSubWindow U ψ s :=
  inter_subset_inter_right U (preimage_mono (ball_subset_ball hrs))

/-- A smooth function times a function smooth on an open set containing the topological support of the first is
smooth. -/
theorem contDiff_mul_of_tsupport_subset {n : WithTop ℕ∞} {χ g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hχ : ContDiff ℝ n χ) (hg : ContDiffOn ℝ n g U) (hsupp : tsupport χ ⊆ U) :
    ContDiff ℝ n (fun x => χ x * g x) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.mul (hg.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h => hx (hsupp h)
    have h0 : (fun y => χ y * g y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq h0

section InverseChart

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-- The closed chart sub-window `U ∩ ψ⁻¹(closedBall 0 r)`, `r < 1`, is compact. -/
theorem IsInverseChart.isCompact_closedSubWindow (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {r : ℝ} (hr : r < 1) :
    IsCompact (U ∩ ψ ⁻¹' closedBall 0 r) := by
  have hK : IsCompact (closure U ∩ ψ ⁻¹' closedBall 0 r) :=
    hUb.isCompact_closure.inter_right (isClosed_closedBall.preimage ψ.continuous)
  convert hK using 1
  ext x
  constructor
  · rintro ⟨hx, hxr⟩
    exact ⟨subset_closure hx, hxr⟩
  · rintro ⟨hx, hxr⟩
    refine ⟨hψ.mem_of_mem_closure hU hx ?_, hxr⟩
    exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hxr) hr)

/-- **The chart sub-windows are smooth bounded open sets.** For `0 < r < 1`, `U ∩ ψ⁻¹(B(0, r))` is the sublevel
set `{ρ < 0}` of the smooth function `ρ = χ (‖ψ‖² - r²) + (1 - χ)`, with `χ` a smooth cutoff equal to `1` on the
closed sub-window of radius `(r + 1) / 2` and supported in `U`; on the zero set of `ρ`, `ρ = ‖ψ‖² - r²` nearby, whose
derivative in the direction `ψ(x) / ψ'(x)` is `2 r² ≠ 0`. -/
theorem IsInverseChart.isSmoothBoundedOpen_chartSubWindow (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    IsSmoothBoundedOpen (chartSubWindow U ψ r) := by
  set r' : ℝ := (r + 1) / 2 with hr'def
  have hrr' : r < r' := by rw [hr'def]; linarith
  have hr'1 : r' < 1 := by rw [hr'def]; linarith
  obtain ⟨χ, hχ, -, hχU, hχ01, hχ1⟩ := HarmonicBalls.exists_smooth_cutoff
    (hψ.isCompact_closedSubWindow hU hUb hr'1) hU inter_subset_left hUb
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ‖ψ x‖ ^ 2 - r ^ 2) U :=
    ((contDiff_norm_sq ℝ).comp_contDiffOn
      ((hψ.differentiableOn.contDiffOn hU).restrict_scalars ℝ)).sub contDiffOn_const
  have hχ0 : ∀ x, x ∉ U → χ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hχU h))
  have hχK : ∀ x ∈ U, ‖ψ x‖ ≤ r' → χ x = 1 := fun x hx h =>
    hχ1 x ⟨hx, mem_closedBall_zero_iff.2 h⟩
  have hpos : ∀ x, ¬ (x ∈ U ∧ ‖ψ x‖ ≤ r') → 0 < χ x * (‖ψ x‖ ^ 2 - r ^ 2) + (1 - χ x) := by
    intro x hx
    by_cases hxU : x ∈ U
    · have hlt : r' < ‖ψ x‖ := lt_of_not_ge fun h => hx ⟨hxU, h⟩
      have ha : 0 < ‖ψ x‖ ^ 2 - r ^ 2 := by nlinarith
      obtain ⟨h0, h1⟩ := hχ01 x
      rcases h0.lt_or_eq with h | h
      · nlinarith
      · rw [← h]
        norm_num
    · rw [hχ0 x hxU]
      norm_num
  refine ⟨hUb.subset inter_subset_left, fun x => χ x * (‖ψ x‖ ^ 2 - r ^ 2) + (1 - χ x),
    (contDiff_mul_of_tsupport_subset hU hχ hg hχU).add (contDiff_const.sub hχ), ?_, ?_⟩
  · ext x
    simp only [chartSubWindow, mem_inter_iff, mem_preimage, mem_ball_zero_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hxU, hxr⟩
      rw [hχK x hxU (hxr.le.trans hrr'.le)]
      nlinarith [norm_nonneg (ψ x)]
    · intro hρ
      by_cases hK : x ∈ U ∧ ‖ψ x‖ ≤ r'
      · refine ⟨hK.1, ?_⟩
        rw [hχK x hK.1 hK.2] at hρ
        nlinarith [norm_nonneg (ψ x)]
      · exact absurd hρ (not_lt.2 (hpos x hK).le)
  · intro x hρ
    beta_reduce at hρ
    have hK : x ∈ U ∧ ‖ψ x‖ ≤ r' := by
      by_contra hK
      exact (hpos x hK).ne' hρ
    have hnorm : ‖ψ x‖ = r := by
      have hρ' := hρ
      rw [hχK x hK.1 hK.2] at hρ'
      have hsq : ‖ψ x‖ ^ 2 = r ^ 2 := by linarith
      exact (pow_left_inj₀ (norm_nonneg _) hr0.le two_ne_zero).1 hsq
    have hW : chartSubWindow U ψ r' ∈ 𝓝 x :=
      (isOpen_chartSubWindow hU ψ r').mem_nhds ⟨hK.1, mem_ball_zero_iff.2 (hnorm ▸ hrr')⟩
    have heq : (fun y => χ y * (‖ψ y‖ ^ 2 - r ^ 2) + (1 - χ y)) =ᶠ[𝓝 x]
        fun y => ‖ψ y‖ ^ 2 - r ^ 2 := by
      filter_upwards [hW] with y hy
      rw [hχK y hy.1 (mem_ball_zero_iff.1 hy.2).le]
      ring
    rw [heq.fderiv_eq]
    have hd0 : deriv ψ x ≠ 0 := hψ.deriv_ne_zero hU hK.1
    have hd : HasDerivAt ψ (deriv ψ x) x :=
      ((hψ.differentiableOn x hK.1).differentiableAt (hU.mem_nhds hK.1)).hasDerivAt
    have hF := ((hd.hasFDerivAt.restrictScalars ℝ).norm_sq).sub_const (r ^ 2)
    rw [hF.fderiv]
    intro h0
    have h1 := congrArg (fun L : ℂ →L[ℝ] ℝ => L (ψ x / deriv ψ x)) h0
    simp [div_mul_cancel₀ _ hd0, hnorm] at h1
    exact hr0.ne' h1

/-- The radii `1 - 1 / (n + 2)` of the exhausting chart sub-windows. -/
noncomputable def subWindowRadius (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)

theorem subWindowRadius_pos (n : ℕ) : 0 < subWindowRadius n := by
  unfold subWindowRadius
  have h : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  linarith

theorem subWindowRadius_lt_one (n : ℕ) : subWindowRadius n < 1 := by
  unfold subWindowRadius
  have : 0 < 1 / ((n : ℝ) + 2) := by positivity
  linarith

theorem subWindowRadius_mono : Monotone subWindowRadius := by
  intro m n hmn
  unfold subWindowRadius
  have hmn' : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
  have h : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

theorem exists_lt_subWindowRadius {a : ℝ} (ha : a < 1) : ∃ n, a < subWindowRadius n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - a))
  refine ⟨n, ?_⟩
  unfold subWindowRadius
  have h1 : 0 < 1 - a := by linarith
  have h2 : 1 / ((n : ℝ) + 2) < 1 - a := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ h1] at hn
    nlinarith
  linarith

/-- The exhausting chart sub-windows `U ∩ ψ⁻¹(B(0, 1 - 1/(n + 2)))`. -/
def chartExhaustion (U : Set ℂ) (ψ : C(ℂ, ℂ)) (n : ℕ) : Set ℂ :=
  chartSubWindow U ψ (subWindowRadius n)

theorem monotone_chartExhaustion (U : Set ℂ) (ψ : C(ℂ, ℂ)) : Monotone (chartExhaustion U ψ) :=
  fun _ _ hmn => chartSubWindow_mono U ψ (subWindowRadius_mono hmn)

theorem IsInverseChart.iUnion_chartExhaustion (hψ : IsInverseChart U z ψ) :
    (⋃ n, chartExhaustion U ψ n) = U := by
  apply Subset.antisymm (iUnion_subset fun n => chartSubWindow_subset U ψ _)
  intro x hx
  have h1 : ‖ψ x‖ < 1 := mem_ball_zero_iff.1 (hψ.mapsTo_ball hx)
  obtain ⟨n, hn⟩ := exists_lt_subWindowRadius h1
  exact mem_iUnion.2 ⟨n, hx, mem_ball_zero_iff.2 hn⟩

theorem IsInverseChart.eventually_mem_chartExhaustion (hψ : IsInverseChart U z ψ) {x : ℂ} (hx : x ∈ U) :
    ∀ᶠ n in atTop, x ∈ chartExhaustion U ψ n :=
  eventually_mem_open_exhaustion _ (monotone_chartExhaustion U ψ) hψ.iUnion_chartExhaustion hx

end InverseChart

/-! ### Exit times of Liouville Brownian motion along the exhaustion -/

/-- The exit time of Liouville Brownian motion is monotone in the domain. -/
theorem lbmExitTime_mono {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {O O' : Set ℂ} (h : O ⊆ O')
    (b : ContinuousPath ℂ) : lbmExitTime F O b ≤ lbmExitTime F O' b := by
  unfold lbmExitTime pathExitTime
  apply sInf_le_sInf
  rintro s ⟨t, rfl, ht⟩
  exact ⟨t, rfl, fun h' => ht (h h')⟩

section Clock

variable {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ} {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {D : Set ℂ}

/-- The exit time of Liouville Brownian motion from a bounded open set is almost surely measurable: it is the limit in
probability of the approximating clocks at the Brownian exit time. -/
theorem aemeasurable_lbmExitTime (hcont : ∀ k : ℕ, Continuous (hε (dyadicScale k)))
    (hclock : IsLQGClock planarBrownianMotion γ hε x F)
    (hF : ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F b))
    (hDo : IsOpen D) (hDb : Bornology.IsBounded D) :
    AEMeasurable (lbmExitTime F D) (planarBrownianMotion x) := by
  let A : ℕ → ContinuousPath ℂ → ℝ := fun k b =>
    lqgClockApprox γ hε (dyadicScale k) b (ContinuousPath.exitTime D b).toNNReal
  have hmeas (k : ℕ) : Measurable (A k) := by
    let g : ℂ → ℝ := fun y => dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) y)
    have hg : Continuous g :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hcont k)))
    simpa only [A, lqgClockApprox, g, SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional,
      Function.comp_def, id_eq] using
      (SubMarkovKernelSemigroup.stronglyMeasurable_feynmanKacAdditiveFunctional_joint
        hg.measurable).measurable.comp
        ((ContinuousPath.measurable_exitTime D hDo).ennreal_toNNReal.prodMk measurable_id)
  have hconv : TendstoInMeasure (planarBrownianMotion x) A atTop
      (fun b => (lbmExitTime F D b).toReal) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro η hη
    simpa only [A, Real.dist_eq] using hclock.tendsto_measure_clockApprox_lbmExitTime hDo hDb hF hη
  have hsm : AEStronglyMeasurable (fun b => (lbmExitTime F D b).toReal) (planarBrownianMotion x) :=
    hconv.aestronglyMeasurable fun k => (hmeas k).aestronglyMeasurable
  have hfin : ∀ᵐ b ∂(planarBrownianMotion x), lbmExitTime F D b ≠ ⊤ := by
    filter_upwards [hF, Section6.ae_planarBrownian_exitTime_bounded_lt_top x hDb] with b hb hτ
    rw [HarmonicBalls.lbmExitTime_eq_clockValue hDo hb hτ.ne]
    exact ENNReal.coe_ne_top
  refine hsm.aemeasurable.ennreal_ofReal.congr ?_
  filter_upwards [hfin] with b hb
  exact ENNReal.ofReal_toReal hb

/-- From a start inside a bounded open set, the exit time of Liouville Brownian motion is almost surely positive. -/
theorem ae_lbmExitTime_pos (hF : ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F b))
    (hDo : IsOpen D) (hDb : Bornology.IsBounded D) (hx : x ∈ D) :
    ∀ᵐ b ∂(planarBrownianMotion x), 0 < lbmExitTime F D b := by
  filter_upwards [hF, Section6.ae_planarBrownian_exitTime_bounded_lt_top x hDb,
    Section6.ae_planarBrownianMotion_exitTime_pos hDo hx] with b hb hτ hτ0
  rw [HarmonicBalls.lbmExitTime_eq_clockValue hDo hb hτ.ne]
  have hτpos : 0 < (ContinuousPath.exitTime D b).toNNReal := ENNReal.toNNReal_pos hτ0.ne' hτ.ne
  have hFpos : 0 < F b (ContinuousPath.exitTime D b).toNNReal := by
    have h := hb.strictMono hτpos
    rwa [hb.map_zero] at h
  exact ENNReal.coe_pos.2 (Real.toNNReal_pos.2 hFpos)

end Clock

/-- **The Green identity for the exit time of Liouville Brownian motion from a chart window.** Let `F x` be LQG clocks
of planar Brownian motion from every start `x` (circle averages continuous at the dyadic radii), almost surely
time-change clocks, and let the Green identity `E_x[τ^{LBM}_O] = ∫_O 2 G_O(x, y) μ(dy)` hold on every smooth bounded
open set `O` (`HarmonicBalls.ae_forall_expectedLBMExitTime_eq_green` gives it almost surely for the LQG measure).
Then for every bounded open set `U` with an inverse chart and every `x ∈ U`,
`E_x[τ^{LBM}_U] = ∫ 2 G_U(x, y) μ(dy)`. -/
theorem expectedLBMExitTime_eq_lintegral_green_of_inverseChart
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {μ : Measure ℂ} {F : ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hcont : ∀ k : ℕ, Continuous (hε (dyadicScale k)))
    (hclock : ∀ x, IsLQGClock planarBrownianMotion γ hε x (F x))
    (hT : ∀ x, ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F x b))
    (hsmooth : ∀ O : Set ℂ, IsSmoothBoundedOpen O → ∀ x ∈ O,
      expectedLBMExitTime (F x) O x = ENNReal.ofReal (∫ y in O, greenFunction O x y * 2 ∂μ))
    {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)} (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {x : ℂ} (hx : x ∈ U) :
    expectedLBMExitTime (F x) U x = ∫⁻ y, ENNReal.ofReal (greenFunction U x y * 2) ∂μ := by
  set V := chartExhaustion U ψ
  have hVo : ∀ n, IsOpen (V n) := fun n => isOpen_chartSubWindow hU ψ _
  have hVm : Monotone V := monotone_chartExhaustion U ψ
  have hVU : ∀ n, V n ⊆ U := fun n => chartSubWindow_subset U ψ _
  have hVb : ∀ n, Bornology.IsBounded (V n) := fun n => hUb.subset (hVU n)
  have hcover : (⋃ n, V n) = U := hψ.iUnion_chartExhaustion
  have hVs : ∀ n, IsSmoothBoundedOpen (V n) := fun n =>
    hψ.isSmoothBoundedOpen_chartSubWindow hU hUb (subWindowRadius_pos n) (subWindowRadius_lt_one n)
  -- the left side: monotone convergence of the exit times
  have hL : Tendsto (fun n => expectedLBMExitTime (F x) (V n) x) atTop
      (𝓝 (expectedLBMExitTime (F x) U x)) := by
    unfold expectedLBMExitTime
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => aemeasurable_lbmExitTime hcont (hclock x) (hT x) (hVo n) (hVb n))
      (ae_of_all _ fun b m n hmn => lbmExitTime_mono (hVm hmn) b) ?_
    filter_upwards [hT x, Section6.ae_planarBrownian_exitTime_bounded_lt_top x hUb] with b hb hτ
    have hτn : ∀ n, ContinuousPath.exitTime (V n) b ≠ ⊤ := fun n =>
      (lt_of_le_of_lt (ContinuousPath.exitTime_mono (hVU n) b) hτ).ne
    have heq : ∀ n, lbmExitTime (F x) (V n) b =
        (Real.toNNReal (F x b (ContinuousPath.exitTime (V n) b).toNNReal) : ℝ≥0∞) := fun n =>
      HarmonicBalls.lbmExitTime_eq_clockValue (hVo n) hb (hτn n)
    simp only [heq, HarmonicBalls.lbmExitTime_eq_clockValue hU hb hτ.ne]
    have hlim : Tendsto (fun n => ContinuousPath.exitTime (V n) b) atTop
        (𝓝 (ContinuousPath.exitTime U b)) := by
      have h := Section6.tendsto_exitTime_open_iUnion hVo hVm b
      rwa [hcover] at h
    have h1 : Tendsto (fun n => (ContinuousPath.exitTime (V n) b).toNNReal) atTop
        (𝓝 (ContinuousPath.exitTime U b).toNNReal) :=
      (ENNReal.tendsto_toNNReal hτ.ne).comp hlim
    have h2 := (hb.continuous.tendsto _).comp h1
    exact ENNReal.tendsto_coe.2 ((continuous_real_toNNReal.tendsto _).comp h2)
  -- the right side: monotone convergence of the Green kernels
  have hR : Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (greenFunction (V n) x y * 2) ∂μ) atTop
      (𝓝 (∫⁻ y, ENNReal.ofReal (greenFunction U x y * 2) ∂μ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => ((measurable_greenFunction (hVo n) x).mul_const 2).ennreal_ofReal.aemeasurable)
      (ae_of_all _ fun y m n hmn => ENNReal.ofReal_le_ofReal ?_) (ae_of_all _ fun y => ?_)
    · exact mul_le_mul_of_nonneg_right
        (Section6.greenFunction_le_of_subset (hVm hmn) (hVb n) x y) zero_le_two
    · refine (ENNReal.continuous_ofReal.tendsto _).comp (Tendsto.mul_const 2 ?_)
      by_cases hyU : y ∈ U
      · by_cases hxy : x = y
        · subst hxy
          simp only [greenFunction_self]
          exact tendsto_const_nhds
        · exact tendsto_greenFunction_of_exhaustion V hVo hVm hU hUb hcover hx hyU hxy
      · have h0 : ∀ n, greenFunction (V n) x y = 0 := fun n =>
          greenFunction_of_notMem_right (fun h => hyU (hVU n h)) x
        simp only [h0, greenFunction_of_notMem_right hyU x]
        exact tendsto_const_nhds
  -- the identity on the smooth sub-windows containing `x`
  have hid : ∀ᶠ n in atTop, expectedLBMExitTime (F x) (V n) x =
      ∫⁻ y, ENNReal.ofReal (greenFunction (V n) x y * 2) ∂μ := by
    filter_upwards [hψ.eventually_mem_chartExhaustion hx] with n hxn
    have h := hsmooth (V n) (hVs n) x hxn
    have hpos : 0 < expectedLBMExitTime (F x) (V n) x := by
      unfold expectedLBMExitTime
      have hae := ae_lbmExitTime_pos (hT x) (hVo n) (hVb n) hxn
      have hm := aemeasurable_lbmExitTime hcont (hclock x) (hT x) (hVo n) (hVb n)
      rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff' hm]
      intro h0
      obtain ⟨b, hb⟩ := (hae.and h0).exists
      exact hb.1.ne' hb.2
    have hint : IntegrableOn (fun y => greenFunction (V n) x y * 2) (V n) μ := by
      by_contra hni
      rw [integral_undef hni, ENNReal.ofReal_zero] at h
      rw [h] at hpos
      exact lt_irrefl _ hpos
    rw [h, ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun y => mul_nonneg (greenFunction_nonneg (hVb n) x y) zero_le_two)]
    refine setLIntegral_eq_of_support_subset fun y hy => ?_
    rw [Function.mem_support] at hy
    by_contra hyn
    apply hy
    simp [greenFunction_of_notMem_right hyn x]
  exact tendsto_nhds_unique (hL.congr' hid) hR

end MatedCRT
