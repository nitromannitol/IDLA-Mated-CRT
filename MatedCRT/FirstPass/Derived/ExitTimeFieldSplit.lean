import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field
import HarmonicBalls.Defs.LBM
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ScaleKolm
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ConeRadial
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ConeOfFun
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.GFFMod

/-!
# The circle-average field of the quantum cone on the disc of radius `1/2`

In the mating-of-trees coupling of a valid environment, the field `h` is the circle-average embedding
`coneField X (coneRadial γ γ B B')` of the `γ`-quantum cone (Duplantier-Miller-Sheffield, Definition 4.10):
the lateral part `X - X_{|·|}(0)` of a whole-plane GFF `X` plus the radial function `w ↦ A_{log(1/|w|)}`,
where `A_u = B_u + γ u` for `u ≥ 0`. The conditioning of the radial process is on negative times only,
i.e. outside the unit disc. Put `t₀ = log (5/3)` (`splitTime`). Every circle `∂B_ε(z)` with `ε < 1/10` and
`z ∈ B_{1/2}` lies in `B_{3/5} = B_{e^{-t₀}}`, where `log(1/|w|) > t₀`, so on such circles
`A_{log(1/|w|)} = B_{t₀} + ((B_u - B_{t₀}) + γ u)` with `u = log(1/|w|)`.

* (L1, `ae_hcirc_eq_add_hTilde`) almost surely, for all `ε ∈ (0, 1/10)` and `z ∈ B_{1/2}` simultaneously,
  `h_ε(z) = B_{t₀} + h̃_ε(z)`, where `h̃_ε(z)` (`hTilde`) is the circle average at `(z, ε)` of the lateral part
  of `X` plus the circle average of the radial function `w ↦ (B_u - B_{t₀}) + γ u`, `u = log(1/|w|)`.
* (L2, `lqgClockApprox_eq_exp_mul_of_eq_add`, `ae_lqgClockApprox_hcirc_eq_exp_mul`) consequently, for a path
  that stays in `B_{1/2}` before time `t`, the approximating LQG clocks factor:
  `∫_0^t ε^{γ²/2} e^{γ h_ε(b_s)} ds = e^{γ B_{t₀}} ∫_0^t ε^{γ²/2} e^{γ h̃_ε(b_s)} ds`.

The circle average of the lateral part of `X` is written `circleAvg X ε z - ⨍_{∂B_ε(z)} X_{|·|}(0)`
(`lateralCircleAverage`); it is the distributional circle average `circleAvg (lateralPartC X) ε z` whenever the
circle `∂B_ε(z)` avoids `0` (`circleAvg_lateralPartC_eq`), and it is jointly continuous in `(ε, z)` also across
the circles through `0`, by the continuity of circle averages of functions with a logarithmic singularity at `0`
(`FieldSplit.continuousAt_circleAverage_of_logBound`).

Proof of (L1): at each fixed circle avoiding `0`, `h_ε(z)` is a.s. the distributional circle average of the cone
field (`MatedCRT.Sec1.ae_distribution_circleAvg_eq`), which splits into the circle averages of `X`, of its radial
part and of the radial profile of the cone (Bonanno, `circleAvg_cone`). Both sides of (L1) are continuous in
`(ε, z)` (the circle-average process of the quantum cone by `IsQuantumCone`, the circle averages of `X` by the
Kolmogorov modification, `ae_tendsto_mollAvgS_circleAvg`), so the identity on a countable dense set of circles
avoiding `0` extends to all circles.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

/-- The split time `t₀ = log (5/3)`: the circles `∂B_ε(z)` with `ε < 1/10` and `z ∈ B_{1/2}` lie in
`B_{3/5} = B_{e^{-t₀}}`. -/
noncomputable def splitTime : ℝ≥0 :=
  ⟨Real.log (5 / 3), Real.log_nonneg (by norm_num)⟩

/-- The radial function of the quantum cone above the split time: `w ↦ (b_u - b_{t₀}) + γ u` at
`u = log(1/|w|) = -log |w|`. -/
noncomputable def splitRadialProfile (γ : ℝ) (b : ℝ≥0 → ℝ) (w : ℂ) : ℝ :=
  b (Real.toNNReal (-Real.log ‖w‖)) - b splitTime + γ * -Real.log ‖w‖

/-- The circle average at `(z, ε)` of the lateral part `X - X_{|·|}(0)` of a field `X`: the circle average of `X`
minus the circle average of its radial part `w ↦ X_{|w|}(0)` (`MoTPort.radialFun`). -/
noncomputable def lateralCircleAverage (X : LQGMetric.DistC) (ε : ℝ) (z : ℂ) : ℝ :=
  LQGMetric.circleAvg X ε z - Real.circleAverage (MatedCRTHarmonic.MoTPort.radialFun X) z ε

/-- The field `h̃` of the split of the quantum cone on `B_{1/2}`: `h̃_ε(z)` is the circle average at `(z, ε)` of the
lateral part of `X` plus the circle average of the radial function `w ↦ (b_u - b_{t₀}) + γ u`, `u = log(1/|w|)`
(`splitRadialProfile`). -/
noncomputable def hTilde (γ : ℝ) (X : LQGMetric.DistC) (b : ℝ≥0 → ℝ) (ε : ℝ) (z : ℂ) : ℝ :=
  lateralCircleAverage X ε z + Real.circleAverage (splitRadialProfile γ b) z ε

namespace FieldSplit

/-- A circle meets a given point for at most countably many parameters, hence for almost no parameter. -/
theorem ae_circleMap_ne (c a : ℂ) {R : ℝ} (hR : R ≠ 0) : ∀ᵐ θ : ℝ, circleMap c R θ ≠ a := by
  by_cases hex : ∃ θ₀ : ℝ, circleMap c R θ₀ = a
  · obtain ⟨θ₀, hθ₀⟩ := hex
    rw [ae_iff]
    refine measure_mono_null (fun θ hθ => ?_)
      ((Set.countable_range fun n : ℤ => θ₀ + n * (2 * Real.pi)).measure_zero volume)
    have h : circleMap c R θ = circleMap c R θ₀ := by
      rw [hθ₀]
      simpa using hθ
    simp only [circleMap, add_right_inj] at h
    have hR' : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (mul_left_cancel₀ hR' h)
    refine ⟨n, ?_⟩
    have him := congrArg Complex.im hn
    simp at him
    show θ₀ + (n : ℝ) * (2 * Real.pi) = θ
    linarith
  · simp only [not_exists] at hex
    exact Eventually.of_forall hex

/-- Circle averages only see the values off a single point. -/
theorem circleAverage_congr_of_ne {f₁ f₂ : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : R ≠ 0) (a : ℂ)
    (h : ∀ w ∈ sphere c |R|, w ≠ a → f₁ w = f₂ w) :
    Real.circleAverage f₁ c R = Real.circleAverage f₂ c R := by
  unfold Real.circleAverage
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_circleMap_ne c a hR] with θ hθ _
  exact h _ (circleMap_mem_sphere' c R θ) hθ

/-- A point of the circle `∂B_r(z)` has norm at most `‖z‖ + |r|`. -/
theorem norm_lt_of_mem_sphere {z w : ℂ} {r ρ : ℝ} (hw : w ∈ sphere z |r|) (h : ‖z‖ + |r| < ρ) :
    ‖w‖ < ρ := by
  rw [mem_sphere, dist_eq_norm] at hw
  calc ‖w‖ = ‖z + (w - z)‖ := by congr 1; ring
    _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
    _ < ρ := by rw [hw]; exact h

/-- Jensen's formula for the logarithmic bound: `⨍_{∂B_r(z)} (c (-log |w|) + C) = c (-log max(|z|, r)) + C`
(as in Bonanno, `ConeArea5.circleAverage_logBound`). -/
theorem circleAverage_logBound (c C : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun w : ℂ => c * -Real.log ‖w‖ + C) z r =
      c * -Real.log (max ‖z‖ r) + C := by
  have h1 := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := z)
    hr.ne'
  simp only [sub_zero] at h1
  have h2 : Real.log r + Real.posLog (r⁻¹ * ‖z‖) = Real.log (max ‖z‖ r) := by
    rw [Real.posLog_eq_log_max_one (by positivity), ← Real.log_mul hr.ne'
      (by positivity : max 1 (r⁻¹ * ‖z‖) ≠ 0)]
    congr 1
    rw [mul_max_of_nonneg _ _ hr.le, mul_one, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul,
      max_comm]
  have e : (fun w : ℂ => c * -Real.log ‖w‖ + C) =
      fun w => ((-c) • fun w : ℂ => Real.log ‖w - 0‖) w + C := by
    funext w; simp only [Pi.smul_apply, smul_eq_mul, sub_zero]; ring
  have hi : CircleIntegrable ((-c) • fun w : ℂ => Real.log ‖w - 0‖) z r :=
    (circleIntegrable_log_norm_sub_const r).const_smul
  rw [e, Real.circleAverage_fun_add hi (circleIntegrable_const C z r), Real.circleAverage_smul,
    Real.circleAverage_const]
  simp only [sub_zero] at h1 ⊢
  rw [smul_eq_mul, h1, h2]
  ring

/-- The logarithmic bound is integrable on every circle. -/
theorem circleIntegrable_logBound (c C : ℝ) (z : ℂ) (r : ℝ) :
    CircleIntegrable (fun w : ℂ => c * -Real.log ‖w‖ + C) z r := by
  have e : (fun w : ℂ => c * -Real.log ‖w‖ + C) =
      fun w => ((-c) • fun w : ℂ => Real.log ‖w - 0‖) w + C := by
    funext w; simp only [Pi.smul_apply, smul_eq_mul, sub_zero]; ring
  rw [e]
  exact IntervalIntegrable.add ((circleIntegrable_log_norm_sub_const r).const_smul (a := -c))
    (circleIntegrable_const C z r)

/-- A measurable function bounded by a logarithmic singularity at `0` on the punctured unit disc is integrable
on every circle inside the unit disc. -/
theorem circleIntegrable_of_abs_le_logBound {g : ℂ → ℝ} (hgm : Measurable g) {c C : ℝ}
    (hgb : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → |g w| ≤ c * -Real.log ‖w‖ + C)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : ‖z‖ + r < 1) : CircleIntegrable g z r := by
  refine IntervalIntegrable.mono_fun (circleIntegrable_logBound c C z r)
    (hgm.comp (continuous_circleMap z r).measurable).aestronglyMeasurable ?_
  refine ae_restrict_of_ae ?_
  filter_upwards [ae_circleMap_ne z 0 hr.ne'] with θ hθ
  have hw : ‖circleMap z r θ‖ < 1 :=
    norm_lt_of_mem_sphere (circleMap_mem_sphere' z r θ) (by rw [abs_of_pos hr]; exact hzr)
  simp only [Real.norm_eq_abs]
  exact (hgb _ hθ hw).trans (le_abs_self _)

/-- **Lower semicontinuity of circle averages of nonnegative functions continuous off `0`**: truncate at
level `M`, use dominated convergence for the truncations (continuous off a null set of parameters), and let
`M → ∞`. -/
theorem eventually_lt_circleAverage_of_nonneg {f : ℂ → ℝ} (hf0 : ∀ w, 0 ≤ f w)
    (hfm : Measurable f) (hfc : ContinuousOn f {0}ᶜ) {r₀ : ℝ} {z₀ : ℂ} (hr₀ : 0 < r₀)
    (hfi : ∀ᶠ p in 𝓝 ((r₀, z₀) : ℝ × ℂ), CircleIntegrable f p.2 p.1) {a : ℝ}
    (ha : a < Real.circleAverage f z₀ r₀) :
    ∀ᶠ p in 𝓝 ((r₀, z₀) : ℝ × ℂ), a < Real.circleAverage f p.2 p.1 := by
  have hmeasM : ∀ M : ℕ, Measurable fun w => min (f w) (M : ℝ) := fun M =>
    hfm.min measurable_const
  have hnormM : ∀ (M : ℕ) (w : ℂ), ‖min (f w) (M : ℝ)‖ ≤ ‖f w‖ ∧ ‖min (f w) (M : ℝ)‖ ≤ M := by
    intro M w
    have h0 : 0 ≤ min (f w) (M : ℝ) := le_min (hf0 w) (Nat.cast_nonneg M)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (hf0 w)]
    exact ⟨min_le_left _ _, min_le_right _ _⟩
  -- the truncated averages converge to the average at `(r₀, z₀)`
  have hconv : Tendsto (fun M : ℕ => Real.circleAverage (fun w => min (f w) (M : ℝ)) z₀ r₀)
      atTop (𝓝 (Real.circleAverage f z₀ r₀)) := by
    have hi : IntervalIntegrable (fun θ => f (circleMap z₀ r₀ θ)) volume 0 (2 * Real.pi) :=
      hfi.self_of_nhds
    simp only [Real.circleAverage]
    refine Tendsto.const_smul ?_ _
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun θ => ‖f (circleMap z₀ r₀ θ)‖) ?_ ?_ hi.norm ?_
    · exact Eventually.of_forall fun M =>
        ((hmeasM M).comp (continuous_circleMap z₀ r₀).measurable).aestronglyMeasurable
    · exact Eventually.of_forall fun M => Eventually.of_forall fun θ _ => (hnormM M _).1
    · refine Eventually.of_forall fun θ _ => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈f (circleMap z₀ r₀ θ)⌉₊] with M hM
      exact (min_eq_left ((Nat.le_ceil _).trans (Nat.cast_le.2 hM))).symm
  obtain ⟨M, hM⟩ := (hconv.eventually (lt_mem_nhds ha)).exists
  -- the truncated average is continuous at `(r₀, z₀)`
  have hcont : ContinuousAt (fun p : ℝ × ℂ =>
      Real.circleAverage (fun w => min (f w) (M : ℝ)) p.2 p.1) (r₀, z₀) := by
    simp only [Real.circleAverage, smul_eq_mul]
    refine continuousAt_const.mul ?_
    refine intervalIntegral.continuousAt_of_dominated_interval
      (bound := fun _ => (M : ℝ)) ?_ ?_ intervalIntegrable_const ?_
    · exact Eventually.of_forall fun p =>
        ((hmeasM M).comp (continuous_circleMap p.2 p.1).measurable).aestronglyMeasurable
    · exact Eventually.of_forall fun p => Eventually.of_forall fun θ _ => (hnormM M _).2
    · filter_upwards [ae_circleMap_ne z₀ 0 hr₀.ne'] with θ hθ _
      have hc : Continuous fun p : ℝ × ℂ => circleMap p.2 p.1 θ := by
        unfold circleMap
        fun_prop
      have hfa : ContinuousAt (fun w => min (f w) (M : ℝ)) (circleMap z₀ r₀ θ) :=
        (continuous_id.min continuous_const).continuousAt.comp (f := f)
          (hfc.continuousAt (isOpen_compl_singleton.mem_nhds hθ))
      exact ContinuousAt.comp (x := ((r₀, z₀) : ℝ × ℂ)) hfa hc.continuousAt
  filter_upwards [hcont.eventually (lt_mem_nhds hM), hfi] with p hp hpi
  refine hp.trans_le (Real.circleAverage_mono ?_ hpi fun w _ => min_le_left _ _)
  exact IntervalIntegrable.mono_fun hpi
    ((hmeasM M).comp (continuous_circleMap p.2 p.1).measurable).aestronglyMeasurable
    (Eventually.of_forall fun θ => (hnormM M _).1)

/-- One half of the continuity of circle averages of a function with a logarithmic singularity at `0`:
`L + g ≥ 0` for the logarithmic bound `L`, whose circle averages are explicit and continuous. -/
theorem eventually_lt_circleAverage_of_logBound {g : ℂ → ℝ} (hgm : Measurable g)
    (hgc : ContinuousOn g {0}ᶜ) {c C : ℝ}
    (hgb : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → |g w| ≤ c * -Real.log ‖w‖ + C)
    {r₀ : ℝ} {z₀ : ℂ} (hr₀ : 0 < r₀) (hz₀ : ‖z₀‖ + r₀ < 1) {a : ℝ}
    (ha : a < Real.circleAverage g z₀ r₀) :
    ∀ᶠ p in 𝓝 ((r₀, z₀) : ℝ × ℂ), a < Real.circleAverage g p.2 p.1 := by
  have hN : ∀ᶠ p in 𝓝 ((r₀, z₀) : ℝ × ℂ), 0 < p.1 ∧ ‖p.2‖ + p.1 < 1 := by
    have hc : Continuous fun p : ℝ × ℂ => ‖p.2‖ + p.1 := by fun_prop
    exact ((continuous_fst.tendsto _).eventually (lt_mem_nhds hr₀)).and
      ((hc.tendsto _).eventually (gt_mem_nhds hz₀))
  have hLm : Measurable fun w : ℂ => c * -Real.log ‖w‖ + C :=
    ((Real.measurable_log.comp measurable_norm).neg.const_mul c).add_const C
  have hLc : ContinuousOn (fun w : ℂ => c * -Real.log ‖w‖ + C) {0}ᶜ := by
    refine (continuousOn_const.mul ?_).add continuousOn_const
    exact (Real.continuousOn_log.comp continuous_norm.continuousOn fun w hw => by
      simpa using hw).neg
  have hgi : ∀ (r : ℝ) (z : ℂ), 0 < r → ‖z‖ + r < 1 → CircleIntegrable g z r :=
    fun r z hr hzr => circleIntegrable_of_abs_le_logBound hgm hgb hr hzr
  -- the nonnegative function `f = max 0 (L + g)` equals `L + g` on the punctured unit disc
  have hfeq : ∀ (r : ℝ) (z : ℂ), 0 < r → ‖z‖ + r < 1 →
      Real.circleAverage (fun w => max 0 ((c * -Real.log ‖w‖ + C) + g w)) z r =
        Real.circleAverage (fun w : ℂ => c * -Real.log ‖w‖ + C) z r +
          Real.circleAverage g z r := by
    intro r z hr hzr
    rw [← Real.circleAverage_fun_add (circleIntegrable_logBound c C z r) (hgi r z hr hzr)]
    refine circleAverage_congr_of_ne hr.ne' 0 fun w hw hw0 => ?_
    have hw1 : ‖w‖ < 1 := norm_lt_of_mem_sphere hw (by rw [abs_of_pos hr]; exact hzr)
    have hb := hgb w hw0 hw1
    have hng := neg_abs_le (g w)
    exact max_eq_right (by linarith)
  have hf0 : ∀ w : ℂ, 0 ≤ max 0 ((c * -Real.log ‖w‖ + C) + g w) := fun w => le_max_left _ _
  have hfm : Measurable fun w : ℂ => max 0 ((c * -Real.log ‖w‖ + C) + g w) :=
    measurable_const.max (hLm.add hgm)
  have hfc : ContinuousOn (fun w : ℂ => max 0 ((c * -Real.log ‖w‖ + C) + g w)) {0}ᶜ :=
    (continuous_const.max continuous_id).comp_continuousOn (hLc.add hgc)
  have hfi : ∀ᶠ p in 𝓝 ((r₀, z₀) : ℝ × ℂ),
      CircleIntegrable (fun w : ℂ => max 0 ((c * -Real.log ‖w‖ + C) + g w)) p.2 p.1 := by
    filter_upwards [hN] with p hp
    refine IntervalIntegrable.mono_fun
      ((IntervalIntegrable.norm (circleIntegrable_logBound c C p.2 p.1)).add
        (IntervalIntegrable.norm (hgi p.1 p.2 hp.1 hp.2)))
      (hfm.comp (continuous_circleMap _ _).measurable).aestronglyMeasurable
      (Eventually.of_forall fun θ => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_left _ _),
      abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
    exact max_le (add_nonneg (abs_nonneg _) (abs_nonneg _))
      ((le_abs_self _).trans (abs_add_le _ _))
  -- the circle averages of the logarithmic bound are continuous
  have hLcont : ContinuousAt (fun p : ℝ × ℂ => c * -Real.log (max ‖p.2‖ p.1) + C) (r₀, z₀) := by
    have hpos : max ‖z₀‖ r₀ ≠ 0 := (lt_max_of_lt_right hr₀).ne'
    have hm : ContinuousAt (fun p : ℝ × ℂ => max ‖p.2‖ p.1) (r₀, z₀) :=
      (continuous_snd.norm.max continuous_fst).continuousAt
    exact (continuousAt_const.mul (hm.log hpos).neg).add continuousAt_const
  have hδ : 0 < (Real.circleAverage g z₀ r₀ - a) / 2 := by linarith
  have hlt : (c * -Real.log (max ‖z₀‖ r₀) + C) + a + (Real.circleAverage g z₀ r₀ - a) / 2 <
      Real.circleAverage (fun w => max 0 ((c * -Real.log ‖w‖ + C) + g w)) z₀ r₀ := by
    rw [hfeq r₀ z₀ hr₀ hz₀, circleAverage_logBound c C z₀ hr₀]
    linarith
  have hLev : ∀ᶠ p in 𝓝 ((r₀, z₀) : ℝ × ℂ), c * -Real.log (max ‖p.2‖ p.1) + C <
      (c * -Real.log (max ‖z₀‖ r₀) + C) + (Real.circleAverage g z₀ r₀ - a) / 2 :=
    hLcont.eventually (gt_mem_nhds (show c * -Real.log (max ‖z₀‖ r₀) + C <
      (c * -Real.log (max ‖z₀‖ r₀) + C) + (Real.circleAverage g z₀ r₀ - a) / 2 by linarith))
  filter_upwards [eventually_lt_circleAverage_of_nonneg hf0 hfm hfc hr₀ hfi hlt, hN, hLev]
    with p h1 h2 h3
  rw [hfeq p.1 p.2 h2.1 h2.2, circleAverage_logBound c C p.2 h2.1] at h1
  linarith

/-- **Continuity of circle averages of a function with a logarithmic singularity at `0`**, jointly in the radius
and the centre, at every circle inside the unit disc, including the circles through `0`. -/
theorem continuousAt_circleAverage_of_logBound {g : ℂ → ℝ} (hgm : Measurable g)
    (hgc : ContinuousOn g {0}ᶜ) {c C : ℝ}
    (hgb : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → |g w| ≤ c * -Real.log ‖w‖ + C)
    {r₀ : ℝ} {z₀ : ℂ} (hr₀ : 0 < r₀) (hz₀ : ‖z₀‖ + r₀ < 1) :
    ContinuousAt (fun p : ℝ × ℂ => Real.circleAverage g p.2 p.1) (r₀, z₀) := by
  have hneg : ∀ (z : ℂ) (r : ℝ),
      Real.circleAverage (fun w => -g w) z r = -Real.circleAverage g z r := by
    intro z r
    simp only [Real.circleAverage, intervalIntegral.integral_neg, smul_neg]
  refine tendsto_order.2 ⟨fun a ha => eventually_lt_circleAverage_of_logBound hgm hgc hgb hr₀ hz₀ ha,
    fun a ha => ?_⟩
  have ha' : Real.circleAverage g z₀ r₀ < a := ha
  have h := eventually_lt_circleAverage_of_logBound (g := fun w => -g w) hgm.neg hgc.neg
    (fun w hw0 hw1 => by rw [abs_neg]; exact hgb w hw0 hw1) hr₀ hz₀ (a := -a)
    (by rw [hneg]; linarith)
  filter_upwards [h] with p hp
  rw [hneg] at hp
  show Real.circleAverage g p.2 p.1 < a
  linarith

/-- Continuity of the radial function of the quantum cone above the split time, off `0`. -/
theorem continuousOn_splitRadialProfile {γ : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b) :
    ContinuousOn (splitRadialProfile γ b) {0}ᶜ := by
  have hlog : ContinuousOn (fun w : ℂ => -Real.log ‖w‖) {0}ᶜ :=
    (Real.continuousOn_log.comp continuous_norm.continuousOn fun w hw => by simpa using hw).neg
  show ContinuousOn (fun w : ℂ => b (Real.toNNReal (-Real.log ‖w‖)) - b splitTime +
    γ * -Real.log ‖w‖) {0}ᶜ
  exact (((hb.comp continuous_real_toNNReal).comp_continuousOn hlog).sub continuousOn_const).add
    (continuousOn_const.mul hlog)

/-- Measurability of the radial function of the quantum cone above the split time. -/
theorem measurable_splitRadialProfile {γ : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b) :
    Measurable (splitRadialProfile γ b) := by
  have hlog : Measurable fun w : ℂ => -Real.log ‖w‖ := (Real.measurable_log.comp measurable_norm).neg
  show Measurable fun w : ℂ => b (Real.toNNReal (-Real.log ‖w‖)) - b splitTime + γ * -Real.log ‖w‖
  exact ((hb.measurable.comp (measurable_real_toNNReal.comp hlog)).sub_const _).add
    (hlog.const_mul γ)

/-- The logarithmic bound of the radial function above the split time, from a linear bound on `b`. -/
theorem abs_splitRadialProfile_le {γ : ℝ} {b : ℝ≥0 → ℝ} {C : ℝ}
    (hC : ∀ t : ℝ≥0, |b t| ≤ 1 * t + C) {w : ℂ} (hw1 : ‖w‖ < 1) :
    |splitRadialProfile γ b w| ≤ (1 + |γ|) * -Real.log ‖w‖ + (C + |b splitTime|) := by
  have hu : 0 ≤ -Real.log ‖w‖ := neg_nonneg.2 (Real.log_nonpos (norm_nonneg w) hw1.le)
  have h1 := hC (Real.toNNReal (-Real.log ‖w‖))
  rw [Real.coe_toNNReal _ hu] at h1
  obtain ⟨h1l, h1r⟩ := abs_le.1 h1
  have hγ1 : γ * -Real.log ‖w‖ ≤ |γ| * -Real.log ‖w‖ :=
    mul_le_mul_of_nonneg_right (le_abs_self γ) hu
  have hγ2 : -|γ| * -Real.log ‖w‖ ≤ γ * -Real.log ‖w‖ :=
    mul_le_mul_of_nonneg_right (neg_abs_le γ) hu
  have hb1 := le_abs_self (b splitTime)
  have hb2 := neg_abs_le (b splitTime)
  rw [abs_le]
  unfold splitRadialProfile
  constructor <;> linarith

/-- On the closed unit disc the radial profile of the cone is `b_{t₀}` plus the radial function above the split
time. -/
theorem coneRadial_neg_log_eq_add_splitRadialProfile (γ : ℝ) (b b' : ℝ≥0 → ℝ) {w : ℂ}
    (hw : ‖w‖ ≤ 1) :
    MatedCRTHarmonic.MatedCRT.coneRadial γ γ b b' (-Real.log ‖w‖) =
      b splitTime + splitRadialProfile γ b w := by
  have h0 : 0 ≤ -Real.log ‖w‖ := neg_nonneg.2 (Real.log_nonpos (norm_nonneg w) hw)
  simp only [MatedCRTHarmonic.MatedCRT.coneRadial, h0, ↓reduceIte, splitRadialProfile]
  ring

end FieldSplit

open FieldSplit

/-- Off the circles through `0`, `lateralCircleAverage X ε z` is the distributional circle average of the lateral
part `lateralPartC X = X - X_{|·|}(0)` (given the convergence of the mollified circle averages of `X` at
`(z, ε)`). -/
theorem circleAvg_lateralPartC_eq {X : LQGMetric.DistC} {z : ℂ} {ρ : ℝ}
    (hX : Tendsto (fun s => MatedCRTHarmonic.LQGCoord.mollAvgS X s z ρ) (𝓝[>] 0)
      (𝓝 (LQGMetric.circleAvg X ρ z)))
    (hl : LocallyIntegrable (MatedCRTHarmonic.MoTPort.radialFun X) volume)
    (hc : ContinuousOn (MatedCRTHarmonic.MoTPort.radialFun X) {0}ᶜ) (hρ : 0 < ρ) (hz : ‖z‖ ≠ ρ) :
    LQGMetric.circleAvg (MatedCRTHarmonic.MoTPort.lateralPartC X) ρ z =
      lateralCircleAverage X ρ z := by
  unfold lateralCircleAverage
  apply MatedCRTHarmonic.LQGCoord.circleAvg_eq_of_tendsto_mollAvgS
  have h := hX.sub (MatedCRTHarmonic.LQGCoord.tendsto_mollAvgS_ofFunC hl isOpen_compl_singleton hc hρ
    (MatedCRTHarmonic.LQGCoord.sphere_subset_compl_zero hz))
  refine h.congr fun s => ?_
  rw [MatedCRTHarmonic.LQGCoord.mollAvgS_eq, MatedCRTHarmonic.LQGCoord.mollAvgS_eq,
    MatedCRTHarmonic.LQGCoord.mollAvgS_eq]
  rfl

/-- **(L1) The field split on `B_{1/2}`.** Under the mating-of-trees coupling, almost surely, for all
`ε ∈ (0, 1/10)` and `z ∈ B_{1/2}`, the circle average `h_ε(z)` of the quantum cone is `B_{t₀} + h̃_ε(z)`. -/
theorem ae_hcirc_eq_add_hTilde {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η' η₀ : Ω → C(ℝ, ℂ)}
    (hcpl : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀
      S.bm)
    (hlink : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC,
      S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) :
    ∀ᵐ ω ∂S.P, ∀ ε ∈ Ioo (0 : ℝ) (1 / 10), ∀ z ∈ ball (0 : ℂ) (1 / 2),
      S.hcirc ω ε z = B splitTime ω + hTilde γ (X ω) (fun u => B u ω) ε z := by
  have hX := hcpl.gff
  have hB := hcpl.bm_B
  have hB' := hcpl.bm_B'
  have hαQ : γ < MatedCRTHarmonic.CellScaling.lqgQ γ := by
    show γ < 2 / γ + γ / 2
    have h4 : γ / 2 < 2 / γ := by
      rw [div_lt_div_iff₀ (by norm_num) hγ]
      nlinarith
    linarith
  -- a countable dense set of radius-centre pairs, and the circles avoiding `0`
  obtain ⟨T, hTc, hTd⟩ := TopologicalSpace.exists_countable_dense (ℝ × ℂ)
  have hcount : Countable ↥(T ∩ {p : ℝ × ℂ | 0 < p.1 ∧ ‖p.2‖ ≠ p.1}) :=
    (hTc.mono inter_subset_left).to_subtype
  have hfix : ∀ᵐ ω ∂S.P, ∀ q : ↥(T ∩ {p : ℝ × ℂ | 0 < p.1 ∧ ‖p.2‖ ≠ p.1}),
      LQGMetric.circleAvg (MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) q.1.1 q.1.2 =
        S.hcirc ω q.1.1 q.1.2 :=
    ae_all_iff.2 fun q => MatedCRT.Sec1.ae_distribution_circleAvg_eq hS hlink q.2.2.1 q.2.2.2
  filter_upwards [hfix, hS.isQuantumCone.ae_continuousOn_circle,
    MatedCRTHarmonic.LQGCoord.ae_radialGood hX hB hB' hαQ,
    MatedCRTHarmonic.LQGCoord.ae_tendsto_mollAvgS_circleAvg hX, hB.cont]
    with ω hωfix hωc hωr hωm hωB
  intro ε hε z hz
  -- regularity of the profiles
  have hc₁ := MatedCRTHarmonic.LQGCoord.continuousOn_radialAvg hωr.good
  have hc₂ := MatedCRTHarmonic.LQGCoord.continuousOn_coneProfile hωr
  obtain ⟨C₁, hC₁⟩ := MatedCRTHarmonic.LQGCoord.abs_radialAvg_le hωr one_pos
  obtain ⟨C₃, hC₃⟩ := MatedCRTHarmonic.LQGCoord.abs_coneProfile_le hωr one_pos
  obtain ⟨C₂, hC₂⟩ := hωr.boundB 1 one_pos
  have hl₁ := MatedCRTHarmonic.LQGCoord.locallyIntegrable_of_logBound
    (MatedCRTHarmonic.LQGCoord.measurable_radialAvg (X ω)) hc₁ hC₁
  have hl₂ := MatedCRTHarmonic.LQGCoord.locallyIntegrable_of_logBound
    (MatedCRTHarmonic.LQGCoord.measurable_coneProfile hωr) hc₂ (fun w h0 h1 => (hC₃ w h0 h1).1)
  have hm₄ : Measurable (splitRadialProfile γ (fun u => B u ω)) := measurable_splitRadialProfile hωB
  have hc₄ : ContinuousOn (splitRadialProfile γ (fun u => B u ω)) {0}ᶜ :=
    continuousOn_splitRadialProfile hωB
  have hb₄ : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → |splitRadialProfile γ (fun u => B u ω) w| ≤
      (1 + |γ|) * -Real.log ‖w‖ + (C₂ + |B splitTime ω|) :=
    fun w _ hw1 => abs_splitRadialProfile_le hC₂ hw1
  -- the two sides, as functions of `(ε, z)`
  have hFc : ContinuousOn (fun p : ℝ × ℂ => S.hcirc ω p.1 p.2)
      (Ioo (0 : ℝ) (1 / 10) ×ˢ ball (0 : ℂ) (1 / 2)) :=
    hωc.mono fun p hp => ⟨hp.1.1, mem_univ _⟩
  have hGc : ContinuousOn
      (fun p : ℝ × ℂ => B splitTime ω + hTilde γ (X ω) (fun u => B u ω) p.1 p.2)
      (Ioo (0 : ℝ) (1 / 10) ×ˢ ball (0 : ℂ) (1 / 2)) := by
    rintro ⟨r, w⟩ ⟨⟨hr0, hr1⟩, hw⟩
    have hw' : ‖w‖ < 1 / 2 := mem_ball_zero_iff.1 hw
    have hwr : ‖w‖ + r < 1 := by linarith
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun p : ℝ × ℂ => LQGMetric.circleAvg (X ω) p.1 p.2) (r, w) :=
      hωm.1.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hr0, mem_univ _⟩)
    have h2 := continuousAt_circleAverage_of_logBound
      (g := MatedCRTHarmonic.MoTPort.radialFun (X ω))
      (MatedCRTHarmonic.LQGCoord.measurable_radialAvg (X ω)) hc₁ hC₁ hr0 hwr
    have h3 := continuousAt_circleAverage_of_logBound hm₄ hc₄ hb₄ hr0 hwr
    exact continuousAt_const.add ((h1.sub h2).add h3)
  -- the identity on the circles of the dense set avoiding `0`
  have hEq : EqOn (fun p : ℝ × ℂ => S.hcirc ω p.1 p.2)
      (fun p : ℝ × ℂ => B splitTime ω + hTilde γ (X ω) (fun u => B u ω) p.1 p.2)
      ((Ioo (0 : ℝ) (1 / 10) ×ˢ ball (0 : ℂ) (1 / 2)) ∩ {p : ℝ × ℂ | ‖p.2‖ ≠ p.1} ∩ T) := by
    rintro ⟨r, w⟩ ⟨⟨⟨⟨hr0, hr1⟩, hw⟩, hne⟩, hT⟩
    have hw' : ‖w‖ < 1 / 2 := mem_ball_zero_iff.1 hw
    have hwr : ‖w‖ + r < 1 := by linarith
    have hfx : LQGMetric.circleAvg (MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) r w =
        S.hcirc ω r w := hωfix ⟨(r, w), hT, hr0, hne⟩
    have hdec : LQGMetric.circleAvg (MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) r w =
        LQGMetric.circleAvg (X ω) r w -
          Real.circleAverage (MatedCRTHarmonic.CellScaling.radialAvg (X ω)) w r +
          Real.circleAverage (MatedCRTHarmonic.LQGCoord.coneProfile γ γ (fun u => B u ω)
            (fun u => B' u ω)) w r := by
      rw [show MatedCRTHarmonic.MatedCRT.coneField (X ω)
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) = _ from
        MatedCRTHarmonic.LQGCoord.coneField_eq_cone γ γ (X ω) (fun u => B u ω) (fun u => B' u ω)]
      exact MatedCRTHarmonic.LQGCoord.circleAvg_cone hl₁ hl₂ hc₁ hc₂ hr0 hne (hωm.2 r hr0 w)
    have hcp : Real.circleAverage (MatedCRTHarmonic.LQGCoord.coneProfile γ γ (fun u => B u ω)
        (fun u => B' u ω)) w r =
        B splitTime ω + Real.circleAverage (splitRadialProfile γ (fun u => B u ω)) w r := by
      have hsp : EqOn (MatedCRTHarmonic.LQGCoord.coneProfile γ γ (fun u => B u ω) (fun u => B' u ω))
          (fun x => B splitTime ω + splitRadialProfile γ (fun u => B u ω) x) (sphere w |r|) := by
        intro x hx
        have hx1 : ‖x‖ < 1 := norm_lt_of_mem_sphere hx (by rw [abs_of_pos hr0]; exact hwr)
        exact coneRadial_neg_log_eq_add_splitRadialProfile γ (fun u => B u ω) (fun u => B' u ω)
          hx1.le
      rw [Real.circleAverage_congr_sphere hsp, Real.circleAverage_fun_add
        (circleIntegrable_const _ _ _) (circleIntegrable_of_abs_le_logBound hm₄ hb₄ hr0 hwr),
        Real.circleAverage_const]
    show S.hcirc ω r w = B splitTime ω + hTilde γ (X ω) (fun u => B u ω) r w
    rw [← hfx, hdec, hcp]
    simp only [hTilde, lateralCircleAverage]
    rw [show Real.circleAverage (MatedCRTHarmonic.MoTPort.radialFun (X ω)) w r =
      Real.circleAverage (MatedCRTHarmonic.CellScaling.radialAvg (X ω)) w r from rfl]
    ring
  -- density of the circles of the dense set avoiding `0`
  have hVo : IsOpen ((Ioo (0 : ℝ) (1 / 10) ×ˢ ball (0 : ℂ) (1 / 2)) ∩
      {p : ℝ × ℂ | ‖p.2‖ ≠ p.1}) :=
    (isOpen_Ioo.prod isOpen_ball).inter (isOpen_ne_fun continuous_snd.norm continuous_fst)
  have hWV : Ioo (0 : ℝ) (1 / 10) ×ˢ ball (0 : ℂ) (1 / 2) ⊆
      closure ((Ioo (0 : ℝ) (1 / 10) ×ˢ ball (0 : ℂ) (1 / 2)) ∩ {p : ℝ × ℂ | ‖p.2‖ ≠ p.1}) := by
    rintro ⟨r, w⟩ hp
    by_cases hne : ‖w‖ = r
    · obtain ⟨⟨hr0, hr1⟩, hw⟩ := hp
      have ht : Tendsto (fun δ : ℝ => ((r + δ, w) : ℝ × ℂ)) (𝓝[>] 0) (𝓝 (r, w)) := by
        have hcont : Continuous fun δ : ℝ => ((r + δ, w) : ℝ × ℂ) := by fun_prop
        have h0 := hcont.tendsto 0
        simp only [add_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto ht ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 10 - r by linarith)] with δ hδ
      obtain ⟨hδ0, hδ1⟩ := hδ
      refine ⟨⟨⟨by linarith, by linarith⟩, hw⟩, ?_⟩
      show ‖w‖ ≠ r + δ
      exact (show ‖w‖ < r + δ by rw [hne]; linarith).ne
    · exact subset_closure ⟨hp, hne⟩
  have hts : Ioo (0 : ℝ) (1 / 10) ×ˢ ball (0 : ℂ) (1 / 2) ⊆
      closure ((Ioo (0 : ℝ) (1 / 10) ×ˢ ball (0 : ℂ) (1 / 2)) ∩ {p : ℝ × ℂ | ‖p.2‖ ≠ p.1} ∩ T) :=
    hWV.trans (closure_minimal (hTd.open_subset_closure_inter hVo) isClosed_closure)
  exact hEq.of_subset_closure hFc hGc (fun p hp => hp.1.1) hts
    (show ((ε, z) : ℝ × ℂ) ∈ Ioo (0 : ℝ) (1 / 10) ×ˢ ball (0 : ℂ) (1 / 2) from ⟨hε, hz⟩)

/-- **(L1), with the coupling of the environment.** For a valid environment and `0 < γ < 2`, the mating-of-trees
coupling `(X, B, B', …)` of `S.IsValid` can be chosen so that almost surely `h_ε(z) = B_{t₀} + h̃_ε(z)` for all
`ε ∈ (0, 1/10)` and `z ∈ B_{1/2}`. -/
theorem exists_ae_hcirc_eq_add_hTilde {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ (X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
      (ηL η' η₀ : Ω → C(ℝ, ℂ)),
      MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀ S.bm ∧
      (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC,
        S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (X ω)
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) ∧
      ∀ᵐ ω ∂S.P, ∀ ε ∈ Ioo (0 : ℝ) (1 / 10), ∀ z ∈ ball (0 : ℂ) (1 / 2),
        S.hcirc ω ε z = B splitTime ω + hTilde γ (X ω) (fun u => B u ω) ε z := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hcpl, hae⟩ := hS.matingOfTrees
  have hlink : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC,
      S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ := by
    filter_upwards [hae] with ω hω
    exact hω.2
  exact ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hcpl, hlink,
    ae_hcirc_eq_add_hTilde hS hγ hγ2 hcpl hlink⟩

/-- **(L2) The approximation split, deterministic form.** If `h_ε = c + h̃_ε` on a set `D` and the path `b`
stays in `D` at all times `s < t`, then the approximating LQG clocks factor:
`∫_0^t ε^{γ²/2} e^{γ h_ε(b_s)} ds = e^{γ c} ∫_0^t ε^{γ²/2} e^{γ h̃_ε(b_s)} ds`. -/
theorem lqgClockApprox_eq_exp_mul_of_eq_add {γ c ε : ℝ} {h hT : ℝ → ℂ → ℝ} {D : Set ℂ}
    (hD : ∀ z ∈ D, h ε z = c + hT ε z) {b : ContinuousPath ℂ} {t : ℝ≥0}
    (hb : ∀ s : ℝ≥0, s < t → b s ∈ D) :
    HarmonicBalls.lqgClockApprox γ h ε b t =
      Real.exp (γ * c) * HarmonicBalls.lqgClockApprox γ hT ε b t := by
  unfold HarmonicBalls.lqgClockApprox
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ s : ℝ, s ≠ (t : ℝ) := by
    rw [ae_iff]
    exact measure_mono_null (fun s hs => Set.mem_singleton_iff.2 (by simpa using hs))
      (measure_singleton (t : ℝ))
  filter_upwards [hne] with s hst hs
  rw [Set.uIoc_of_le t.coe_nonneg] at hs
  have hlt : s.toNNReal < t := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1.le]
    exact lt_of_le_of_ne hs.2 hst
  rw [hD _ (hb _ hlt), mul_add, Real.exp_add]
  ring

/-- **(L2) The approximation split.** Under the mating-of-trees coupling, almost surely, for every
`ε ∈ (0, 1/10)`, every path `b` with `b_s ∈ B_{1/2}` for all `s < t` (e.g. `t` at most the exit time of `b` from
`B_{1/2}`): `lqgClockApprox γ h ε b t = e^{γ B_{t₀}} lqgClockApprox γ h̃ ε b t`. -/
theorem ae_lqgClockApprox_hcirc_eq_exp_mul {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η' η₀ : Ω → C(ℝ, ℂ)}
    (hcpl : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀
      S.bm)
    (hlink : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC,
      S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) :
    ∀ᵐ ω ∂S.P, ∀ ε ∈ Ioo (0 : ℝ) (1 / 10), ∀ (b : ContinuousPath ℂ) (t : ℝ≥0),
      (∀ s : ℝ≥0, s < t → b s ∈ ball (0 : ℂ) (1 / 2)) →
      HarmonicBalls.lqgClockApprox γ (S.hcirc ω) ε b t =
        Real.exp (γ * B splitTime ω) *
          HarmonicBalls.lqgClockApprox γ (hTilde γ (X ω) (fun u => B u ω)) ε b t := by
  filter_upwards [ae_hcirc_eq_add_hTilde hS hγ hγ2 hcpl hlink] with ω hω ε hε b t hb
  exact lqgClockApprox_eq_exp_mul_of_eq_add (fun z hz => hω ε hε z hz) hb

/-- **(L2) at the dyadic scales `2^{-k} < 1/10`.** -/
theorem ae_lqgClockApprox_dyadic_hcirc_eq_exp_mul {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ)
    (hγ2 : γ < 2) {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η' η₀ : Ω → C(ℝ, ℂ)}
    (hcpl : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀
      S.bm)
    (hlink : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC,
      S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) :
    ∀ᵐ ω ∂S.P, ∀ k : ℕ, HarmonicBalls.dyadicScale k < 1 / 10 →
      ∀ (b : ContinuousPath ℂ) (t : ℝ≥0), (∀ s : ℝ≥0, s < t → b s ∈ ball (0 : ℂ) (1 / 2)) →
      HarmonicBalls.lqgClockApprox γ (S.hcirc ω) (HarmonicBalls.dyadicScale k) b t =
        Real.exp (γ * B splitTime ω) *
          HarmonicBalls.lqgClockApprox γ (hTilde γ (X ω) (fun u => B u ω))
            (HarmonicBalls.dyadicScale k) b t := by
  filter_upwards [ae_lqgClockApprox_hcirc_eq_exp_mul hS hγ hγ2 hcpl hlink] with ω hω k hk
  have hpos : 0 < HarmonicBalls.dyadicScale k := by
    unfold HarmonicBalls.dyadicScale
    positivity
  exact hω _ ⟨hpos, hk⟩

end MatedCRT
