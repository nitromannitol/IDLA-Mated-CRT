import MatedCRT.FirstPass.Derived.LQGMeasureChartSmooth
import MatedCRT.FirstPass.Derived.ZeroConeAreaCoordinateChangeProof
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Radial
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_2

/-!
# Radial pairings of a distribution with continuous circle averages

For a distribution `T` on `ℂ` whose mollified circle averages extend continuously to the scale `0`
(`MatedCRT.ConeAreaCovariance.ScaleRegular`) and whose circle averages grow at most logarithmically as the radius
tends to `0`, the pairing of `T` with a smooth test function `v(z − ·)`, `v` radial, is the radial integral of its
circle averages (Sheffield–Wang, arXiv:1605.06171v2, p. 10: `h ∗ f_ε(z) = 2π ∫_0^ε h_r(z) f_ε(r) r dr`;
Duplantier–Sheffield, arXiv:0808.1560v2, §3.1, for the circle averages):
`T(v(z − ·)) = ∫_0^∞ 2π r v(r) T_r(z) dr`.

This is the identity of the continuous circle-average process used in the first localization step of the
coordinate change of the LQG measure (the decomposition of the field on a disc into a zero-boundary GFF and a
continuous function, `MatedCRT.LQGMeasureChart.exists_discMarkovDecomposition_wholePlane`).

* `mollAvgS_eq_integral_circleAvg`: the mollified circle average at scale `s` is the average over the centres
  `w + v`, `|v| < s`, of the circle averages, `⨍_{∂B(w,ρ)} T(ψ_{s,·}) = ∫ ψ_s(v) T_ρ(w + v) dv`; hence it is bounded
  by the circle averages near `w` (`abs_mollAvgS_le_of_circleAvg`).
* `pairing_eq_setIntegral_circleAvg`: the radial identity, by the regularization
  `T φ = lim ∫ φ(y) T(ψ_{n,y}) dy` and polar coordinates (`LQGMetric.DFGPS.tendsto_integral_mul_pair_bumpTest`,
  `LQGMetric.DFGPS.integral_mul_eq_polar`), and dominated convergence with the logarithmic bound.
* `ae_abs_circleAvg_le_log`: the circle averages of a whole-plane GFF grow at most logarithmically, uniformly on
  bounded sets of centres (Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380, Lemma 2.2, `LQGMetric.DFGPS.lem2_2`).
* `pairFun_sub_eq_intervalIntegral`: the radial identity for a field `T − u` on a disc, `u` continuous, in the form
  of `IsCircleProcess`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped Real

namespace MatedCRT

namespace LQGMeasureChart

open LQGMetric MatedCRTHarmonic.LQGCoord MatedCRT.ConeAreaCovariance

/-! ## Discs, circle averages of continuous functions, test functions -/

/-- A closed disc `B̄(z, s)` lies in the open disc `B(c, r)` iff `|z − c| + s < r`. -/
theorem closedBall_subset_ball_iff_dist_add_lt {z c : ℂ} {s r : ℝ} (hs : 0 ≤ s) :
    closedBall z s ⊆ ball c r ↔ dist z c + s < r := by
  constructor
  · intro h
    by_cases hzc : z = c
    · subst hzc
      have hmem : z + (s : ℂ) ∈ closedBall z s := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hs]
      have h1 := h hmem
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hs] at h1
      rw [dist_self, zero_add]
      exact h1
    · have hd : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hzc)
      have hq : 0 ≤ s / ‖z - c‖ := div_nonneg hs hd.le
      have hxz : z + ((s / ‖z - c‖ : ℝ) : ℂ) * (z - c) - z = ((s / ‖z - c‖ : ℝ) : ℂ) * (z - c) := by
        ring
      have hxc : z + ((s / ‖z - c‖ : ℝ) : ℂ) * (z - c) - c =
          ((1 + s / ‖z - c‖ : ℝ) : ℂ) * (z - c) := by
        push_cast
        ring
      have hmem : z + ((s / ‖z - c‖ : ℝ) : ℂ) * (z - c) ∈ closedBall z s := by
        rw [mem_closedBall, dist_eq_norm, hxz, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hq, div_mul_cancel₀ s hd.ne']
      have h1 := h hmem
      rw [mem_ball, dist_eq_norm, hxc, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith), add_mul, one_mul, div_mul_cancel₀ s hd.ne'] at h1
      rw [dist_eq_norm]
      exact h1
  · intro h x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    linarith [dist_triangle x z c]

/-- The circle averages `(s, z) ↦ ⨍_{∂B(z, s)} u` of a function continuous on `U` are jointly continuous on the
closed discs contained in `U`. -/
theorem continuousOn_circleAverage_of_continuousOn {u : ℂ → ℝ} {U : Set ℂ} (hu : ContinuousOn u U) :
    ContinuousOn (fun p : ℝ × ℂ => Real.circleAverage u p.2 p.1)
      {p : ℝ × ℂ | 0 ≤ p.1 ∧ closedBall p.2 p.1 ⊆ U} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hu' : Continuous (U.domRestrict u) := continuousOn_iff_continuous_domRestrict.1 hu
  have hmem : ∀ (p : {p : ℝ × ℂ | 0 ≤ p.1 ∧ closedBall p.2 p.1 ⊆ U}) (θ : ℝ),
      circleMap p.1.2 p.1.1 θ ∈ U := fun p θ => p.2.2 (by
    rw [mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg p.2.1])
  have hcm : Continuous fun q : {p : ℝ × ℂ | 0 ≤ p.1 ∧ closedBall p.2 p.1 ⊆ U} × ℝ =>
      circleMap q.1.1.2 q.1.1.1 q.2 := by
    simp only [circleMap]
    fun_prop
  have hc : Continuous fun q : {p : ℝ × ℂ | 0 ≤ p.1 ∧ closedBall p.2 p.1 ⊆ U} × ℝ =>
      u (circleMap q.1.1.2 q.1.1.1 q.2) :=
    hu'.comp (f := fun q : {p : ℝ × ℂ | 0 ≤ p.1 ∧ closedBall p.2 p.1 ⊆ U} × ℝ =>
      (⟨circleMap q.1.1.2 q.1.1.1 q.2, hmem q.1 q.2⟩ : U)) (hcm.subtype_mk _)
  have h := (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun (p : {p : ℝ × ℂ | 0 ≤ p.1 ∧ closedBall p.2 p.1 ⊆ U}) (θ : ℝ) =>
      u (circleMap p.1.2 p.1.1 θ)) hc 0 (2 * π)).const_smul (2 * π)⁻¹
  refine h.congr fun p => ?_
  simp only [Set.domRestrict_apply, Real.circleAverage_def, Pi.smul_apply]

/-- Almost sure agreement of two almost surely continuous random functions on an open set of `ℝ × ℂ`, from almost
sure agreement at each point (on a countable dense set). -/
theorem ae_eqOn_of_continuousOn {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F G : Ω → ℝ × ℂ → ℝ}
    {S : Set (ℝ × ℂ)} (hS : IsOpen S) (hF : ∀ᵐ ω ∂P, ContinuousOn (F ω) S)
    (hG : ∀ᵐ ω ∂P, ContinuousOn (G ω) S) (hpt : ∀ p ∈ S, ∀ᵐ ω ∂P, F ω p = G ω p) :
    ∀ᵐ ω ∂P, EqOn (F ω) (G ω) S := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (ℝ × ℂ)
  have hcount : Countable ↥(S ∩ D) := (hDc.mono inter_subset_right).to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ q : ↥(S ∩ D), F ω q.1 = G ω q.1 := ae_all_iff.2 fun q => hpt q.1 q.2.1
  filter_upwards [hall, hF, hG] with ω hω hFω hGω
  have hEq : EqOn (F ω) (G ω) (S ∩ D) := fun p hp => hω ⟨p, hp⟩
  exact hEq.of_subset_closure hFω hGω inter_subset_left (hDd.open_subset_closure_inter hS)

/-- The product of a function continuous on `V` with a test function on `V` is integrable. -/
theorem integrable_mul_testOn_of_continuousOn {V : TopologicalSpace.Opens ℂ} {g : ℂ → ℝ}
    (hg : ContinuousOn g V) (φ : TestOn V) : Integrable fun x => g x * φ x := by
  have hK : IsCompact (tsupport (φ : ℂ → ℝ)) := φ.hasCompactSupport
  have hKV : tsupport (φ : ℂ → ℝ) ⊆ V := φ.tsupport_subset
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport (φ : ℂ → ℝ)) ?_ fun x hx => ?_
  · exact ((hg.mono hKV).mul φ.continuous.continuousOn).integrableOn_compact hK
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- The restriction of a distribution to `V`, evaluated at a test function on `V`, is the distribution evaluated at
any test function on `ℂ` with the same values. -/
theorem restrictTo_apply_eq_of_coe {V : TopologicalSpace.Opens ℂ} (T : DistC) (φ : TestOn V) (ψ : TestC)
    (h : ∀ x, ψ x = φ x) : restrictTo V T φ = T ψ := by
  show T (TestFunction.monoCLM ℝ φ) = T ψ
  congr 1
  ext x
  rw [TestFunction.monoCLM_apply, ite_eq_left ⟨le_rfl, le_top⟩, h]

/-- The support of `w ↦ v(z − w)` lies in `B(z, ε)` when the support of `v` lies in `B(0, ε)`. -/
theorem tsupport_sub_subset {v : ℂ → ℝ} {z : ℂ} {ε : ℝ} (hv : tsupport v ⊆ ball 0 ε) :
    tsupport (fun w => v (z - w)) ⊆ ball z ε := by
  have hC : IsClosed ((fun w => z - w) ⁻¹' tsupport v) :=
    (isClosed_tsupport v).preimage (by fun_prop)
  refine (closure_minimal (s := Function.support fun w => v (z - w))
    (t := (fun w => z - w) ⁻¹' tsupport v) (fun w hw => subset_tsupport v hw) hC).trans fun w hw => ?_
  have h1 := hv hw
  rw [mem_ball_zero_iff] at h1
  rw [mem_ball, dist_eq_norm, ← norm_neg, neg_sub]
  exact h1

/-! ## Mollified circle averages as averages of circle averages -/

/-- The mollified circle averages of a scale-regular distribution at a fixed radius are bounded on compact sets of
centres, uniformly in the scale `s ∈ (0, 1]`. -/
theorem exists_bound_mollAvgS {T : DistC} (hT : ScaleRegular T) {ρ : ℝ} (hρ : 0 < ρ) {K : Set ℂ}
    (hK : IsCompact K) : ∃ M : ℝ, ∀ s ∈ Ioc (0 : ℝ) 1, ∀ w ∈ K, |mollAvgS T s w ρ| ≤ M := by
  obtain ⟨F, hFc, hF⟩ := hT
  have hc : Continuous fun p : ℝ × ℂ => scalePt p.1 p.2 ρ := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_fst
    · exact Complex.continuous_re.comp continuous_snd
    · exact Complex.continuous_im.comp continuous_snd
    · exact continuous_const
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod hK).exists_bound_of_continuousOn
    (hFc.comp hc).continuousOn
  refine ⟨M, fun s hs w hw => ?_⟩
  have h1 : ‖F (scalePt s w ρ)‖ ≤ M := hM (s, w) ⟨⟨hs.1.le, hs.2⟩, hw⟩
  have hne : scalePt s w ρ 0 ≠ 0 := by
    show s ≠ 0
    exact hs.1.ne'
  rw [hF _ hne, mollProc_scalePt T hs.1 hρ w, Real.norm_eq_abs] at h1
  exact h1

/-- The dyadic scales `2^{-n}` tend to `0` from above. -/
lemma tendsto_dyadic_nhdsGT : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    (Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity))

/-- **Mollified circle averages are averages of circle averages.** For a scale-regular distribution `T`,
`⨍_{∂B(w,ρ)} T(ψ_{s,·}) = ∫ ψ_s(v) T_ρ(w + v) dv`. -/
theorem mollAvgS_eq_integral_circleAvg {T : DistC} (hT : ScaleRegular T) {s ρ : ℝ} (hs : 0 < s)
    (hρ : 0 < ρ) (w : ℂ) : mollAvgS T s w ρ = ∫ v, bumpS s 0 v * circleAvg T ρ (w + v) := by
  have h1 := LQGMetric.DFGPS.tendsto_integral_mul_pair_bumpTest T (circBumpS s w ρ)
  have h2 : ∀ n : ℕ, ∫ y, circBumpS s w ρ y * T (bumpTest n y) =
      ∫ v, bumpS s 0 v * mollAvgS T ((2 : ℝ)⁻¹ ^ n) (w + v) ρ := by
    intro n
    have hfc : Continuous fun y => T (bumpTest n y) := T.continuous.comp (continuous_bumpTest n)
    calc ∫ y, circBumpS s w ρ y * T (bumpTest n y)
        = mollAvgS (MatedCRTHarmonic.CellScaling.ofFunC fun y => T (bumpTest n y)) s w ρ := by
          rw [mollAvgS_eq, ofFunC_apply_li hfc.locallyIntegrable]
      _ = ∫ v, bumpS s 0 v * Real.circleAverage (fun y => T (bumpTest n y)) (w + v) ρ :=
          mollAvgS_ofFunC_eq hfc.measurable hfc.locallyIntegrable s w ρ
      _ = ∫ v, bumpS s 0 v * mollAvgS T ((2 : ℝ)⁻¹ ^ n) (w + v) ρ := by
          refine integral_congr_ae (Eventually.of_forall fun v => ?_)
          simp only [mollAvgS, bumpS_dyadic]
  obtain ⟨M, hM⟩ := exists_bound_mollAvgS hT hρ (isCompact_closedBall w s)
  have h3 : Tendsto (fun n : ℕ => ∫ v, bumpS s 0 v * mollAvgS T ((2 : ℝ)⁻¹ ^ n) (w + v) ρ) atTop
      (𝓝 (∫ v, bumpS s 0 v * circleAvg T ρ (w + v))) := by
    refine tendsto_integral_of_dominated_convergence (fun v => bumpS s 0 v * M) (fun n => ?_)
      (((bumpS s 0).continuous.integrable_of_hasCompactSupport (bumpS s 0).hasCompactSupport).mul_const M)
      (fun n => Eventually.of_forall fun v => ?_) (Eventually.of_forall fun v => ?_)
    · have hc : Continuous fun v : ℂ => mollAvgS T ((2 : ℝ)⁻¹ ^ n) (w + v) ρ :=
        (continuousOn_mollAvgS T).comp_continuous (f := fun v : ℂ => ((2 : ℝ)⁻¹ ^ n, w + v, ρ))
          (by fun_prop) fun v => ⟨Set.mem_Ioi.2 (by positivity), mem_univ _⟩
      exact ((bumpS s 0).continuous.mul hc).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (bumpS_nonneg s 0 v)]
      by_cases hv : dist v 0 < s
      · refine mul_le_mul_of_nonneg_left (hM _ ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩ _ ?_)
          (bumpS_nonneg s 0 v)
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
        rw [dist_zero_right] at hv
        exact hv.le
      · rw [bumpS_eq_zero s (by rw [abs_of_pos hs]; exact not_lt.mp hv), zero_mul, zero_mul]
    · exact ((tendsto_mollAvgS_circleAvg_of_scaleRegular hT hρ (w + v)).comp
        tendsto_dyadic_nhdsGT).const_mul _
  rw [mollAvgS_eq]
  exact tendsto_nhds_unique (h1.congr h2) h3

/-- A mollified circle average of a scale-regular distribution is bounded by the circle averages of the same
radius centred within the mollifier scale. -/
theorem abs_mollAvgS_le_of_circleAvg {T : DistC} (hT : ScaleRegular T) {s ρ B : ℝ} (hs : 0 < s)
    (hρ : 0 < ρ) {w : ℂ} (hB : ∀ v ∈ closedBall w s, |circleAvg T ρ v| ≤ B) :
    |mollAvgS T s w ρ| ≤ B := by
  rw [mollAvgS_eq_integral_circleAvg hT hs hρ w]
  have hc : Continuous fun v : ℂ => circleAvg T ρ (w + v) :=
    (continuousOn_circleAvg_of_scaleRegular hT).comp_continuous (f := fun v : ℂ => (ρ, w + v))
      (by fun_prop) fun v => ⟨hρ, mem_univ _⟩
  have h := abs_integral_bumpS_mul_sub_le hc hs (c₀ := 0) (η := B) fun v hv => by
    rw [sub_zero]
    refine hB _ ?_
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    rwa [mem_closedBall, dist_zero_right] at hv
  rwa [sub_zero] at h

/-! ## The radial identity -/

/-- **Pairing with a radial test function** (Sheffield–Wang (2016), p. 10). For a scale-regular distribution `T`
whose circle averages near `z` are at most `C (1 + |log ρ|)`, and a test function `φ` radial about `z` vanishing
outside `B(z, ε)`, the function `r ↦ 2π r φ(z + r) T_r(z)` is integrable on `(0, ∞)` and
`T φ = ∫_0^∞ 2π r φ(z + r) T_r(z) dr`. -/
theorem pairing_eq_setIntegral_circleAvg {T : DistC} (hT : ScaleRegular T) {z : ℂ} {ε C : ℝ}
    (hb : ∀ ρ : ℝ, 0 < ρ → ∀ w ∈ closedBall z 1, |circleAvg T ρ w| ≤ C * (1 + |Real.log ρ|))
    (φ : TestC) (hrad : ∀ w : ℂ, φ w = φ (z + ((‖w - z‖ : ℝ) : ℂ)))
    (hsupp : ∀ r : ℝ, ε ≤ r → φ (z + (r : ℂ)) = 0) :
    IntegrableOn (fun r : ℝ => 2 * π * r * φ (z + (r : ℂ)) * circleAvg T r z) (Ioi 0) ∧
      T φ = ∫ r in Ioi (0 : ℝ), 2 * π * r * φ (z + (r : ℂ)) * circleAvg T r z := by
  -- the dominating function
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ,
      g = fun r : ℝ => 2 * π * |φ (z + (r : ℂ))| * |C| * (|r| + |r * Real.log r|) := ⟨_, rfl⟩
  have hφ0 : ∀ r : ℝ, ε ≤ |r| → φ (z + (r : ℂ)) = 0 := by
    intro r hr
    rw [hrad, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    exact hsupp _ hr
  have hgc : Continuous g := by
    have h1 : Continuous fun r : ℝ => φ (z + (r : ℂ)) := φ.continuous.comp (by fun_prop)
    have h2 : Continuous fun r : ℝ => r * Real.log r := Real.continuous_mul_log
    rw [hg]
    exact ((continuous_const.mul h1.abs).mul continuous_const).mul (continuous_abs.add h2.abs)
  have hgs : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -|ε|) (b := |ε|)) fun r hr => ?_
    have hr' : ε ≤ |r| := not_lt.1 fun hlt =>
      hr ⟨by linarith [neg_abs_le r, le_abs_self ε], by linarith [le_abs_self r, le_abs_self ε]⟩
    rw [hg]
    simp only [hφ0 r hr', abs_zero, mul_zero, zero_mul]
  have hgi : IntegrableOn g (Ioi 0) := (hgc.integrable_of_hasCompactSupport hgs).integrableOn
  have hpos : ∀ r : ℝ, 0 < r → ∀ a : ℝ, |a| ≤ C * (1 + |Real.log r|) →
      ‖2 * π * r * φ (z + (r : ℂ)) * a‖ ≤ g r := by
    intro r hr a ha
    have hC : C * (1 + |Real.log r|) ≤ |C| * (1 + |Real.log r|) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have hga : g r = 2 * π * |φ (z + (r : ℂ))| * |C| * (r + r * |Real.log r|) := by
      rw [hg]
      simp only [abs_mul, abs_of_pos hr]
    rw [hga, Real.norm_eq_abs]
    simp only [abs_mul, abs_two, abs_of_pos Real.pi_pos, abs_of_pos hr]
    have h0 : 0 ≤ 2 * π * r * |φ (z + (r : ℂ))| :=
      mul_nonneg (mul_nonneg (by positivity) hr.le) (abs_nonneg _)
    calc 2 * π * r * |φ (z + (r : ℂ))| * |a|
        ≤ 2 * π * r * |φ (z + (r : ℂ))| * (|C| * (1 + |Real.log r|)) :=
          mul_le_mul_of_nonneg_left (ha.trans hC) h0
      _ = 2 * π * |φ (z + (r : ℂ))| * |C| * (r + r * |Real.log r|) := by ring
  -- the regularized pairings in polar coordinates
  have h1 := LQGMetric.DFGPS.tendsto_integral_mul_pair_bumpTest T φ
  have h2 : ∀ n : ℕ, ∫ y, φ y * T (bumpTest n y) =
      ∫ r in Ioi (0 : ℝ), 2 * π * r * φ (z + (r : ℂ)) * mollAvgS T ((2 : ℝ)⁻¹ ^ n) z r := by
    intro n
    rw [LQGMetric.DFGPS.integral_mul_eq_polar (m := fun x => T (bumpTest n x))
      (T.continuous.comp (continuous_bumpTest n)) φ z hrad]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [mollAvgS, bumpS_dyadic]
  have hs : ∀ n : ℕ, 0 < (2 : ℝ)⁻¹ ^ n := fun n => by positivity
  have hs1 : ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n ≤ 1 := fun n => pow_le_one₀ (by norm_num) (by norm_num)
  have h3 : Tendsto (fun n : ℕ =>
      ∫ r in Ioi (0 : ℝ), 2 * π * r * φ (z + (r : ℂ)) * mollAvgS T ((2 : ℝ)⁻¹ ^ n) z r) atTop
      (𝓝 (∫ r in Ioi (0 : ℝ), 2 * π * r * φ (z + (r : ℂ)) * circleAvg T r z)) := by
    refine tendsto_integral_of_dominated_convergence g (fun n => ?_) hgi (fun n => ?_) ?_
    · have hc : Continuous fun r : ℝ => mollAvgS T ((2 : ℝ)⁻¹ ^ n) z r :=
        (continuousOn_mollAvgS T).comp_continuous (f := fun r : ℝ => ((2 : ℝ)⁻¹ ^ n, z, r))
          (by fun_prop) fun r => ⟨hs n, mem_univ _⟩
      have hφc : Continuous fun r : ℝ => φ (z + (r : ℂ)) := φ.continuous.comp (by fun_prop)
      exact (((continuous_const.mul continuous_id).mul hφc).mul hc).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun r hr => hpos r hr _ ?_
      refine abs_mollAvgS_le_of_circleAvg hT (hs n) hr fun v hv => hb r hr v ?_
      exact closedBall_subset_closedBall (hs1 n) hv
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun r hr => ?_
      exact ((tendsto_mollAvgS_circleAvg_of_scaleRegular hT hr z).comp tendsto_dyadic_nhdsGT).const_mul _
  refine ⟨?_, tendsto_nhds_unique (h1.congr h2) h3⟩
  -- integrability of the limit
  refine Integrable.mono' hgi ?_ ?_
  · have hc : ContinuousOn (fun r : ℝ => circleAvg T r z) (Ioi 0) :=
      (continuousOn_circleAvg_of_scaleRegular hT).comp (f := fun r : ℝ => ((r, z) : ℝ × ℂ))
        (by fun_prop : Continuous fun r : ℝ => ((r, z) : ℝ × ℂ)).continuousOn
        fun r hr => (⟨hr, mem_univ z⟩ : ((r, z) : ℝ × ℂ) ∈ Ioi 0 ×ˢ univ)
    have hφc : Continuous fun r : ℝ => φ (z + (r : ℂ)) := φ.continuous.comp (by fun_prop)
    exact ((((continuous_const.mul continuous_id).mul hφc).continuousOn).mul hc).aestronglyMeasurable
      measurableSet_Ioi
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun r hr => hpos r hr _ (hb r hr z (mem_closedBall_self zero_le_one))

/-- Radial integrals over `(0, ∞)` of a test function `f` with `f(z + r) = v(r)`, `v` vanishing for `r ≥ ε`, as
interval integrals over `(0, ε)`. -/
theorem setIntegral_Ioi_sub_eq_intervalIntegral {f v : ℂ → ℝ} {z : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ r : ℝ, f (z + (r : ℂ)) = v r) (hv0 : ∀ r : ℝ, ε ≤ r → v r = 0) (G₁ G₂ : ℝ → ℝ) :
    ∫ r in Ioi (0 : ℝ), (2 * π * r * f (z + (r : ℂ)) * G₁ r - 2 * π * r * f (z + (r : ℂ)) * G₂ r) =
      2 * π * ∫ s in (0 : ℝ)..ε, (G₁ s - G₂ s) * v s * s := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    (fun r hr => ?_), intervalIntegral.integral_of_le hε.le, ← integral_const_mul]
  · refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
    simp only [hf]
    ring
  · have hr' : ε < r := by
      by_contra h
      exact hr.2 ⟨hr.1, not_lt.1 h⟩
    simp only [hf, hv0 r hr'.le, mul_zero, zero_mul, sub_self]

/-- **The radial identity on a disc.** Let `T` be a scale-regular distribution whose circle averages grow at most
logarithmically on bounded sets, and let `T = Xz + u` on the disc `B(c, r)`, with `u` continuous. For every closed
disc `B̄(z, ε) ⊆ B(c, r)` and every smooth radial `v` supported in `B(0, ε)`,
`Xz(v(z − ·)) = 2π ∫_0^ε (T_s(z) − ⨍_{∂B(z,s)} u) v(s) s ds`. -/
theorem pairFun_sub_eq_intervalIntegral {c : ℂ} {r : ℝ} {T : DistC} {Xz : DistOn (disc c r)}
    {u : ℂ → ℝ} (hT : ScaleRegular T)
    (hlog : ∀ R : ℕ, ∃ C : ℝ, ∀ ρ : ℝ, 0 < ρ → ∀ w ∈ ball (0 : ℂ) R,
      |circleAvg T ρ w| ≤ C * (1 + |Real.log ρ|))
    (hu : ContinuousOn u (ball c r))
    (hd : ∀ φ : TestOn (disc c r), restrictTo (disc c r) T φ = Xz φ + ∫ x, u x * φ x)
    {z : ℂ} {ε : ℝ} (hε : 0 < ε) (hzε : closedBall z ε ⊆ ball c r) {v : ℂ → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvrad : ∀ w w' : ℂ, ‖w‖ = ‖w'‖ → v w = v w')
    (hvs : tsupport v ⊆ ball 0 ε) :
    pairFun Xz (fun w => v (z - w)) =
      2 * π * ∫ s in (0 : ℝ)..ε, (circleAvg T s z - Real.circleAverage u z s) * v s * s := by
  -- the test function `v(z − ·)`
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun w => v (z - w)) := hv.comp (contDiff_const.sub contDiff_id)
  have hts : tsupport (fun w => v (z - w)) ⊆ ball z ε := tsupport_sub_subset hvs
  have hcs : HasCompactSupport (fun w => v (z - w)) :=
    (isCompact_closedBall z ε).of_isClosed_subset (isClosed_tsupport _) (hts.trans ball_subset_closedBall)
  have htV : tsupport (fun w => v (z - w)) ⊆ (disc c r : Set ℂ) :=
    hts.trans (ball_subset_closedBall.trans hzε)
  let φV : TestOn (disc c r) := ⟨fun w => v (z - w), hcd, hcs, htV⟩
  let φC : TestC := ⟨fun w => v (z - w), hcd, hcs, subset_univ _⟩
  have hpair : pairFun Xz (fun w => v (z - w)) = Xz φV := dite_eq_left ⟨hcd, hcs, htV⟩
  have hRφ : restrictTo (disc c r) T φV = T φC := restrictTo_apply_eq_of_coe T φV φC fun _ => rfl
  -- its radial structure
  have hrad : ∀ w : ℂ, φC w = φC (z + ((‖w - z‖ : ℝ) : ℂ)) := by
    intro w
    show v (z - w) = v (z - (z + ((‖w - z‖ : ℝ) : ℂ)))
    apply hvrad
    rw [sub_add_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_norm, norm_sub_rev]
  have hφr : ∀ s : ℝ, φC (z + (s : ℂ)) = v s := by
    intro s
    show v (z - (z + (s : ℂ))) = v s
    apply hvrad
    rw [sub_add_cancel_left, norm_neg]
  have hv0 : ∀ s : ℝ, ε ≤ s → v s = 0 := by
    intro s hs
    refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have h1 := hvs h
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] at h1
    linarith [le_abs_self s]
  have hsupp : ∀ s : ℝ, ε ≤ s → φC (z + (s : ℂ)) = 0 := fun s hs => by rw [hφr]; exact hv0 s hs
  -- the logarithmic bound near `z`
  obtain ⟨C, hC⟩ := hlog (⌈‖z‖⌉₊ + 2)
  have hb : ∀ ρ : ℝ, 0 < ρ → ∀ w ∈ closedBall z 1, |circleAvg T ρ w| ≤ C * (1 + |Real.log ρ|) := by
    intro ρ hρ w hw
    refine hC ρ hρ w ?_
    rw [mem_ball_zero_iff]
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 := norm_sub_norm_le w z
    have h2 := Nat.le_ceil ‖z‖
    push_cast
    linarith
  obtain ⟨hi1, hT1⟩ := pairing_eq_setIntegral_circleAvg hT hb φC hrad hsupp
  -- the continuous part, in polar coordinates
  have hmc : Continuous fun x => u (LQGMetric.MarkovWeyl2.projB z ε x) :=
    hu.comp_continuous (LQGMetric.MarkovWeyl2.continuous_projB z ε) fun x => hzε (by
      rw [mem_closedBall, dist_eq_norm]
      exact LQGMetric.MarkovWeyl2.norm_projB_sub_le hε z x)
  have hum : ∫ x, u x * φV x = ∫ y, φC y * u (LQGMetric.MarkovWeyl2.projB z ε y) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show u x * v (z - x) = v (z - x) * u (LQGMetric.MarkovWeyl2.projB z ε x)
    by_cases hx : v (z - x) = 0
    · rw [hx, mul_zero, zero_mul]
    · have hxs : x ∈ ball z ε := hts (subset_tsupport _ hx)
      rw [LQGMetric.MarkovWeyl2.projB_eq hε (by rw [mem_ball, dist_eq_norm] at hxs; exact hxs.le),
        mul_comm]
  have hpol : ∫ y, φC y * u (LQGMetric.MarkovWeyl2.projB z ε y) = ∫ s in Ioi (0 : ℝ),
      2 * π * s * φC (z + (s : ℂ)) * Real.circleAverage (fun x => u (LQGMetric.MarkovWeyl2.projB z ε x)) z s :=
    LQGMetric.DFGPS.integral_mul_eq_polar hmc φC z hrad
  have hi2 : IntegrableOn (fun s : ℝ => 2 * π * s * φC (z + (s : ℂ)) *
      Real.circleAverage (fun x => u (LQGMetric.MarkovWeyl2.projB z ε x)) z s) (Ioi 0) := by
    have hca : Continuous (Real.circleAverage (fun x => u (LQGMetric.MarkovWeyl2.projB z ε x)) z) :=
      Real.Continuous.circleAverage hmc
    have hφc : Continuous fun s : ℝ => φC (z + (s : ℂ)) := φC.continuous.comp (by fun_prop)
    have hc : Continuous fun s : ℝ => 2 * π * s * φC (z + (s : ℂ)) *
        Real.circleAverage (fun x => u (LQGMetric.MarkovWeyl2.projB z ε x)) z s :=
      ((continuous_const.mul continuous_id).mul hφc).mul hca
    refine (hc.integrable_of_hasCompactSupport ?_).integrableOn
    refine HasCompactSupport.intro (isCompact_Icc (a := -ε) (b := ε)) fun s hs => ?_
    have hs' : ε ≤ |s| := not_lt.1 fun hlt =>
      hs ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
    have h0 : φC (z + (s : ℂ)) = 0 := by
      rw [hrad, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
      exact hsupp _ hs'
    simp only [h0, mul_zero, zero_mul]
  -- assembling
  have hd' := hd φV
  rw [hRφ] at hd'
  have hX : Xz φV = T φC - ∫ x, u x * φV x := by linarith
  have key : T φC - ∫ x, u x * φV x = 2 * π * ∫ s in (0 : ℝ)..ε,
      (circleAvg T s z - Real.circleAverage (fun x => u (LQGMetric.MarkovWeyl2.projB z ε x)) z s) * v s * s := by
    rw [hT1, hum, hpol, ← integral_sub hi1 hi2]
    exact setIntegral_Ioi_sub_eq_intervalIntegral hε hφr hv0 (fun s => circleAvg T s z)
      (fun s => Real.circleAverage (fun x => u (LQGMetric.MarkovWeyl2.projB z ε x)) z s)
  rw [hpair, hX, key]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le hε.le] at hs
  have hca : Real.circleAverage (fun x => u (LQGMetric.MarkovWeyl2.projB z ε x)) z s =
      Real.circleAverage u z s := by
    refine Real.circleAverage_congr_sphere fun x hx => ?_
    rw [mem_sphere, dist_eq_norm, abs_of_nonneg hs.1] at hx
    show u (LQGMetric.MarkovWeyl2.projB z ε x) = u x
    rw [LQGMetric.MarkovWeyl2.projB_eq hε (by rw [hx]; exact hs.2)]
  simp only [hca]

/-! ## The logarithmic growth of the circle averages of the whole-plane GFF -/

/-- **The circle averages of a whole-plane GFF grow at most logarithmically** (Dubédat–Falconet–Gwynne–Pfeffer–Sun,
arXiv:1905.00380, Lemma 2.2, with a deterministic constant): almost surely, for every `R`, there is `C` with
`|h_ρ(w)| ≤ C (1 + |log ρ|)` for all `ρ > 0` and `|w| < R`. -/
theorem ae_abs_circleAvg_le_log {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → DistC} (hX : LQGMetric.IsWholePlaneGFF X P) :
    ∀ᵐ ω ∂P, ∀ R : ℕ, ∃ C : ℝ, ∀ ρ : ℝ, 0 < ρ → ∀ w ∈ ball (0 : ℂ) R,
      |circleAvg (X ω) ρ w| ≤ C * (1 + |Real.log ρ|) := by
  obtain ⟨H, hH⟩ := LQGMetric.DFGPS.exists_isCircleAvgVersion hX
  have hagree : ∀ᵐ ω ∂P, EqOn (fun p : ℝ × ℂ => H p.1 p.2 ω)
      (fun p : ℝ × ℂ => circleAvg (X ω) p.1 p.2) (Ioi 0 ×ˢ univ) := by
    refine ae_eqOn_of_continuousOn (isOpen_Ioi.prod isOpen_univ)
      (Eventually.of_forall fun ω => hH.cont ω) ?_ fun p hp => hH.ae_eq p.1 hp.1 p.2
    filter_upwards [ae_scaleRegular_wp hX] with ω hω
    exact continuousOn_circleAvg_of_scaleRegular hω
  have hbd : ∀ᵐ ω ∂P, ∀ R : ℕ, ∃ C : ℝ, ∀ ρ : ℝ, 0 < ρ → ∀ w ∈ ball (0 : ℂ) R,
      |H ρ w ω| ≤ C * (1 + |Real.log ρ|) := by
    rw [ae_all_iff]
    intro R
    obtain ⟨A, hA, hAζ⟩ := LQGMetric.DFGPS.lem2_2 hX hH (R : ℝ)
    filter_upwards [hAζ (1 / 2) (by norm_num)] with ω hω
    obtain ⟨C, hC⟩ := hω
    refine ⟨|C| * (A + 1), fun ρ hρ w hw => ?_⟩
    have h1 := hC ρ hρ w hw
    rw [show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one, one_div, Real.log_inv] at h1
    have hl1 := neg_le_abs (Real.log ρ)
    have hl2 := le_abs_self (Real.log ρ)
    have hl0 := abs_nonneg (Real.log ρ)
    have hm1 : 1 ≤ max (max (A * -Real.log ρ) (Real.log ρ)) 1 := le_max_right _ _
    have hm : max (max (A * -Real.log ρ) (Real.log ρ)) 1 ≤ (A + 1) * (1 + |Real.log ρ|) := by
      refine max_le (max_le ?_ ?_) ?_ <;>
        nlinarith [mul_nonneg hA.le (show (0 : ℝ) ≤ |Real.log ρ| + Real.log ρ by linarith),
          mul_nonneg hA.le (show (0 : ℝ) ≤ 1 + |Real.log ρ| by linarith)]
    calc |H ρ w ω| ≤ C * max (max (A * -Real.log ρ) (Real.log ρ)) 1 := h1
      _ ≤ |C| * max (max (A * -Real.log ρ) (Real.log ρ)) 1 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (zero_le_one.trans hm1)
      _ ≤ |C| * ((A + 1) * (1 + |Real.log ρ|)) := mul_le_mul_of_nonneg_left hm (abs_nonneg C)
      _ = |C| * (A + 1) * (1 + |Real.log ρ|) := by ring
  filter_upwards [hagree, hbd] with ω h1 h2 R
  obtain ⟨C, hC⟩ := h2 R
  refine ⟨C, fun ρ hρ w hw => ?_⟩
  have e : H ρ w ω = circleAvg (X ω) ρ w :=
    h1 (show ((ρ, w) : ℝ × ℂ) ∈ Ioi 0 ×ˢ univ from ⟨hρ, mem_univ w⟩)
  rw [← e]
  exact hC ρ hρ w hw

end LQGMeasureChart

end MatedCRT
