import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraKernelLayer
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraBarrierStrip
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraBarrierCanonical
import MatedCRT.FirstPass.Derived.BrownianTubeChain

/-!
# The killed interval kernel near the lower barrier, for planar Brownian motion

For planar Brownian motion `planarBrownianMotion 0`, the real part stays in `(-e, H)` up to time `T` and ends in
`(y₁, y₂)`, `0 < y₁ < y₂ < H`, with probability at least `c e` for `0 < e ≤ 1` (`exists_le_planarBrownianMotion_killedStrip`;
Karatzas–Shreve, *Brownian Motion and Stochastic
Calculus*, §2.8.C). Two stages, joined by the Markov property at the deterministic time `t₁ = T/2`
(`le_planarBrownian_inter_shift_preimage`):

* up to `t₁` the path stays in the box `(-e, L - e) × (-L/2, L/2)` and ends with real part in `(5L/16, 7L/16)`, with
  probability at least `exp(-π² t₁/(2L²))² / (8L) · e` (`le_measure_layer`, for the canonical planar Brownian motion,
  `isPlanarBM_canonical`), where `L = min H √t₁` makes the first Dirichlet mode dominate;
* from any point with real part in `[5L/16, 7L/16]` the real part stays in `(0, H)` for the remaining time `T - t₁`
  and ends in `(y₁, y₂)` with probability at least a constant `p > 0` (`exists_pos_le_planarBrownianMotion_reStrip`).

For `e > L/16` the event only grows with `e`.

* `killedStrip e H y₁ y₂ T`: the event of the statement for the real part.
* `layerEvent e L t`: the first stage; `measurableSet_layerEvent`: it is adapted at time `t`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls

namespace MatedCRT.PeanosphereTriplePoints

/-- The real part stays in `(-e, H)` up to time `T` and ends in `(y₁, y₂)`. -/
def killedStrip (e H y₁ y₂ : ℝ) (T : ℝ≥0) : Set (ContinuousPath ℂ) :=
  {ω | (∀ s ≤ T, -e < (ω s).re ∧ (ω s).re < H) ∧ (ω T).re ∈ Ioo y₁ y₂}

theorem killedStrip_mono {e e' H y₁ y₂ : ℝ} {T : ℝ≥0} (h : e ≤ e') :
    killedStrip e H y₁ y₂ T ⊆ killedStrip e' H y₁ y₂ T := by
  rintro ω ⟨h1, h2⟩
  exact ⟨fun s hs => ⟨by linarith [(h1 s hs).1], (h1 s hs).2⟩, h2⟩

/-- The box `(-e, L - e) × (-L/2, L/2)` as a sublevel set: `z` lies in it iff `layerF e L z < 0`. -/
noncomputable def layerF (e L : ℝ) (z : ℂ) : ℝ :=
  max (max (-z.re - e) (z.re - (L - e))) (max (z.im - L / 2) (-z.im - L / 2))

theorem continuous_layerF (e L : ℝ) : Continuous (layerF e L) := by
  unfold layerF
  fun_prop

/-- The first stage: the path stays in the box `(-e, L - e) × (-L/2, L/2)` up to time `t` and ends with real part in
`(5L/16, 7L/16)`. -/
def layerEvent (e L : ℝ) (t : ℝ≥0) : Set (ContinuousPath ℂ) :=
  {ω | ∀ s ≤ t, layerF e L (ω s) < 0} ∩ {ω | (ω t).re ∈ Ioo (5 * L / 16) (7 * L / 16)}

theorem measurableSet_layerEvent (e L : ℝ) (t : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] (layerEvent e L t) := by
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_forall_le_lt_canonicalFiltration t (fun s ω => layerF e L (ω s))
      (fun s hs => (continuous_layerF e L).measurable.comp (measurable_eval_canonicalFiltration hs))
      (fun ω => (continuous_layerF e L).comp ω.continuous) 0
  · exact (Complex.continuous_re.measurable.comp (measurable_eval_canonicalFiltration le_rfl))
      measurableSet_Ioo

/-- The real part stays in `(0, H)` up to time `T` and ends in `(y₁, y₂)` (the event of the second stage). -/
def reStrip (H y₁ y₂ : ℝ) (T : ℝ≥0) : Set (ContinuousPath ℂ) :=
  {ω | (∀ s ≤ T, 0 < (ω s).re ∧ (ω s).re < H) ∧ (ω T).re ∈ Ioo y₁ y₂}

theorem measurableSet_reStrip (H y₁ y₂ : ℝ) (T : ℝ≥0) : MeasurableSet (reStrip H y₁ y₂ T) := by
  have hF : Continuous fun z : ℂ => max (-z.re) (z.re - H) := by fun_prop
  have hset : reStrip H y₁ y₂ T =
      {ω : ContinuousPath ℂ | ∀ s ≤ T, max (-(ω s).re) ((ω s).re - H) < 0} ∩
        {ω | (ω T).re ∈ Ioo y₁ y₂} := by
    ext ω
    simp only [reStrip, mem_ofPred_eq, mem_inter_iff, max_lt_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun s hs => ⟨by linarith [(h1 s hs).1], by linarith [(h1 s hs).2]⟩, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun s hs => ⟨by linarith [(h1 s hs).1], by linarith [(h1 s hs).2]⟩, h2⟩
  rw [hset]
  refine ((ContinuousPath.canonicalFiltration (alpha := ℂ)).le T) _ (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_forall_le_lt_canonicalFiltration T (fun s ω => max (-(ω s).re) ((ω s).re - H))
      (fun s hs => hF.measurable.comp (measurable_eval_canonicalFiltration hs))
      (fun ω => hF.comp ω.continuous) 0
  · exact (Complex.continuous_re.measurable.comp (measurable_eval_canonicalFiltration le_rfl))
      measurableSet_Ioo

/-- `exp (-2) ≤ 1/4`. -/
theorem exp_neg_two_le_quarter : Real.exp (-2) ≤ 1 / 4 := by
  have h := Real.quadratic_le_exp_of_nonneg (x := 2) (by norm_num)
  rw [Real.exp_neg]
  rw [inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
  linarith

/-- **The killed interval kernel near the lower barrier, for planar Brownian motion.** For `0 < y₁ < y₂ < H` and
`T > 0` there is `c > 0` such that for `0 < e ≤ 1` the real part of planar Brownian motion started at `0` stays in
`(-e, H)` up to time `T` and ends in `(y₁, y₂)` with probability at least `c e`. -/
theorem exists_le_planarBrownianMotion_killedStrip {T : ℝ≥0} (hT : 0 < T) {H y₁ y₂ : ℝ}
    (hy₁ : 0 < y₁) (hy₁₂ : y₁ < y₂) (hy₂ : y₂ < H) :
    ∃ c : ℝ, 0 < c ∧ ∀ e : ℝ, 0 < e → e ≤ 1 →
      ENNReal.ofReal (c * e) ≤ planarBrownianMotion 0 (killedStrip e H y₁ y₂ T) := by
  set t₁ : ℝ≥0 := T / 2 with ht₁def
  have ht₁0 : 0 < t₁ := by rw [ht₁def]; positivity
  have ht₁T : t₁ ≤ T := by rw [ht₁def]; exact div_le_self (by positivity) one_le_two
  set T' : ℝ≥0 := T - t₁ with hT'def
  have hT'0 : 0 < T' := by
    rw [hT'def, ht₁def]
    exact tsub_pos_of_lt (half_lt_self hT)
  have htT : t₁ + T' = T := add_tsub_cancel_of_le ht₁T
  have hH : 0 < H := by linarith
  have ht₁r : (0 : ℝ) < t₁ := by exact_mod_cast ht₁0
  set L : ℝ := min H (Real.sqrt t₁) with hLdef
  have hL0 : 0 < L := lt_min hH (Real.sqrt_pos.2 ht₁r)
  have hLH : L ≤ H := min_le_left _ _
  have hLt : L ^ 2 ≤ t₁ := by
    have h1 : L ≤ Real.sqrt t₁ := min_le_right _ _
    calc L ^ 2 ≤ Real.sqrt t₁ ^ 2 := pow_le_pow_left₀ hL0.le h1 2
      _ = t₁ := Real.sq_sqrt (NNReal.coe_nonneg _)
  set r := Real.exp (-(Real.pi ^ 2 / (2 * L ^ 2)) * t₁) with hrdef
  have hr : r ≤ 1 / 4 := by
    refine le_trans (Real.exp_le_exp.2 ?_) exp_neg_two_le_quarter
    have hpi : 4 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hL2 : 0 < L ^ 2 := by positivity
    have h2 : 2 ≤ Real.pi ^ 2 / (2 * L ^ 2) * t₁ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hr0 : 0 < r := Real.exp_pos _
  -- the second stage
  obtain ⟨p, hp0, hp⟩ := exists_pos_le_planarBrownianMotion_reStrip (H := H) (α := 5 * L / 16)
    (β := 7 * L / 16) (y₁ := y₁) (y₂ := y₂) (by positivity) (by linarith) (by linarith) hy₁ hy₁₂ hy₂ hT'0
  have hpTop : p ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_ne_top (planarBrownianMotion ((5 * L / 16 : ℝ) : ℂ)) _)
      (hp ((5 * L / 16 : ℝ) : ℂ) ?_)
    simp only [Complex.ofReal_re, mem_Icc]
    constructor <;> linarith
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0.ne' hpTop
  set κ : ℝ := r ^ 2 / (8 * L) with hκdef
  have hκ : 0 < κ := by positivity
  -- the bound for `e ≤ L/16`
  have key : ∀ e : ℝ, 0 < e → e ≤ L / 16 →
      p * ENNReal.ofReal (κ * e) ≤ planarBrownianMotion 0 (killedStrip e H y₁ y₂ T) := by
    intro e he0 heL
    have hA : ENNReal.ofReal (κ * e) ≤ planarBrownianMotion 0 (layerEvent e L t₁) := by
      refine (le_measure_layer isPlanarBM_canonical hL0 ht₁0 hr he0 heL).trans (measure_mono ?_)
      rintro ω ⟨hwin, hsq⟩
      obtain ⟨h1, h2, -, -⟩ := mem_of_mem_layerWindow hwin
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] at h1 h2
      refine ⟨fun s hs => ?_, ⟨by linarith, by linarith⟩⟩
      have hs' := hsq s hs
      simp only [LQGMetric.HeatSq.sqOpen, mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
        sub_zero, add_zero, mul_one, zero_add] at hs'
      obtain ⟨a1, a2, a3, a4⟩ := hs'
      simp only [layerF, max_lt_iff]
      refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    have hM := le_planarBrownian_inter_shift_preimage 0 t₁ (measurableSet_layerEvent e L t₁)
      (measurableSet_reStrip H y₁ y₂ T') (p := p) (fun ω hω => hp (ω t₁) (by
        obtain ⟨-, h⟩ := hω
        exact ⟨h.1.le, h.2.le⟩))
    calc p * ENNReal.ofReal (κ * e) ≤ p * planarBrownianMotion 0 (layerEvent e L t₁) := by gcongr
      _ ≤ planarBrownianMotion 0 (layerEvent e L t₁ ∩ ContinuousPath.shift t₁ ⁻¹' reStrip H y₁ y₂ T') := hM
      _ ≤ planarBrownianMotion 0 (killedStrip e H y₁ y₂ T) := by
        refine measure_mono ?_
        rintro ω ⟨⟨hbox, -⟩, hstrip⟩
        obtain ⟨hs2, hend⟩ := hstrip
        refine ⟨fun s hs => ?_, ?_⟩
        · by_cases hst : s ≤ t₁
          · have h := hbox s hst
            simp only [layerF, max_lt_iff] at h
            exact ⟨by linarith [h.1.1], by linarith [h.1.2]⟩
          · rw [not_le] at hst
            have hu : s - t₁ ≤ T' := by
              rw [tsub_le_iff_left, htT]
              exact hs
            have h := hs2 (s - t₁) hu
            rw [ContinuousPath.shift_apply, add_tsub_cancel_of_le hst.le] at h
            exact ⟨by linarith [h.1], h.2⟩
        · have h := hend
          rw [ContinuousPath.shift_apply, htT] at h
          exact h
  refine ⟨p.toReal * κ * min 1 (L / 16), by positivity, fun e he0 he1 => ?_⟩
  have hmin1 : min 1 (L / 16) ≤ 1 := min_le_left _ _
  have hmin2 : min 1 (L / 16) ≤ L / 16 := min_le_right _ _
  have hmin0 : 0 ≤ min 1 (L / 16) := le_min zero_le_one (by positivity)
  by_cases he : e ≤ L / 16
  · calc ENNReal.ofReal (p.toReal * κ * min 1 (L / 16) * e) ≤ ENNReal.ofReal (p.toReal * (κ * e)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have : p.toReal * κ * min 1 (L / 16) * e ≤ p.toReal * κ * 1 * e := by gcongr
          linarith
      _ = p * ENNReal.ofReal (κ * e) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hpTop]
      _ ≤ _ := key e he0 he
  · rw [not_le] at he
    calc ENNReal.ofReal (p.toReal * κ * min 1 (L / 16) * e)
        ≤ ENNReal.ofReal (p.toReal * (κ * (L / 16))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have : p.toReal * κ * min 1 (L / 16) * e ≤ p.toReal * κ * (L / 16) * 1 := by gcongr
          linarith
      _ = p * ENNReal.ofReal (κ * (L / 16)) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hpTop]
      _ ≤ planarBrownianMotion 0 (killedStrip (L / 16) H y₁ y₂ T) := key (L / 16) (by positivity) le_rfl
      _ ≤ planarBrownianMotion 0 (killedStrip e H y₁ y₂ T) := measure_mono (killedStrip_mono he.le)

end MatedCRT.PeanosphereTriplePoints
