import MatedCRT.FirstPass.Derived.DiscGreenPotentialConvergence
import MatedCRT.FirstPass.Derived.ChartLimitTransport

/-!
# Canonical absolutely continuous approximations of a measure on the unit disc

For a measure `ν` on `ℂ` and `k ∈ ℕ`, the canonical rate

  `g_k(ν)(v) = 1/(k+1) + c_k⁻¹ ∫ χ_k(v - w) ν_k(dw)`

is the mollification of the restriction `ν_k` of `ν` to the disc `B(0, 1 - 1/(k+2))` (replaced by `0` if that
restriction has infinite mass) by the tent mollifier `χ_k(u) = (1 - (k+1)|u|)⁺` of radius `1/(k+1)` and mass
`c_k = ∫ χ_k`, plus the constant `1/(k+1)`. It is

* jointly Borel in the measure (for the Giry `σ`-algebra) and the point (`measurable_discCanonicalRate`), continuous
  in the point, positive and bounded;
* of mass at most `π/(k+1) + ν(B(0, 1))` on the unit disc;
* of upper power growth `∫_{B(v, s)} g_k(ν) ≤ C s^β` uniformly in `k` when `ν` has upper power growth
  (`lintegral_ball_discCanonicalRate_le`);
* convergent to `ν` vaguely on every closed disc `B̄(0, r)`, `r < 1`, when `ν(B(0, 1)) < ∞`
  (`tendsto_integral_mul_discCanonicalRate`).

These are the absolutely continuous additive functionals approximating the time change of Brownian motion killed on
exiting the unit disc by the additive functional with Revuz measure `ν` (Fukushima–Oshima–Takeda (2011), §5.1, §6.2;
Armitage–Gardiner, §4.3, for the Green potentials).
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set Metric
open scoped NNReal ENNReal

namespace MatedCRT

/-! ### The tent mollifier -/

/-- The tent mollifier `u ↦ (1 - (k+1)|u|)⁺` of radius `1/(k+1)`. -/
noncomputable def discMollifier (k : ℕ) (u : ℂ) : ℝ := max 0 (1 - ((k : ℝ) + 1) * ‖u‖)

theorem continuous_discMollifier (k : ℕ) : Continuous (discMollifier k) :=
  continuous_const.max (continuous_const.sub (continuous_const.mul continuous_norm))

theorem discMollifier_nonneg (k : ℕ) (u : ℂ) : 0 ≤ discMollifier k u := le_max_left _ _

theorem discMollifier_le_one (k : ℕ) (u : ℂ) : discMollifier k u ≤ 1 := by
  unfold discMollifier
  refine max_le zero_le_one ?_
  have : 0 ≤ ((k : ℝ) + 1) * ‖u‖ := by positivity
  linarith

theorem discMollifier_eq_zero (k : ℕ) {u : ℂ} (hu : 1 / ((k : ℝ) + 1) ≤ ‖u‖) : discMollifier k u = 0 := by
  unfold discMollifier
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : 1 ≤ ((k : ℝ) + 1) * ‖u‖ := by
    rw [mul_comm]
    exact (div_le_iff₀ hk).1 hu
  exact max_eq_left (by linarith)

theorem hasCompactSupport_discMollifier (k : ℕ) : HasCompactSupport (discMollifier k) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (1 / ((k : ℝ) + 1))) fun u hu => ?_
  rw [mem_closedBall_zero_iff, not_le] at hu
  exact discMollifier_eq_zero k hu.le

theorem integrable_discMollifier (k : ℕ) : Integrable (discMollifier k) :=
  (continuous_discMollifier k).integrable_of_hasCompactSupport (hasCompactSupport_discMollifier k)

theorem discMollifier_eq_smul (k : ℕ) (u : ℂ) : discMollifier k u = discMollifier 0 (((k : ℝ) + 1) • u) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  simp only [discMollifier, Nat.cast_zero, zero_add, one_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hk]

/-- The mass `c_k = ∫ χ_k` of the tent mollifier. -/
noncomputable def discMollifierMass (k : ℕ) : ℝ := ∫ u, discMollifier k u

theorem discMollifierMass_pos (k : ℕ) : 0 < discMollifierMass k :=
  (continuous_discMollifier k).integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) (x := 0)
    (hasCompactSupport_discMollifier k) (discMollifier_nonneg k) (by norm_num [discMollifier])

/-- The mass of the tent mollifier scales as `c_k = c_0 / (k+1)²`. -/
theorem discMollifierMass_eq (k : ℕ) : discMollifierMass k = discMollifierMass 0 / ((k : ℝ) + 1) ^ 2 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have h := MeasureTheory.Measure.integral_comp_smul_of_nonneg (μ := volume) (discMollifier 0)
    ((k : ℝ) + 1) (hR := hk)
  rw [Complex.finrank_real_complex, smul_eq_mul] at h
  unfold discMollifierMass
  simp_rw [discMollifier_eq_smul k]
  rw [h, inv_mul_eq_div]

/-- The translates of the mollifier have mass `c_k`. -/
theorem integral_discMollifier_sub (k : ℕ) (w : ℂ) : ∫ v, discMollifier k (v - w) = discMollifierMass k :=
  integral_sub_right_eq_self (discMollifier k) w

theorem lintegral_discMollifier_sub (k : ℕ) (w : ℂ) :
    ∫⁻ v, ENNReal.ofReal (discMollifier k (v - w)) = ENNReal.ofReal (discMollifierMass k) := by
  rw [← integral_discMollifier_sub k w, ofReal_integral_eq_lintegral_ofReal]
  · exact (integrable_discMollifier k).comp_sub_right w
  · exact ae_of_all _ fun v => discMollifier_nonneg k _

/-! ### The truncated measure -/

/-- The radius `1 - 1/(k+2)` of the truncation disc. -/
noncomputable def discTruncationRadius (k : ℕ) : ℝ := 1 - 1 / ((k : ℝ) + 2)

theorem discTruncationRadius_lt_one (k : ℕ) : discTruncationRadius k < 1 := by
  unfold discTruncationRadius
  have : 0 < 1 / ((k : ℝ) + 2) := by positivity
  linarith

open Classical in
/-- The restriction of `ν` to `B(0, 1 - 1/(k+2))` if it is finite, and `0` otherwise. -/
noncomputable def discTruncation (k : ℕ) (ν : Measure ℂ) : Measure ℂ :=
  if ν (ball 0 (discTruncationRadius k)) < ⊤ then ν.restrict (ball 0 (discTruncationRadius k)) else 0

theorem discTruncation_univ_lt_top (k : ℕ) (ν : Measure ℂ) : discTruncation k ν univ < ⊤ := by
  unfold discTruncation
  split_ifs with h
  · rw [Measure.restrict_apply_univ]
    exact h
  · simp

instance (k : ℕ) (ν : Measure ℂ) : IsFiniteMeasure (discTruncation k ν) :=
  ⟨discTruncation_univ_lt_top k ν⟩

theorem discTruncation_le (k : ℕ) (ν : Measure ℂ) (s : Set ℂ) :
    discTruncation k ν s ≤ ν (s ∩ ball 0 (discTruncationRadius k)) := by
  unfold discTruncation
  split_ifs
  · exact (Measure.restrict_apply' measurableSet_ball).le
  · simp

theorem discTruncation_eq (k : ℕ) {ν : Measure ℂ} (hν : ν (ball 0 (discTruncationRadius k)) < ⊤) :
    discTruncation k ν = ν.restrict (ball 0 (discTruncationRadius k)) := by
  simp only [discTruncation, hν, ↓reduceIte]

theorem measurable_discTruncation (k : ℕ) : Measurable (discTruncation k) := by
  have hset : MeasurableSet {ν : Measure ℂ | ν (ball 0 (discTruncationRadius k)) < ⊤} :=
    measurableSet_lt (Measure.measurable_coe measurableSet_ball) measurable_const
  have hres : Measurable fun ν : Measure ℂ => ν.restrict (ball 0 (discTruncationRadius k)) := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.restrict_apply hs]
    exact Measure.measurable_coe (hs.inter measurableSet_ball)
  unfold discTruncation
  exact Measurable.ite hset hres measurable_const

/-! ### The canonical rate -/

/-- The mollified density `c_k⁻¹ ∫ χ_k(v - w) ν_k(dw)` of the truncated measure. -/
noncomputable def discMollifiedDensity (k : ℕ) (ν : Measure ℂ) (v : ℂ) : ℝ :=
  (∫ w, discMollifier k (v - w) ∂(discTruncation k ν)) / discMollifierMass k

/-- **The canonical rate** `g_k(ν) = 1/(k+1) + c_k⁻¹ ∫ χ_k(· - w) ν_k(dw)`. -/
noncomputable def discCanonicalRate (k : ℕ) (ν : Measure ℂ) (v : ℂ) : ℝ :=
  1 / ((k : ℝ) + 1) + discMollifiedDensity k ν v

theorem discMollifiedDensity_nonneg (k : ℕ) (ν : Measure ℂ) (v : ℂ) : 0 ≤ discMollifiedDensity k ν v :=
  div_nonneg (integral_nonneg fun w => discMollifier_nonneg k (v - w)) (discMollifierMass_pos k).le

theorem discMollifiedDensity_le (k : ℕ) (ν : Measure ℂ) (v : ℂ) :
    discMollifiedDensity k ν v ≤ (discTruncation k ν univ).toReal / discMollifierMass k := by
  refine div_le_div_of_nonneg_right ?_ (discMollifierMass_pos k).le
  calc ∫ w, discMollifier k (v - w) ∂(discTruncation k ν) ≤ ∫ _w, (1 : ℝ) ∂(discTruncation k ν) :=
        integral_mono_of_nonneg (ae_of_all _ fun w => discMollifier_nonneg k _) (integrable_const _)
          (ae_of_all _ fun w => discMollifier_le_one k _)
    _ = (discTruncation k ν univ).toReal := by
        rw [integral_const, smul_eq_mul, mul_one, Measure.real]

theorem discCanonicalRate_pos (k : ℕ) (ν : Measure ℂ) (v : ℂ) : 0 < discCanonicalRate k ν v :=
  add_pos_of_pos_of_nonneg (by positivity) (discMollifiedDensity_nonneg k ν v)

theorem abs_discCanonicalRate_le (k : ℕ) (ν : Measure ℂ) (v : ℂ) :
    |discCanonicalRate k ν v| ≤ 1 / ((k : ℝ) + 1) + (discTruncation k ν univ).toReal / discMollifierMass k := by
  rw [abs_of_pos (discCanonicalRate_pos k ν v)]
  exact add_le_add le_rfl (discMollifiedDensity_le k ν v)

theorem continuous_discMollifiedDensity (k : ℕ) (ν : Measure ℂ) : Continuous (discMollifiedDensity k ν) := by
  unfold discMollifiedDensity
  refine Continuous.div_const ?_ _
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) ?_ ?_ (integrable_const _) ?_
  · exact fun v => ((continuous_discMollifier k).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · intro v
    refine ae_of_all _ fun w => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (discMollifier_nonneg k _)]
    exact discMollifier_le_one k _
  · exact ae_of_all _ fun w => (continuous_discMollifier k).comp (continuous_id.sub continuous_const)

theorem continuous_discCanonicalRate (k : ℕ) (ν : Measure ℂ) : Continuous (discCanonicalRate k ν) :=
  continuous_const.add (continuous_discMollifiedDensity k ν)

/-- **The canonical rate is jointly Borel in the measure and the point.** -/
theorem measurable_discCanonicalRate (k : ℕ) :
    Measurable (Function.uncurry (discCanonicalRate k)) := by
  have hint : ∀ v : ℂ, Measurable fun ν : Measure ℂ => ∫ w, discMollifier k (v - w) ∂(discTruncation k ν) := by
    intro v
    have hl : Measurable fun ν : Measure ℂ =>
        ∫⁻ w, ENNReal.ofReal (discMollifier k (v - w)) ∂(discTruncation k ν) :=
      (Measure.measurable_lintegral
        ((continuous_discMollifier k).comp (continuous_const.sub continuous_id)).measurable.ennreal_ofReal).comp
        (measurable_discTruncation k)
    have heq : (fun ν : Measure ℂ => ∫ w, discMollifier k (v - w) ∂(discTruncation k ν)) =
        fun ν => (∫⁻ w, ENNReal.ofReal (discMollifier k (v - w)) ∂(discTruncation k ν)).toReal := by
      funext ν
      exact integral_eq_lintegral_of_nonneg_ae (f := fun w => discMollifier k (v - w))
        (ae_of_all _ fun w => discMollifier_nonneg k (v - w))
        ((continuous_discMollifier k).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    rw [heq]
    exact hl.ennreal_toReal
  have hu : Measurable (Function.uncurry fun (v : ℂ) (ν : Measure ℂ) => discCanonicalRate k ν v) :=
    measurable_uncurry_of_continuous_of_measurable (fun ν => continuous_discCanonicalRate k ν)
      fun v => show Measurable fun ν : Measure ℂ => discCanonicalRate k ν v by
        unfold discCanonicalRate discMollifiedDensity
        exact measurable_const.add ((hint v).div_const _)
  exact hu.comp measurable_swap

/-! ### Mass and power growth -/

theorem ofReal_discMollifiedDensity (k : ℕ) (ν : Measure ℂ) (v : ℂ) :
    ENNReal.ofReal (discMollifiedDensity k ν v) =
      (∫⁻ w, ENNReal.ofReal (discMollifier k (v - w)) ∂(discTruncation k ν)) /
        ENNReal.ofReal (discMollifierMass k) := by
  unfold discMollifiedDensity
  rw [ENNReal.ofReal_div_of_pos (discMollifierMass_pos k), ofReal_integral_eq_lintegral_ofReal]
  · refine (integrable_const (1 : ℝ)).mono'
      ((continuous_discMollifier k).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (discMollifier_nonneg k _)]
    exact discMollifier_le_one k _
  · exact ae_of_all _ fun w => discMollifier_nonneg k _

/-- **Mass of the mollified density on a disc.** If every translate `χ_k(· - w)` has mass at most `a` on `B(v₀, ρ)`,
then the mollified density has mass at most `a ν_k(B(v₀, ρ + 1/(k+1))) / c_k` on `B(v₀, ρ)` (Tonelli). -/
theorem lintegral_ball_discMollifiedDensity_le (k : ℕ) (ν : Measure ℂ) (v₀ : ℂ) (ρ : ℝ) {a : ℝ≥0∞}
    (ha : ∀ w, ∫⁻ v in ball v₀ ρ, ENNReal.ofReal (discMollifier k (v - w)) ≤ a) :
    ∫⁻ v in ball v₀ ρ, ENNReal.ofReal (discMollifiedDensity k ν v) ≤
      a * discTruncation k ν (ball v₀ (ρ + 1 / ((k : ℝ) + 1))) / ENNReal.ofReal (discMollifierMass k) := by
  have hc : ENNReal.ofReal (discMollifierMass k) ≠ 0 := (ENNReal.ofReal_pos.2 (discMollifierMass_pos k)).ne'
  simp_rw [ofReal_discMollifiedDensity, div_eq_mul_inv]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hc)]
  refine mul_le_mul' ?_ le_rfl
  have hF : Measurable fun p : ℂ × ℂ => ENNReal.ofReal (discMollifier k (p.1 - p.2)) :=
    (ENNReal.continuous_ofReal.comp ((continuous_discMollifier k).comp
      (continuous_fst.sub continuous_snd))).measurable
  rw [lintegral_lintegral_swap hF.aemeasurable]
  calc ∫⁻ w, (∫⁻ v in ball v₀ ρ, ENNReal.ofReal (discMollifier k (v - w))) ∂(discTruncation k ν)
      ≤ ∫⁻ w, (ball v₀ (ρ + 1 / ((k : ℝ) + 1))).indicator (fun _ => a) w ∂(discTruncation k ν) := by
        refine lintegral_mono fun w => ?_
        by_cases hw : w ∈ ball v₀ (ρ + 1 / ((k : ℝ) + 1))
        · rw [indicator_of_mem hw]
          exact ha w
        · rw [indicator_of_notMem hw]
          have h0 : ∀ v ∈ ball v₀ ρ, ENNReal.ofReal (discMollifier k (v - w)) = 0 := by
            intro v hv
            rw [mem_ball] at hv hw
            have hd : 1 / ((k : ℝ) + 1) ≤ ‖v - w‖ := by
              rw [← dist_eq_norm]
              have h3 := dist_triangle w v v₀
              rw [dist_comm w v] at h3
              linarith [not_lt.1 hw]
            rw [discMollifier_eq_zero k hd, ENNReal.ofReal_zero]
          exact le_of_eq ((setLIntegral_congr_fun measurableSet_ball h0).trans lintegral_zero)
    _ = a * discTruncation k ν (ball v₀ (ρ + 1 / ((k : ℝ) + 1))) :=
        lintegral_indicator_const measurableSet_ball a

theorem volume_ball_complex (z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    volume (ball z s) = ENNReal.ofReal (Real.pi * s ^ 2) := by
  rw [Complex.volume_ball, ← ENNReal.ofReal_pow hs, ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- The canonical rate on a disc: the constant part plus the mollified density. -/
theorem lintegral_ball_discCanonicalRate_eq (k : ℕ) (ν : Measure ℂ) (z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ v in ball z s, ENNReal.ofReal (discCanonicalRate k ν v) =
      ENNReal.ofReal (1 / ((k : ℝ) + 1) * (Real.pi * s ^ 2)) +
        ∫⁻ v in ball z s, ENNReal.ofReal (discMollifiedDensity k ν v) := by
  have hδ : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
  simp_rw [discCanonicalRate, ENNReal.ofReal_add hδ (discMollifiedDensity_nonneg k ν _)]
  rw [lintegral_add_left measurable_const, setLIntegral_const, volume_ball_complex z hs,
    ← ENNReal.ofReal_mul hδ]

/-- The real inequality `s² δ^β ≤ s^β δ²` for `0 < s ≤ δ` and `β ≤ 2`. -/
theorem sq_mul_rpow_le_rpow_mul_sq {s δ β : ℝ} (hs : 0 < s) (hsδ : s ≤ δ) (hβ2 : β ≤ 2) :
    s ^ 2 * δ ^ β ≤ s ^ β * δ ^ 2 := by
  have hδ : 0 < δ := hs.trans_le hsδ
  have h1 : s ^ 2 = s ^ β * s ^ (2 - β) := by
    rw [← Real.rpow_add hs, add_sub_cancel, ← Real.rpow_natCast]
    norm_num
  have h2 : δ ^ 2 = δ ^ β * δ ^ (2 - β) := by
    rw [← Real.rpow_add hδ, add_sub_cancel, ← Real.rpow_natCast]
    norm_num
  have h3 : s ^ (2 - β) ≤ δ ^ (2 - β) := Real.rpow_le_rpow hs.le hsδ (by linarith)
  rw [h1, h2]
  have h4 : 0 ≤ s ^ β * δ ^ β := by positivity
  nlinarith [h4, h3]

/-- **Upper power growth of the canonical rates, uniformly in `k`.** If `ν(B(z, s)) ≤ C s^β` for `z ∈ B(0, R)` and
`s < s₀ ≤ 1` (`β ≤ 2`), then for every `k` with `2/(k+1) < s₀`, every `z ∈ B(0, R)` and `2s < s₀`,
`∫_{B(z, s)} g_k(ν) ≤ (π + C 2^β + π C 2^β / c_0) s^β`. -/
theorem lintegral_ball_discCanonicalRate_le {ν : Measure ℂ} {R s₀ C β : ℝ} (hs₀1 : s₀ ≤ 1) (hβ2 : β ≤ 2) (hC : 0 ≤ C)
    (hpow : ∀ z ∈ ball (0 : ℂ) R, ∀ s, 0 < s → s < s₀ → ν (ball z s) ≤ ENNReal.ofReal (C * s ^ β))
    {k : ℕ} (hk : 2 / ((k : ℝ) + 1) < s₀) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {s : ℝ} (hs : 0 < s)
    (hs1 : 2 * s < s₀) :
    ∫⁻ v in ball z s, ENNReal.ofReal (discCanonicalRate k ν v) ≤
      ENNReal.ofReal ((Real.pi + C * 2 ^ β + Real.pi * C * 2 ^ β / discMollifierMass 0) * s ^ β) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hδ : 0 < 1 / ((k : ℝ) + 1) := by positivity
  have hδ1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hk1]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hc0 := discMollifierMass_pos 0
  have hcm : discMollifierMass k = discMollifierMass 0 * (1 / ((k : ℝ) + 1)) ^ 2 := by
    rw [discMollifierMass_eq, div_pow, one_pow, mul_one_div]
  have hs1' : s < 1 := by linarith
  have hsβ : s ^ 2 ≤ s ^ β := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hs hs1'.le (by norm_num; linarith)
  have hsβ0 : 0 ≤ s ^ β := by positivity
  have h2β : 0 ≤ C * 2 ^ β := by positivity
  have hconst : 0 ≤ Real.pi * C * 2 ^ β / discMollifierMass 0 := by positivity
  have hfirst : 1 / ((k : ℝ) + 1) * (Real.pi * s ^ 2) ≤ Real.pi * s ^ β := by
    have h5 : Real.pi * s ^ 2 ≤ Real.pi * s ^ β := mul_le_mul_of_nonneg_left hsβ Real.pi_pos.le
    have h6 : 1 / ((k : ℝ) + 1) * (Real.pi * s ^ 2) ≤ 1 * (Real.pi * s ^ 2) :=
      mul_le_mul_of_nonneg_right hδ1 (by positivity)
    linarith
  have htrunc : ∀ ρ : ℝ, discTruncation k ν (ball z ρ) ≤ ν (ball z ρ) := fun ρ =>
    (discTruncation_le k ν _).trans (measure_mono inter_subset_left)
  rw [lintegral_ball_discCanonicalRate_eq k ν z hs.le]
  -- the mollified part, in the two regimes `1/(k+1) ≤ s` and `s < 1/(k+1)`
  obtain ⟨Y, hY0, hYle, hYbd⟩ : ∃ Y : ℝ, 0 ≤ Y ∧
      ∫⁻ v in ball z s, ENNReal.ofReal (discMollifiedDensity k ν v) ≤ ENNReal.ofReal Y ∧
      Y ≤ C * 2 ^ β * s ^ β + Real.pi * C * 2 ^ β / discMollifierMass 0 * s ^ β := by
    by_cases hsδ : 1 / ((k : ℝ) + 1) ≤ s
    · refine ⟨C * (2 * s) ^ β, by positivity, ?_, ?_⟩
      · have hm := lintegral_ball_discMollifiedDensity_le k ν z s (a := ENNReal.ofReal (discMollifierMass k))
          fun w => (setLIntegral_le_lintegral _ _).trans (lintegral_discMollifier_sub k w).le
        rw [mul_div_assoc, ENNReal.mul_div_cancel (ENNReal.ofReal_pos.2 (discMollifierMass_pos k)).ne'
          ENNReal.ofReal_ne_top] at hm
        refine hm.trans ((htrunc _).trans ((measure_mono (ball_subset_ball (by linarith))).trans
          (hpow z hz (2 * s) (by linarith) hs1)))
      · rw [Real.mul_rpow (by norm_num) hs.le]
        have : C * (2 ^ β * s ^ β) = C * 2 ^ β * s ^ β := by ring
        rw [this]
        have : 0 ≤ Real.pi * C * 2 ^ β / discMollifierMass 0 * s ^ β := by positivity
        linarith
    · have hsδ' : s < 1 / ((k : ℝ) + 1) := lt_of_not_ge hsδ
      set δ : ℝ := 1 / ((k : ℝ) + 1) with hδdef
      refine ⟨Real.pi * s ^ 2 * (C * (2 * δ) ^ β) / (discMollifierMass 0 * δ ^ 2), by positivity, ?_, ?_⟩
      · have hvol : ∀ w, ∫⁻ v in ball z s, ENNReal.ofReal (discMollifier k (v - w)) ≤
            ENNReal.ofReal (Real.pi * s ^ 2) := by
          intro w
          calc ∫⁻ v in ball z s, ENNReal.ofReal (discMollifier k (v - w))
              ≤ ∫⁻ _v in ball z s, 1 :=
                lintegral_mono fun v => ENNReal.ofReal_le_one.2 (discMollifier_le_one k _)
            _ = ENNReal.ofReal (Real.pi * s ^ 2) := by
                rw [setLIntegral_const, one_mul, volume_ball_complex z hs.le]
        have hm := lintegral_ball_discMollifiedDensity_le k ν z s hvol
        have hν2 : discTruncation k ν (ball z (s + δ)) ≤ ENNReal.ofReal (C * (2 * δ) ^ β) :=
          (htrunc _).trans ((measure_mono (ball_subset_ball (by linarith))).trans
            (hpow z hz (2 * δ) (by positivity) (by rw [hδdef, mul_one_div]; exact hk)))
        refine hm.trans ?_
        rw [hcm]
        calc ENNReal.ofReal (Real.pi * s ^ 2) * discTruncation k ν (ball z (s + δ)) /
              ENNReal.ofReal (discMollifierMass 0 * δ ^ 2)
            ≤ ENNReal.ofReal (Real.pi * s ^ 2) * ENNReal.ofReal (C * (2 * δ) ^ β) /
              ENNReal.ofReal (discMollifierMass 0 * δ ^ 2) :=
              ENNReal.div_le_div_right (mul_le_mul' le_rfl hν2) _
          _ = ENNReal.ofReal (Real.pi * s ^ 2 * (C * (2 * δ) ^ β) / (discMollifierMass 0 * δ ^ 2)) := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
      · have hmix := sq_mul_rpow_le_rpow_mul_sq hs hsδ'.le hβ2
        rw [Real.mul_rpow (by norm_num) hδ.le]
        have hc0δ : 0 < discMollifierMass 0 * δ ^ 2 := by positivity
        rw [div_le_iff₀ hc0δ]
        have h10 : Real.pi * C * 2 ^ β / discMollifierMass 0 * s ^ β * (discMollifierMass 0 * δ ^ 2) =
            Real.pi * C * 2 ^ β * (s ^ β * δ ^ 2) := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hc0.ne']
          ring
        rw [add_mul, h10]
        have h7 : Real.pi * s ^ 2 * (C * (2 ^ β * δ ^ β)) = Real.pi * C * 2 ^ β * (s ^ 2 * δ ^ β) := by ring
        rw [h7]
        have h8 : Real.pi * C * 2 ^ β * (s ^ 2 * δ ^ β) ≤ Real.pi * C * 2 ^ β * (s ^ β * δ ^ 2) :=
          mul_le_mul_of_nonneg_left hmix (by positivity)
        have h9 : 0 ≤ C * 2 ^ β * s ^ β * (discMollifierMass 0 * δ ^ 2) := by positivity
        linarith
  calc ENNReal.ofReal (1 / ((k : ℝ) + 1) * (Real.pi * s ^ 2)) +
        ∫⁻ v in ball z s, ENNReal.ofReal (discMollifiedDensity k ν v)
      ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1) * (Real.pi * s ^ 2)) + ENNReal.ofReal Y := add_le_add le_rfl hYle
    _ = ENNReal.ofReal (1 / ((k : ℝ) + 1) * (Real.pi * s ^ 2) + Y) :=
        (ENNReal.ofReal_add (by positivity) hY0).symm
    _ ≤ ENNReal.ofReal ((Real.pi + C * 2 ^ β + Real.pi * C * 2 ^ β / discMollifierMass 0) * s ^ β) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : (Real.pi + C * 2 ^ β + Real.pi * C * 2 ^ β / discMollifierMass 0) * s ^ β =
            Real.pi * s ^ β + (C * 2 ^ β * s ^ β + Real.pi * C * 2 ^ β / discMollifierMass 0 * s ^ β) := by ring
        rw [e]
        linarith

/-- **Mass of the canonical rate on a disc.** `∫_{B(0, ρ)} g_k(ν) ≤ π ρ² + ν(B(0, 1))` for `0 ≤ ρ`. -/
theorem lintegral_ball_zero_discCanonicalRate_le (k : ℕ) (ν : Measure ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫⁻ v in ball (0 : ℂ) ρ, ENNReal.ofReal (discCanonicalRate k ν v) ≤
      ENNReal.ofReal (Real.pi * ρ ^ 2) + ν (ball 0 1) := by
  rw [lintegral_ball_discCanonicalRate_eq k ν 0 hρ]
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hδ1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hk1]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  refine add_le_add (ENNReal.ofReal_le_ofReal ?_) ?_
  · have h6 : 1 / ((k : ℝ) + 1) * (Real.pi * ρ ^ 2) ≤ 1 * (Real.pi * ρ ^ 2) :=
      mul_le_mul_of_nonneg_right hδ1 (by positivity)
    linarith
  · have hm := lintegral_ball_discMollifiedDensity_le k ν 0 ρ (a := ENNReal.ofReal (discMollifierMass k))
      fun w => (setLIntegral_le_lintegral _ _).trans (lintegral_discMollifier_sub k w).le
    rw [mul_div_assoc, ENNReal.mul_div_cancel (ENNReal.ofReal_pos.2 (discMollifierMass_pos k)).ne'
      ENNReal.ofReal_ne_top] at hm
    refine hm.trans ((discTruncation_le k ν _).trans (measure_mono ?_))
    refine inter_subset_right.trans (ball_subset_ball (discTruncationRadius_lt_one k).le)

/-! ### Vague convergence -/

/-- The mollification `Φ_k(w) = c_k⁻¹ ∫ F(v) χ_k(v - w) dv` of a test function `F`. -/
noncomputable def discMollifiedTest (k : ℕ) (F : ℂ → ℝ) (w : ℂ) : ℝ :=
  (discMollifierMass k)⁻¹ * ∫ v, F v * discMollifier k (v - w)

theorem continuous_discMollifiedTest (k : ℕ) {F : ℂ → ℝ} (hF : Continuous F) (hFi : Integrable F) :
    Continuous (discMollifiedTest k F) := by
  unfold discMollifiedTest
  refine continuous_const.mul ?_
  refine continuous_of_dominated (bound := fun v => |F v|) ?_ ?_ hFi.abs ?_
  · exact fun _ => (hF.mul ((continuous_discMollifier k).comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable
  · intro w
    refine ae_of_all _ fun v => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (discMollifier_nonneg k (v - w))]
    exact mul_le_of_le_one_right (abs_nonneg _) (discMollifier_le_one k (v - w))
  · exact ae_of_all _ fun _ => continuous_const.mul ((continuous_discMollifier k).comp
      (continuous_const.sub continuous_id))

/-- The mollification of `F` is within `η` of `F` if `F` oscillates by at most `η` at distances `< 1/(k+1)`. -/
theorem abs_discMollifiedTest_sub_le (k : ℕ) {F : ℂ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    {η : ℝ} (hη : ∀ v w : ℂ, ‖v - w‖ < 1 / ((k : ℝ) + 1) → |F v - F w| ≤ η) (w : ℂ) :
    |discMollifiedTest k F w - F w| ≤ η := by
  have hc := discMollifierMass_pos k
  have hint1 : Integrable (fun v => F v * discMollifier k (v - w)) :=
    (hF.mul ((continuous_discMollifier k).comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hint2 : Integrable (fun v => F w * discMollifier k (v - w)) :=
    ((integrable_discMollifier k).comp_sub_right w).const_mul (F w)
  have heq : discMollifiedTest k F w - F w =
      (discMollifierMass k)⁻¹ * ∫ v, (F v - F w) * discMollifier k (v - w) := by
    have h2 : ∫ v, F w * discMollifier k (v - w) = F w * discMollifierMass k := by
      rw [integral_const_mul, integral_discMollifier_sub]
    have h3 : ∫ v, (F v - F w) * discMollifier k (v - w) =
        (∫ v, F v * discMollifier k (v - w)) - F w * discMollifierMass k := by
      rw [← h2, ← integral_sub hint1 hint2]
      congr 1
      funext v
      ring
    rw [h3, mul_sub, discMollifiedTest, mul_comm (F w), ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  have hb : |∫ v, (F v - F w) * discMollifier k (v - w)| ≤ η * discMollifierMass k := by
    rw [← integral_discMollifier_sub k w, ← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (((integrable_discMollifier k).comp_sub_right w).const_mul η)
      (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (discMollifier_nonneg k (v - w))]
    by_cases hv : ‖v - w‖ < 1 / ((k : ℝ) + 1)
    · exact mul_le_mul_of_nonneg_right (hη v w hv) (discMollifier_nonneg k (v - w))
    · rw [discMollifier_eq_zero k (not_lt.1 hv)]
      simp
  rw [heq, abs_mul, abs_of_pos (inv_pos.2 hc)]
  calc (discMollifierMass k)⁻¹ * |∫ v, (F v - F w) * discMollifier k (v - w)|
      ≤ (discMollifierMass k)⁻¹ * (η * discMollifierMass k) := mul_le_mul_of_nonneg_left hb (inv_pos.2 hc).le
    _ = η := by rw [mul_comm η, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

/-- Fubini for the canonical rate: `∫ F g_k(ν) = (k+1)⁻¹ ∫ F + ∫ Φ_k dν_k`. -/
theorem integral_mul_discCanonicalRate_eq (k : ℕ) (ν : Measure ℂ) {F : ℂ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    ∫ v, F v * discCanonicalRate k ν v =
      1 / ((k : ℝ) + 1) * (∫ v, F v) + ∫ w, discMollifiedTest k F w ∂(discTruncation k ν) := by
  have hFi : Integrable F := hF.integrable_of_hasCompactSupport hFc
  have hint1 : Integrable (fun v => 1 / ((k : ℝ) + 1) * F v) := hFi.const_mul _
  have hint2 : Integrable (fun v => F v * discMollifiedDensity k ν v) :=
    (hF.mul (continuous_discMollifiedDensity k ν)).integrable_of_hasCompactSupport hFc.mul_right
  have hsplit : (fun v => F v * discCanonicalRate k ν v) =
      fun v => 1 / ((k : ℝ) + 1) * F v + F v * discMollifiedDensity k ν v := by
    funext v
    simp only [discCanonicalRate]
    ring
  have hprod : Integrable (Function.uncurry fun (v w : ℂ) => F v * discMollifier k (v - w))
      ((volume : Measure ℂ).prod (discTruncation k ν)) := by
    refine Integrable.mono' (hFi.abs.mul_prod (integrable_const (1 : ℝ))) ?_ (ae_of_all _ fun p => ?_)
    · exact ((hF.comp continuous_fst).mul ((continuous_discMollifier k).comp
        (continuous_fst.sub continuous_snd))).aestronglyMeasurable
    · show ‖F p.1 * discMollifier k (p.1 - p.2)‖ ≤ |F p.1| * 1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (discMollifier_nonneg k _)]
      exact mul_le_mul_of_nonneg_left (discMollifier_le_one k _) (abs_nonneg _)
  have hfub : ∫ v, F v * discMollifiedDensity k ν v = ∫ w, discMollifiedTest k F w ∂(discTruncation k ν) := by
    calc ∫ v, F v * discMollifiedDensity k ν v
        = ∫ v, (discMollifierMass k)⁻¹ * ∫ w, F v * discMollifier k (v - w) ∂(discTruncation k ν) := by
          refine integral_congr_ae (ae_of_all _ fun v => ?_)
          simp only [discMollifiedDensity]
          rw [integral_const_mul]
          ring
      _ = (discMollifierMass k)⁻¹ * ∫ w, (∫ v, F v * discMollifier k (v - w)) ∂(discTruncation k ν) := by
          rw [integral_const_mul, integral_integral_swap hprod]
      _ = ∫ w, discMollifiedTest k F w ∂(discTruncation k ν) := by
          simp only [discMollifiedTest]
          rw [integral_const_mul]
  rw [hsplit, integral_add hint1 hint2, integral_const_mul, hfub]

/-- **Vague convergence of the canonical rates.** If `ν(B(0, 1)) < ∞`, then for every continuous `F` supported in a
closed disc `B̄(0, r)` with `r < 1`, `∫ F g_k(ν) → ∫ F dν` as `k → ∞`. -/
theorem tendsto_integral_mul_discCanonicalRate {ν : Measure ℂ} (hν : ν (ball 0 1) < ⊤) {r : ℝ} (hr : r < 1)
    {F : ℂ → ℝ} (hF : Continuous F) (hFs : tsupport F ⊆ closedBall 0 r) :
    Tendsto (fun k : ℕ => ∫ v, F v * discCanonicalRate k ν v) atTop (𝓝 (∫ v, F v ∂ν)) := by
  have hFc : HasCompactSupport F :=
    (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset (isClosed_tsupport F) hFs
  have hFi : Integrable F := hF.integrable_of_hasCompactSupport hFc
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, (ν (ball 0 1)).toReal = M := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hMdef ▸ ENNReal.toReal_nonneg
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = ε / (2 * (M + 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hη_def]; positivity
  obtain ⟨δ, hδ, hδη⟩ := Metric.uniformContinuous_iff.1 (hFc.uniformContinuous_of_continuous hF) η hη
  have hI : 0 < |∫ v, F v| + 1 := by positivity
  have hc : 0 < min δ (min (1 - r) (ε / (2 * (|∫ v, F v| + 1)))) :=
    lt_min hδ (lt_min (by linarith) (by positivity))
  filter_upwards [h0.eventually (gt_mem_nhds hc)] with k hk
  have hkδ : 1 / ((k : ℝ) + 1) < δ := hk.trans_le (min_le_left _ _)
  have hkr : 1 / ((k : ℝ) + 1) < 1 - r := hk.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hkε : 1 / ((k : ℝ) + 1) < ε / (2 * (|∫ v, F v| + 1)) :=
    hk.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hηk : ∀ v w : ℂ, ‖v - w‖ < 1 / ((k : ℝ) + 1) → |F v - F w| ≤ η := by
    intro v w hvw
    have h := hδη (a := v) (b := w) (by rw [dist_eq_norm]; exact hvw.trans hkδ)
    rw [Real.dist_eq] at h
    exact h.le
  have hρν : ν (ball 0 (discTruncationRadius k)) < ⊤ :=
    (measure_mono (ball_subset_ball (discTruncationRadius_lt_one k).le)).trans_lt hν
  have hρr : r < discTruncationRadius k := by
    unfold discTruncationRadius
    have : 1 / ((k : ℝ) + 2) ≤ 1 / ((k : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hFν : ∫ w, F w ∂(discTruncation k ν) = ∫ w, F w ∂ν := by
    rw [discTruncation_eq k hρν]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport fun hxF => hx ?_
    have h := hFs hxF
    rw [mem_closedBall_zero_iff] at h
    exact mem_ball_zero_iff.2 (h.trans_lt hρr)
  have hFk : Integrable F (discTruncation k ν) := hF.integrable_of_hasCompactSupport hFc
  have hΦF : Integrable (fun w => discMollifiedTest k F w - F w) (discTruncation k ν) :=
    (integrable_const η).mono' (((continuous_discMollifiedTest k hF hFi).sub hF).aestronglyMeasurable)
      (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact abs_discMollifiedTest_sub_le k hF hFc hηk w)
  have hΦ : Integrable (discMollifiedTest k F) (discTruncation k ν) :=
    (hΦF.add hFk).congr (ae_of_all _ fun w => by simp only [Pi.add_apply, sub_add_cancel])
  have hsub : ∫ w, discMollifiedTest k F w ∂(discTruncation k ν) - ∫ w, F w ∂ν =
      ∫ w, (discMollifiedTest k F w - F w) ∂(discTruncation k ν) := by
    rw [← hFν, integral_sub hΦ hFk]
  have hreal : (discTruncation k ν).real univ ≤ M := by
    rw [← hMdef]
    exact ENNReal.toReal_mono hν.ne ((discTruncation_le k ν univ).trans
      (measure_mono (inter_subset_right.trans (ball_subset_ball (discTruncationRadius_lt_one k).le))))
  have hbd1 : |∫ w, (discMollifiedTest k F w - F w) ∂(discTruncation k ν)| ≤ η * M := by
    have h := norm_integral_le_of_norm_le_const (μ := discTruncation k ν)
      (ae_of_all _ fun w => (show ‖discMollifiedTest k F w - F w‖ ≤ η by
        rw [Real.norm_eq_abs]; exact abs_discMollifiedTest_sub_le k hF hFc hηk w))
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left hreal hη.le)
  have hηM : η * M ≤ ε / 2 := by
    rw [hη_def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hbd2 : |1 / ((k : ℝ) + 1) * ∫ v, F v| < ε / 2 := by
    have hk0 : 0 < 1 / ((k : ℝ) + 1) := by positivity
    rw [abs_mul, abs_of_pos hk0]
    calc 1 / ((k : ℝ) + 1) * |∫ v, F v| ≤ 1 / ((k : ℝ) + 1) * (|∫ v, F v| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hk0.le
      _ < ε / (2 * (|∫ v, F v| + 1)) * (|∫ v, F v| + 1) := mul_lt_mul_of_pos_right hkε hI
      _ = ε / 2 := by rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hI.ne']
  have hmain : 1 / ((k : ℝ) + 1) * (∫ v, F v) + ∫ w, discMollifiedTest k F w ∂(discTruncation k ν) -
      ∫ w, F w ∂ν =
      1 / ((k : ℝ) + 1) * (∫ v, F v) + ∫ w, (discMollifiedTest k F w - F w) ∂(discTruncation k ν) := by
    rw [← hsub]
    ring
  rw [Real.dist_eq, integral_mul_discCanonicalRate_eq k ν hF hFc, hmain]
  calc |1 / ((k : ℝ) + 1) * (∫ v, F v) + ∫ w, (discMollifiedTest k F w - F w) ∂(discTruncation k ν)|
      ≤ |1 / ((k : ℝ) + 1) * ∫ v, F v| + |∫ w, (discMollifiedTest k F w - F w) ∂(discTruncation k ν)| :=
        abs_add_le _ _
    _ < ε := by linarith

end MatedCRT
