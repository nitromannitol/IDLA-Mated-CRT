import MatedCRT.FirstPass.Derived.KilledOccupationMaximal
import MatedCRT.FirstPass.Derived.KilledPotentialGreen
import HarmonicBalls.Proofs.Potential.GreenBall

/-!
# Occupation functionals of Brownian motion killed on exiting nested discs

For open sets `D' ⊆ D`, the occupation functional `A^f = ∫_0^{τ_D} f(b_s) ds` of a path killed at its exit from `D`
splits into the occupation functional of the path killed at its exit from `D'` and the part
`∫_{τ_{D'}}^{τ_D} f(b_s) ds` collected between the two exit times (`killedOccupationBetween`). The expectation of the
latter is the difference `u^D_f - u^{D'}_f` of the potentials (`lintegral_killedOccupationBetween`). For the discs
`B(0, r) ⊆ B(0, 1)` and the start `0`, the explicit Green function of a disc gives
`u^{B(0,1)}_f(0) - u^{B(0,r)}_f(0) ≤ π⁻¹ log (1/r) ∫_{B(0,1)} f` (`killedPotential_ball_one_sub_le`).

Combined with the maximal inequality for the gap of two occupation functionals of the path killed at its exit from
`B(0, r)` (`mul_measure_exists_lt_abs_killedOccupationGapUpTo_le`), this bounds the probability that the occupation
functionals of two rates along Brownian motion from `0` killed on exiting the unit disc differ by more than `η` at
some time, in terms of the uniform distance `δ` of their potentials on `B(0, r)`, a bound `M` of these potentials, and
the masses of the rates on the unit disc (`measure_exists_lt_abs_killedOccupationGapUpTo_ball_one_le`): additive
functionals of killed Brownian motion with uniformly close potentials on an exhausting subdomain are uniformly close
(Fukushima–Oshima–Takeda (2011), §5.1, Lemma 5.1.2; Armitage–Gardiner, §4.3, for the Green function of a disc).
-/

set_option autoImplicit false

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess HarmonicBalls

/-! ### The part of the occupation functional between two exit times -/

section Nested

variable {D' D : Set ℂ}

/-- The rate `f(b_s)` at the times `τ_{D'}(b) ≤ s < τ_D(b)` (and `s > 0`) between the exit times of the path `b` from
`D'` and from `D`, and `0` at all other times. -/
noncomputable def killedRateBetween (D' D : Set ℂ) (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) (s : ℝ) : ℝ≥0∞ :=
  (killedTimes D b \ killedTimes D' b).indicator (fun s => f (b s.toNNReal)) s

/-- The occupation functional `∫_{τ_{D'}(b)}^{τ_D(b)} f(b_s) ds` between the exit times of the path `b` from `D'` and
from `D`. -/
noncomputable def killedOccupationBetween (D' D : Set ℂ) (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  ∫⁻ s, killedRateBetween D' D f b s

theorem killedTimes_mono (h : D' ⊆ D) (b : ContinuousPath ℂ) : killedTimes D' b ⊆ killedTimes D b :=
  fun _ hs => ⟨hs.1, hs.2.trans_le (ContinuousPath.exitTime_mono h b)⟩

/-- The killed rate on `D` is the killed rate on `D'` plus the rate between the exit times. -/
theorem killedRate_eq_add (h : D' ⊆ D) (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) (s : ℝ) :
    killedRate D f b s = killedRate D' f b s + killedRateBetween D' D f b s := by
  unfold killedRate killedRateBetween
  by_cases h1 : s ∈ killedTimes D' b
  · rw [indicator_of_mem h1, indicator_of_mem (killedTimes_mono h b h1),
      indicator_of_notMem (fun hs => hs.2 h1), add_zero]
  · rw [indicator_of_notMem h1, zero_add]
    by_cases h2 : s ∈ killedTimes D b
    · rw [indicator_of_mem h2, indicator_of_mem (show s ∈ killedTimes D b \ killedTimes D' b from ⟨h2, h1⟩)]
    · rw [indicator_of_notMem h2, indicator_of_notMem (fun hs => h2 hs.1)]

/-- The occupation functional on `D` is the occupation functional on `D'` plus the part between the exit times. -/
theorem killedOccupation_eq_add (hD' : IsOpen D') (h : D' ⊆ D) {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    (b : ContinuousPath ℂ) :
    killedOccupation D f b = killedOccupation D' f b + killedOccupationBetween D' D f b := by
  unfold killedOccupation killedOccupationBetween
  have hfun : killedRate D f b = fun s => killedRate D' f b s + killedRateBetween D' D f b s :=
    funext (killedRate_eq_add h f b)
  rw [hfun]
  exact lintegral_add_left (measurable_killedRate_path hD' hf b) _

/-- The occupation functional up to a time is monotone in the domain. -/
theorem killedOccupationUpTo_mono (h : D' ⊆ D) (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) (t : ℝ) :
    killedOccupationUpTo D' f b t ≤ killedOccupationUpTo D f b t := by
  unfold killedOccupationUpTo
  refine lintegral_mono fun s => ?_
  by_cases hs : s ∈ Iic t
  · rw [indicator_of_mem hs, indicator_of_mem hs, killedRate_eq_add h f b]
    exact le_self_add
  · rw [indicator_of_notMem hs, indicator_of_notMem hs]

/-- Up to any time, the occupation functional on `D` exceeds the one on `D'` by at most the part between the exit
times. -/
theorem killedOccupationUpTo_le_add (hD' : IsOpen D') (h : D' ⊆ D) {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    (b : ContinuousPath ℂ) (t : ℝ) :
    killedOccupationUpTo D f b t ≤ killedOccupationUpTo D' f b t + killedOccupationBetween D' D f b := by
  unfold killedOccupationUpTo killedOccupationBetween
  have hpt : ∀ s, (Iic t).indicator (killedRate D f b) s ≤
      (Iic t).indicator (killedRate D' f b) s + killedRateBetween D' D f b s := by
    intro s
    by_cases hs : s ∈ Iic t
    · rw [indicator_of_mem hs, indicator_of_mem hs, killedRate_eq_add h f b]
    · rw [indicator_of_notMem hs, indicator_of_notMem hs, zero_add]
      exact zero_le
  calc ∫⁻ s, (Iic t).indicator (killedRate D f b) s
      ≤ ∫⁻ s, ((Iic t).indicator (killedRate D' f b) s + killedRateBetween D' D f b s) := lintegral_mono hpt
    _ = _ := lintegral_add_left ((measurable_killedRate_path hD' hf b).indicator measurableSet_Iic) _

/-- **The gap on `D` against the gap on `D'`.** When both occupation functionals on `D` are finite, at every time the
gap `A^f_t - A^g_t` of the path killed on exiting `D` differs from that of the path killed on exiting `D'` by at most
the parts of the two occupation functionals between the exit times. -/
theorem abs_killedOccupationGapUpTo_le (hD' : IsOpen D') (h : D' ⊆ D) {f g : ℂ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) {b : ContinuousPath ℂ} (hfb : killedOccupation D f b ≠ ⊤)
    (hgb : killedOccupation D g b ≠ ⊤) (t : ℝ) :
    |killedOccupationGapUpTo D f g b t| ≤ |killedOccupationGapUpTo D' f g b t| +
      (killedOccupationBetween D' D f b).toReal + (killedOccupationBetween D' D g b).toReal := by
  have key : ∀ k : ℂ → ℝ≥0∞, Measurable k → killedOccupation D k b ≠ ⊤ →
      (killedOccupationUpTo D' k b t).toReal ≤ (killedOccupationUpTo D k b t).toReal ∧
      (killedOccupationUpTo D k b t).toReal ≤
        (killedOccupationUpTo D' k b t).toReal + (killedOccupationBetween D' D k b).toReal := by
    intro k hk hkb
    have h1 : killedOccupationUpTo D k b t ≠ ⊤ :=
      ne_top_of_le_ne_top hkb (killedOccupationUpTo_le_killedOccupation k b t)
    have hB : killedOccupationBetween D' D k b ≠ ⊤ := by
      rw [killedOccupation_eq_add hD' h hk b] at hkb
      exact (ENNReal.add_ne_top.1 hkb).2
    have hmono := killedOccupationUpTo_mono h k b t
    have h2 : killedOccupationUpTo D' k b t ≠ ⊤ := ne_top_of_le_ne_top h1 hmono
    refine ⟨ENNReal.toReal_mono h1 hmono, ?_⟩
    rw [← ENNReal.toReal_add h2 hB]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h2, hB⟩) (killedOccupationUpTo_le_add hD' h hk b t)
  obtain ⟨hf1, hf2⟩ := key f hf hfb
  obtain ⟨hg1, hg2⟩ := key g hg hgb
  have hB1 := ENNReal.toReal_nonneg (a := killedOccupationBetween D' D f b)
  have hB2 := ENNReal.toReal_nonneg (a := killedOccupationBetween D' D g b)
  have hy1 := le_abs_self ((killedOccupationUpTo D' f b t).toReal - (killedOccupationUpTo D' g b t).toReal)
  have hy2 := neg_abs_le ((killedOccupationUpTo D' f b t).toReal - (killedOccupationUpTo D' g b t).toReal)
  unfold killedOccupationGapUpTo
  rw [abs_le]
  constructor <;> linarith

/-- **Splitting a large gap.** If the occupation functionals on `D'` are finite and the gap on `D` exceeds `η` at some
time, then the gap on `D'` exceeds `η / 3` at some time, or one of the two parts between the exit times exceeds
`η / 3`. -/
theorem exists_lt_abs_killedOccupationGapUpTo_or (hD' : IsOpen D') (h : D' ⊆ D) {f g : ℂ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {b : ContinuousPath ℂ} (hfb : killedOccupation D' f b ≠ ⊤)
    (hgb : killedOccupation D' g b ≠ ⊤) {η : ℝ} (hη : 0 < η)
    (hb : ∃ t : ℝ, η < |killedOccupationGapUpTo D f g b t|) :
    (∃ t : ℝ, η / 3 < |killedOccupationGapUpTo D' f g b t|) ∨
      ENNReal.ofReal (η / 3) < killedOccupationBetween D' D f b ∨
      ENNReal.ofReal (η / 3) < killedOccupationBetween D' D g b := by
  obtain ⟨t, ht⟩ := hb
  by_cases h1 : ENNReal.ofReal (η / 3) < killedOccupationBetween D' D f b
  · exact Or.inr (Or.inl h1)
  by_cases h2 : ENNReal.ofReal (η / 3) < killedOccupationBetween D' D g b
  · exact Or.inr (Or.inr h2)
  refine Or.inl ⟨t, ?_⟩
  rw [not_lt] at h1 h2
  have hBf : killedOccupationBetween D' D f b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have hBg : killedOccupationBetween D' D g b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
  have hfD : killedOccupation D f b ≠ ⊤ := by
    rw [killedOccupation_eq_add hD' h hf b]
    exact ENNReal.add_ne_top.2 ⟨hfb, hBf⟩
  have hgD : killedOccupation D g b ≠ ⊤ := by
    rw [killedOccupation_eq_add hD' h hg b]
    exact ENNReal.add_ne_top.2 ⟨hgb, hBg⟩
  have hle := abs_killedOccupationGapUpTo_le hD' h hf hg hfD hgD t
  have hη3 : 0 ≤ η / 3 := by positivity
  have hf3 : (killedOccupationBetween D' D f b).toReal ≤ η / 3 := ENNReal.toReal_le_of_le_ofReal hη3 h1
  have hg3 : (killedOccupationBetween D' D g b).toReal ≤ η / 3 := ENNReal.toReal_le_of_le_ofReal hη3 h2
  by_contra hc
  rw [not_lt] at hc
  linarith

/-- **Expectation of the part between the exit times**: the difference of the potentials. -/
theorem lintegral_killedOccupationBetween (hD' : IsOpen D') (h : D' ⊆ D) {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    (w : ℂ) (hfin : killedPotential D' f w ≠ ⊤) :
    ∫⁻ b, killedOccupationBetween D' D f b ∂planarBrownianMotion w =
      killedPotential D f w - killedPotential D' f w := by
  have hsum : killedPotential D f w =
      killedPotential D' f w + ∫⁻ b, killedOccupationBetween D' D f b ∂planarBrownianMotion w := by
    unfold killedPotential
    have hfun : killedOccupation D f =
        fun b => killedOccupation D' f b + killedOccupationBetween D' D f b :=
      funext (killedOccupation_eq_add hD' h hf)
    rw [hfun]
    exact lintegral_add_left (measurable_killedOccupation hD' hf) _
  rw [hsum, ENNReal.add_sub_cancel_left hfin]

theorem aemeasurable_killedOccupationBetween (hD' : IsOpen D') (hD : IsOpen D) (h : D' ⊆ D) {f : ℂ → ℝ≥0∞}
    (hf : Measurable f) (w : ℂ) (hfin : killedPotential D' f w ≠ ⊤) :
    AEMeasurable (killedOccupationBetween D' D f) (planarBrownianMotion w) := by
  refine ((measurable_killedOccupation hD hf).sub (measurable_killedOccupation hD' hf)).aemeasurable.congr ?_
  filter_upwards [ae_lt_top (measurable_killedOccupation hD' hf) hfin] with b hb
  show killedOccupation D f b - killedOccupation D' f b = killedOccupationBetween D' D f b
  rw [killedOccupation_eq_add hD' h hf b, ENNReal.add_sub_cancel_left hb.ne]

end Nested

/-! ### Nested discs -/

/-- The Green function of the disc `B(0, R)` with pole at the centre: `G_{B_R}(0, y) = (2π)⁻¹ log (R / |y|)`. -/
theorem greenBall_zero_left {R : ℝ} (hR : 0 < R) (y : ℂ) :
    greenBall R 0 y = (2 * Real.pi)⁻¹ * Real.log (R / ‖y‖) := by
  have h1 : ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) 0 * y‖ = R ^ 2 := by
    rw [map_zero, zero_mul, sub_zero, norm_pow, Complex.norm_of_nonneg hR.le]
  rw [greenBall, h1, zero_sub, norm_neg, sq, mul_div_mul_left _ _ hR.ne']

/-- **Comparison of the Green functions of nested discs at the centre**:
`2 G_{B_1}(0, y) ≤ 2 G_{B_r}(0, y) + π⁻¹ log (1/r) 1_{B_1}(y)` for `0 < r ≤ 1`. -/
theorem ofReal_two_mul_greenFunction_ball_one_le {r : ℝ} (hr : 0 < r) (y : ℂ) :
    ENNReal.ofReal (2 * greenFunction (ball 0 1) 0 y) ≤
      ENNReal.ofReal (2 * greenFunction (ball 0 r) 0 y) +
        (ball (0 : ℂ) 1).indicator (fun _ => ENNReal.ofReal (Real.pi⁻¹ * Real.log r⁻¹)) y := by
  by_cases hy1 : y ∈ ball (0 : ℂ) 1
  swap
  · rw [greenFunction_of_notMem_right hy1, mul_zero, ENNReal.ofReal_zero]
    exact zero_le
  by_cases hy0 : y = 0
  · rw [hy0, greenFunction_self, mul_zero, ENNReal.ofReal_zero]
    exact zero_le
  rw [indicator_of_mem hy1]
  refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  have hy : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hG1 : greenFunction (ball 0 1) 0 y = (2 * Real.pi)⁻¹ * (-Real.log ‖y‖) := by
    rw [greenFunction_ball (mem_ball_self one_pos) hy1 (Ne.symm hy0), greenBall_zero_left one_pos, one_div,
      Real.log_inv]
  rw [hG1, Real.log_inv]
  rcases lt_or_ge ‖y‖ r with hlt | hge
  · have hyr : y ∈ ball (0 : ℂ) r := mem_ball_zero_iff.2 hlt
    rw [greenFunction_ball (mem_ball_self hr) hyr (Ne.symm hy0), greenBall_zero_left hr,
      Real.log_div hr.ne' hy.ne']
    exact le_of_eq (by ring)
  · rw [greenFunction_ball_of_le_norm hge, mul_zero, zero_add]
    have hlog : Real.log r ≤ Real.log ‖y‖ := Real.log_le_log hr hge
    have hpi : 0 < Real.pi⁻¹ := inv_pos.2 Real.pi_pos
    have h2 : 2 * ((2 * Real.pi)⁻¹ * -Real.log ‖y‖) = Real.pi⁻¹ * -Real.log ‖y‖ := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left (neg_le_neg hlog) hpi.le

/-- **The potential collected between the exits from `B(0, r)` and `B(0, 1)`**, from the centre:
`u^{B(0,1)}_f(0) - u^{B(0,r)}_f(0) ≤ π⁻¹ log (1/r) ∫_{B(0,1)} f`. -/
theorem killedPotential_ball_one_sub_le {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    killedPotential (ball 0 1) f 0 - killedPotential (ball 0 r) f 0 ≤
      ENNReal.ofReal (Real.pi⁻¹ * Real.log r⁻¹) * ∫⁻ y in ball (0 : ℂ) 1, f y := by
  rw [killedPotential_ball_eq_lintegral_greenFunction one_pos hf,
    killedPotential_ball_eq_lintegral_greenFunction hr hf, tsub_le_iff_left]
  have hpt : ∀ y, ENNReal.ofReal (2 * greenFunction (ball 0 1) 0 y) * f y ≤
      ENNReal.ofReal (2 * greenFunction (ball 0 r) 0 y) * f y +
        ENNReal.ofReal (Real.pi⁻¹ * Real.log r⁻¹) * (ball (0 : ℂ) 1).indicator f y := by
    intro y
    have h := ofReal_two_mul_greenFunction_ball_one_le hr y
    by_cases hy1 : y ∈ ball (0 : ℂ) 1
    · rw [indicator_of_mem hy1] at h ⊢
      calc ENNReal.ofReal (2 * greenFunction (ball 0 1) 0 y) * f y
          ≤ (ENNReal.ofReal (2 * greenFunction (ball 0 r) 0 y) +
              ENNReal.ofReal (Real.pi⁻¹ * Real.log r⁻¹)) * f y := by gcongr
        _ = _ := add_mul _ _ _
    · rw [indicator_of_notMem hy1, add_zero] at h
      rw [indicator_of_notMem hy1, mul_zero, add_zero]
      gcongr
  have hm := hf.indicator (measurableSet_ball (x := (0 : ℂ)) (ε := 1))
  calc ∫⁻ y, ENNReal.ofReal (2 * greenFunction (ball 0 1) 0 y) * f y
      ≤ ∫⁻ y, (ENNReal.ofReal (2 * greenFunction (ball 0 r) 0 y) * f y +
          ENNReal.ofReal (Real.pi⁻¹ * Real.log r⁻¹) * (ball (0 : ℂ) 1).indicator f y) := lintegral_mono hpt
    _ = _ := by
      rw [lintegral_add_right _ (hm.const_mul _), lintegral_const_mul _ hm,
        lintegral_indicator measurableSet_ball]

/-- `ofReal x * P ≤ K` with `x > 0` gives `P ≤ ofReal x⁻¹ * K`. -/
theorem le_ofReal_inv_mul_of_ofReal_mul_le {x : ℝ} (hx : 0 < x) {P K : ℝ≥0∞}
    (h : ENNReal.ofReal x * P ≤ K) : P ≤ ENNReal.ofReal x⁻¹ * K := by
  calc P = ENNReal.ofReal x⁻¹ * (ENNReal.ofReal x * P) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hx.le), inv_mul_cancel₀ hx.ne', ENNReal.ofReal_one,
          one_mul]
    _ ≤ ENNReal.ofReal x⁻¹ * K := by gcongr

/-- **Occupation functionals with close potentials are uniformly close (unit disc).** Let `f, g` be Borel rates,
`0 < r ≤ 1`, and let the potentials of `f` and `g` for Brownian motion killed on exiting `B(0, r)` be bounded by
`M < ∞` and `δ`-close on `B(0, r)`. Then for Brownian motion from `0` killed on exiting the unit disc, the
probability that the occupation functionals of `f` and `g` differ by more than `η` at some time is at most
`(9/η²) 32 δ M + (3/η) π⁻¹ log (1/r) (∫_{B(0,1)} f + ∫_{B(0,1)} g)`. -/
theorem measure_exists_lt_abs_killedOccupationGapUpTo_ball_one_le {f g : ℂ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {M δ : ℝ≥0∞} (hM : M ≠ ⊤)
    (hMf : ∀ y ∈ ball (0 : ℂ) r, killedPotential (ball 0 r) f y ≤ M)
    (hMg : ∀ y ∈ ball (0 : ℂ) r, killedPotential (ball 0 r) g y ≤ M)
    (hfg : ∀ y ∈ ball (0 : ℂ) r, killedPotential (ball 0 r) f y ≤ killedPotential (ball 0 r) g y + δ)
    (hgf : ∀ y ∈ ball (0 : ℂ) r, killedPotential (ball 0 r) g y ≤ killedPotential (ball 0 r) f y + δ)
    {η : ℝ} (hη : 0 < η) :
    planarBrownianMotion 0 {b | ∃ t : ℝ, η < |killedOccupationGapUpTo (ball 0 1) f g b t|} ≤
      ENNReal.ofReal (9 / η ^ 2) * (32 * δ * M) +
        ENNReal.ofReal (3 / η) * (ENNReal.ofReal (Real.pi⁻¹ * Real.log r⁻¹) *
          ((∫⁻ y in ball (0 : ℂ) 1, f y) + ∫⁻ y in ball (0 : ℂ) 1, g y)) := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have hsub : ball (0 : ℂ) r ⊆ ball 0 1 := ball_subset_ball hr1
  have hη3 : 0 < η / 3 := by positivity
  have hfin_f : killedPotential (ball 0 r) f 0 ≠ ⊤ := ne_top_of_le_ne_top hM (hMf 0 h0)
  have hfin_g : killedPotential (ball 0 r) g 0 ≠ ⊤ := ne_top_of_le_ne_top hM (hMg 0 h0)
  have h1 := ae_lt_top (measurable_killedOccupation isOpen_ball hf) hfin_f
  have h2 := ae_lt_top (measurable_killedOccupation isOpen_ball hg) hfin_g
  set E₁ : Set (ContinuousPath ℂ) := {b | ∃ t : ℝ, η / 3 < |killedOccupationGapUpTo (ball 0 r) f g b t|}
  set E₂ : Set (ContinuousPath ℂ) :=
    {b | ENNReal.ofReal (η / 3) ≤ killedOccupationBetween (ball 0 r) (ball 0 1) f b}
  set E₃ : Set (ContinuousPath ℂ) :=
    {b | ENNReal.ofReal (η / 3) ≤ killedOccupationBetween (ball 0 r) (ball 0 1) g b}
  have hcover : {b | ∃ t : ℝ, η < |killedOccupationGapUpTo (ball 0 1) f g b t|} ≤ᵐ[planarBrownianMotion 0]
      (E₁ ∪ E₂ ∪ E₃ : Set (ContinuousPath ℂ)) := by
    filter_upwards [h1, h2] with b hb1 hb2 hb
    rcases exists_lt_abs_killedOccupationGapUpTo_or isOpen_ball hsub hf hg hb1.ne hb2.ne hη hb with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h.le)
    · exact Or.inr h.le
  have hb1 : planarBrownianMotion 0 E₁ ≤ ENNReal.ofReal (9 / η ^ 2) * (32 * δ * M) := by
    have hK := mul_measure_exists_lt_abs_killedOccupationGapUpTo_le isOpen_ball hf hg hM hMf hMg hfg hgf h0 hη3
    have hx : 0 < (η / 3) ^ 2 := by positivity
    have he : ((η / 3) ^ 2)⁻¹ = 9 / η ^ 2 := by
      rw [div_pow, inv_div]
      norm_num
    rw [← he]
    exact le_ofReal_inv_mul_of_ofReal_mul_le hx hK
  have htail : ∀ k : ℂ → ℝ≥0∞, Measurable k → killedPotential (ball 0 r) k 0 ≠ ⊤ →
      planarBrownianMotion 0 {b | ENNReal.ofReal (η / 3) ≤ killedOccupationBetween (ball 0 r) (ball 0 1) k b} ≤
        ENNReal.ofReal (3 / η) * (ENNReal.ofReal (Real.pi⁻¹ * Real.log r⁻¹) * ∫⁻ y in ball (0 : ℂ) 1, k y) := by
    intro k hk hfin
    have hMk := mul_meas_ge_le_lintegral₀
      (aemeasurable_killedOccupationBetween isOpen_ball isOpen_ball hsub hk 0 hfin) (ENNReal.ofReal (η / 3))
    rw [lintegral_killedOccupationBetween isOpen_ball hsub hk 0 hfin] at hMk
    have he : (η / 3)⁻¹ = 3 / η := inv_div η 3
    rw [← he]
    exact le_ofReal_inv_mul_of_ofReal_mul_le hη3 (hMk.trans (killedPotential_ball_one_sub_le hr hk))
  calc planarBrownianMotion 0 {b | ∃ t : ℝ, η < |killedOccupationGapUpTo (ball 0 1) f g b t|}
      ≤ planarBrownianMotion 0 (E₁ ∪ E₂ ∪ E₃) := measure_mono_ae hcover
    _ ≤ planarBrownianMotion 0 E₁ + planarBrownianMotion 0 E₂ + planarBrownianMotion 0 E₃ :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (9 / η ^ 2) * (32 * δ * M) +
          ENNReal.ofReal (3 / η) * (ENNReal.ofReal (Real.pi⁻¹ * Real.log r⁻¹) * ∫⁻ y in ball (0 : ℂ) 1, f y) +
          ENNReal.ofReal (3 / η) * (ENNReal.ofReal (Real.pi⁻¹ * Real.log r⁻¹) * ∫⁻ y in ball (0 : ℂ) 1, g y) :=
        add_le_add (add_le_add hb1 (htail f hf hfin_f)) (htail g hg hfin_g)
    _ = _ := by rw [mul_add, mul_add, add_assoc]

end MatedCRT
