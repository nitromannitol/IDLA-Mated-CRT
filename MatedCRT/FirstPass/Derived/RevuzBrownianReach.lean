import MatedCRT.FirstPass.Derived.RevuzPositive
import MatedCRT.FirstPass.LPBridge.PlanarBrownianSpace
import LatticeProb.Prob.BrownianMax

/-!
# Planar Brownian motion reaches a fixed disc from few starting points

For planar Brownian motion `P_z` (generator `Δ / 2`) and a radius `n ≥ 0`, the probability that
the path visits the closed disc `{‖y‖ ≤ n}` before time `1` has a Gaussian tail in the starting
point `z`:

`P_z(∃ s ≤ 1, ‖B_s‖ ≤ n) ≤ 8 exp(n² / 128) exp(-‖z‖² / 256)`,

so it is Lebesgue integrable in `z`: `∫ dz P_z(∃ s ≤ 1, ‖B_s‖ ≤ n) < ∞`.

The tail comes from the maximal inequality for real Brownian motion
`P(∃ s ≤ T, a ≤ |X_s - X_0|) ≤ 4 exp(-a² / (32 T))` (`LatticeProb.measure_exists_abs_sub_ge_le`),
applied to the real and imaginary parts of the planar path, which are real Brownian motions.

This is the integrability statement used to show that the Revuz measure of a positive continuous
additive functional of planar Brownian motion with respect to Lebesgue measure is `σ`-finite: the
sets `{y | ‖y‖ ≤ n, P_y(A_1 ≤ n) ≥ 1/n}` have finite Revuz measure.
-/

open MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT

/-- The real part of the planar path, recentred at its start, has the maximal tail of real
Brownian motion on `[0, 1]`. -/
theorem planarLaw_exists_abs_re_sub_ge_le (z : ℂ) {a : ℝ} (ha : 0 < a) :
    planarLaw z {ω | ∃ s : ℝ≥0, s ≤ 1 ∧ a ≤ |(ω s).re - (ω 0).re|}
      ≤ 4 * ENNReal.ofReal (Real.exp (-(a ^ 2 / 32))) := by
  have : IsProbabilityMeasure (planarLaw z) := by unfold planarLaw; infer_instance
  have hB : ProbabilityTheory.IsBrownianReal (fun t (ω : ContinuousPath ℂ) => (HarmonicBalls.reImPath ω).1 t - z.re)
      (planarLaw z) :=
    PlanarBrownianSpace.isBrownianReal_comp_hasLaw
      (PlanarBrownianSpace.isBrownianReal_brownianMotion_sub z.re) (PlanarBrownianSpace.hasLaw_re z)
  have hm : ∀ t, Measurable fun ω : ContinuousPath ℂ => (HarmonicBalls.reImPath ω).1 t - z.re := by
    intro t
    simp only [HarmonicBalls.reImPath_fst_apply]
    exact (Complex.measurable_re.comp (PlanarBrownianSpace.measurable_eval_path t)).sub_const _
  have h := LatticeProb.measure_exists_abs_sub_ge_le hB hm 1 ha
  simpa only [HarmonicBalls.reImPath_fst_apply, sub_sub_sub_cancel_right, NNReal.coe_one,
    mul_one] using h

/-- The imaginary part of the planar path, recentred at its start, has the maximal tail of real
Brownian motion on `[0, 1]`. -/
theorem planarLaw_exists_abs_im_sub_ge_le (z : ℂ) {a : ℝ} (ha : 0 < a) :
    planarLaw z {ω | ∃ s : ℝ≥0, s ≤ 1 ∧ a ≤ |(ω s).im - (ω 0).im|}
      ≤ 4 * ENNReal.ofReal (Real.exp (-(a ^ 2 / 32))) := by
  have : IsProbabilityMeasure (planarLaw z) := by unfold planarLaw; infer_instance
  have hB : ProbabilityTheory.IsBrownianReal (fun t (ω : ContinuousPath ℂ) => (HarmonicBalls.reImPath ω).2 t - z.im)
      (planarLaw z) :=
    PlanarBrownianSpace.isBrownianReal_comp_hasLaw
      (PlanarBrownianSpace.isBrownianReal_brownianMotion_sub z.im) (PlanarBrownianSpace.hasLaw_im z)
  have hm : ∀ t, Measurable fun ω : ContinuousPath ℂ => (HarmonicBalls.reImPath ω).2 t - z.im := by
    intro t
    simp only [HarmonicBalls.reImPath_snd_apply]
    exact (Complex.measurable_im.comp (PlanarBrownianSpace.measurable_eval_path t)).sub_const _
  have h := LatticeProb.measure_exists_abs_sub_ge_le hB hm 1 ha
  simpa only [HarmonicBalls.reImPath_snd_apply, sub_sub_sub_cancel_right, NNReal.coe_one,
    mul_one] using h

/-- Elementary comparison `(x - n)² ≥ x² / 2 - n²`, used to turn the tail in `‖z‖ - n` into a
Gaussian in `‖z‖`. -/
private lemma half_sq_sub_sq_le_sq_sub (x n : ℝ) : x ^ 2 / 2 - n ^ 2 ≤ (x - n) ^ 2 := by
  nlinarith [sq_nonneg (x - 2 * n)]

/-- **Gaussian tail of the probability of reaching a disc before time `1`.**  For every `n`,
`P_z(∃ s ≤ 1, ‖B_s‖ ≤ n) ≤ 8 exp(n² / 128) exp(-‖z‖² / 256)`. -/
theorem planarLaw_exists_norm_le_le (n : ℝ) (z : ℂ) :
    planarLaw z {ω | ∃ s : ℝ≥0, s ≤ 1 ∧ ‖ω s‖ ≤ n}
      ≤ ENNReal.ofReal (8 * Real.exp (n ^ 2 / 128) * Real.exp (-(‖z‖ ^ 2 / 256))) := by
  have : IsProbabilityMeasure (planarLaw z) := by unfold planarLaw; infer_instance
  rcases le_or_gt ‖z‖ n with hz | hz
  · -- Near the disc the right-hand side is at least `1`.
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsq : ‖z‖ ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
    have h1 : 1 ≤ Real.exp (n ^ 2 / 128) * Real.exp (-(‖z‖ ^ 2 / 256)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [sq_nonneg n])
    nlinarith [Real.exp_pos (n ^ 2 / 128), Real.exp_pos (-(‖z‖ ^ 2 / 256))]
  · set a : ℝ := (‖z‖ - n) / 2 with ha_def
    have ha : 0 < a := by rw [ha_def]; linarith
    -- Almost surely the path starts at `z`, so reaching the disc forces a large coordinate increment.
    have hsub : {ω : ContinuousPath ℂ | ∃ s : ℝ≥0, s ≤ 1 ∧ ‖ω s‖ ≤ n} ≤ᵐ[planarLaw z]
        ({ω | ∃ s : ℝ≥0, s ≤ 1 ∧ a ≤ |(ω s).re - (ω 0).re|} ∪
          {ω | ∃ s : ℝ≥0, s ≤ 1 ∧ a ≤ |(ω s).im - (ω 0).im|} : Set (ContinuousPath ℂ)) := by
      filter_upwards [ae_planarLaw_eval_zero z] with ω hω0
      rintro ⟨s, hs1, hsn⟩
      have hre_im := Complex.norm_le_abs_re_add_abs_im (ω s - z)
      have htri : ‖z‖ ≤ ‖ω s‖ + ‖ω s - z‖ := by
        have := norm_sub_le (ω s) (ω s - z)
        simpa using this
      rw [Complex.sub_re, Complex.sub_im] at hre_im
      by_cases hre : a ≤ |(ω s).re - z.re|
      · exact Or.inl ⟨s, hs1, by rw [hω0]; exact hre⟩
      · refine Or.inr ⟨s, hs1, ?_⟩
        rw [hω0]
        have hre' := not_le.1 hre
        linarith
    have hexp : Real.exp (-(a ^ 2 / 32))
        ≤ Real.exp (n ^ 2 / 128) * Real.exp (-(‖z‖ ^ 2 / 256)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := half_sq_sub_sq_le_sq_sub ‖z‖ n
      rw [ha_def]
      nlinarith
    calc planarLaw z {ω | ∃ s : ℝ≥0, s ≤ 1 ∧ ‖ω s‖ ≤ n}
        ≤ planarLaw z ({ω | ∃ s : ℝ≥0, s ≤ 1 ∧ a ≤ |(ω s).re - (ω 0).re|} ∪
            {ω | ∃ s : ℝ≥0, s ≤ 1 ∧ a ≤ |(ω s).im - (ω 0).im|}) := measure_mono_ae hsub
      _ ≤ 4 * ENNReal.ofReal (Real.exp (-(a ^ 2 / 32)))
            + 4 * ENNReal.ofReal (Real.exp (-(a ^ 2 / 32))) :=
          (measure_union_le _ _).trans
            (add_le_add (planarLaw_exists_abs_re_sub_ge_le z ha)
              (planarLaw_exists_abs_im_sub_ge_le z ha))
      _ = ENNReal.ofReal (8 * Real.exp (-(a ^ 2 / 32))) := by
          rw [← add_mul, ENNReal.ofReal_mul (by norm_num)]
          norm_num
      _ ≤ ENNReal.ofReal (8 * Real.exp (n ^ 2 / 128) * Real.exp (-(‖z‖ ^ 2 / 256))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hexp (by norm_num)

/-- The Gaussian `z ↦ exp(-‖z‖² / 256)` is Lebesgue integrable on `ℂ`. -/
private lemma integrable_exp_neg_sq_norm_div : Integrable fun z : ℂ => Real.exp (-(‖z‖ ^ 2 / 256)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (1 / 256 : ℂ))
    (by norm_num) 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  rw [show (-(1 / 256 : ℂ)) * (‖z‖ : ℂ) ^ 2 = ((-(‖z‖ ^ 2 / 256) : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

/-- **Planar Brownian motion reaches a fixed disc before time `1` from a Lebesgue-integrable set of
starting points:** `∫ dz P_z(∃ s ≤ 1, ‖B_s‖ ≤ n) < ∞` for every `n`. -/
theorem lintegral_planarLaw_exists_norm_le_lt_top (n : ℝ) :
    ∫⁻ z, planarLaw z {ω | ∃ s : ℝ≥0, s ≤ 1 ∧ ‖ω s‖ ≤ n} < ∞ := by
  calc ∫⁻ z, planarLaw z {ω | ∃ s : ℝ≥0, s ≤ 1 ∧ ‖ω s‖ ≤ n}
      ≤ ∫⁻ z, ENNReal.ofReal (8 * Real.exp (n ^ 2 / 128) * Real.exp (-(‖z‖ ^ 2 / 256))) :=
        lintegral_mono fun z => planarLaw_exists_norm_le_le n z
    _ < ∞ := (integrable_exp_neg_sq_norm_div.const_mul (8 * Real.exp (n ^ 2 / 128))).lintegral_lt_top

end MatedCRT
