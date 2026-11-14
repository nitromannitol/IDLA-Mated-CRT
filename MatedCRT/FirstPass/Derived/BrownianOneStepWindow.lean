import HarmonicBalls.Proofs.Sec6.BrownianScaling
import LatticeProb.Bonanno.MatedCRTHarmonic.Brownian.OneStep

/-!
# The one-step window of planar Brownian motion

The first two steps of the tube (support-theorem) argument for planar Brownian motion, used for
the Brownian disconnection estimate in the proof of the invariance principle of
Gwynne-Miller-Sheffield (Lemma 3.14 of arXiv:1807.07515).

* `oneStepConst_smul`: the one-step constant `oneStepConst ε Δ` of the real one-step window is
  invariant under Brownian scaling `(ε, Δ) ↦ (c ε, c² Δ)`.
* `ofReal_oneStepConst_le_brownianMotion`: real Brownian motion started from `y` stays within
  `3ε/4` of `y` up to time `Δ` and ends within `ε/16` of `y + a`, `|a| ≤ ε/8`, with probability at
  least `oneStepConst ε Δ`.
* `ofReal_oneStepConst_sq_le_planarBrownianMotion`: the planar window, from the independence of
  the real and imaginary parts of planar Brownian motion; the probability is at least
  `oneStepConst ε Δ ^ 2`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 MatedCRTHarmonic.Brownian

namespace MatedCRT

/-- **Brownian scaling of the one-step constant.** For `c > 0`,
`oneStepConst (c ε) (c² Δ) = oneStepConst ε Δ`. -/
theorem oneStepConst_smul {c : ℝ≥0} (hc : c ≠ 0) (ε : ℝ) (Δ : ℝ≥0) :
    oneStepConst ((c : ℝ) * ε) (c ^ 2 * Δ) = oneStepConst ε Δ := by
  have hc' : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  have hc2 : (c : ℝ) ^ 2 ≠ 0 := by positivity
  have hsqrt : Real.sqrt (2 * Real.pi * ((c : ℝ) ^ 2 * Δ)) =
      c * Real.sqrt (2 * Real.pi * Δ) := by
    rw [show 2 * Real.pi * ((c : ℝ) ^ 2 * Δ) = (c : ℝ) ^ 2 * (2 * Real.pi * Δ) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc'.le]
  have he1 : -(3 * ((c : ℝ) * ε) / 16 - 0) ^ 2 / (2 * ((c : ℝ) ^ 2 * Δ)) =
      -(3 * ε / 16 - 0) ^ 2 / (2 * Δ) := by
    rw [show -(3 * ((c : ℝ) * ε) / 16 - 0) ^ 2 = (c : ℝ) ^ 2 * (-(3 * ε / 16 - 0) ^ 2) by ring,
      show 2 * ((c : ℝ) ^ 2 * Δ) = (c : ℝ) ^ 2 * (2 * Δ) by ring, mul_div_mul_left _ _ hc2]
  have he2 : -((c : ℝ) * ε / 2) ^ 2 / (2 * ((c : ℝ) ^ 2 * Δ)) = -(ε / 2) ^ 2 / (2 * Δ) := by
    rw [show -((c : ℝ) * ε / 2) ^ 2 = (c : ℝ) ^ 2 * (-(ε / 2) ^ 2) by ring,
      show 2 * ((c : ℝ) ^ 2 * Δ) = (c : ℝ) ^ 2 * (2 * Δ) by ring, mul_div_mul_left _ _ hc2]
  unfold oneStepConst gaussianPDFReal
  push_cast
  rw [hsqrt, he1, he2]
  have hcc : (c : ℝ) * (c : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hc'.ne'
  linear_combination (2 * (ε / 16) * (Real.sqrt (2 * Real.pi * Δ))⁻¹ *
    Real.exp (-(3 * ε / 16 - 0) ^ 2 / (2 * Δ))) * hcc

/-- **One-step window of real Brownian motion.** Real Brownian motion started from `y` stays
within `3ε/4` of `y` up to time `Δ` and ends within `ε/16` of `y + a`, `|a| ≤ ε/8`, with
probability at least `oneStepConst ε Δ`. -/
theorem ofReal_oneStepConst_le_brownianMotion (y : ℝ) {ε : ℝ} (hε : 0 < ε) {Δ : ℝ≥0}
    (hΔ : 0 < Δ) {a : ℝ} (ha : |a| ≤ ε / 8) :
    ENNReal.ofReal (oneStepConst ε Δ) ≤
      brownianMotion y
        {p : ContinuousPath ℝ | (∀ t ≤ Δ, |p t - y| < 3 * ε / 4) ∧ |p Δ - y - a| < ε / 16} := by
  have h0 := ae_brownianMotion_eval_zero y
  have hB : IsPreBrownianReal (fun (t : ℝ≥0) (p : ContinuousPath ℝ) => p t - p 0)
      (brownianMotion y) :=
    (isPreBrownianReal_brownianMotion y).congr fun t => by
      filter_upwards [h0] with p hp
      simp only [hp]
  have hm : ∀ t : ℝ≥0, Measurable (fun p : ContinuousPath ℝ => p t - p 0) := fun t =>
    ((continuous_eval_const t).sub (continuous_eval_const 0)).measurable
  calc ENNReal.ofReal (oneStepConst ε Δ)
      ≤ brownianMotion y {p : ContinuousPath ℝ |
          (∀ t ≤ Δ, |p t - p 0| < 3 * ε / 4) ∧ |p Δ - p 0 - a| < ε / 16} :=
        oneStepConst_le_measure hB hm (fun p => p.continuous.sub continuous_const)
          (fun p => sub_self _) hε hΔ ha
    _ ≤ _ := by
      refine measure_mono_ae ?_
      filter_upwards [h0] with p hp
      intro hmem
      simpa only [hp] using hmem

/-- **One-step window of planar Brownian motion.** Planar Brownian motion started from `x` stays
in the square of half-side `3ε/4` around `x` up to time `Δ` and ends in the square of half-side
`ε/16` around `x + a`, where `|Re a|, |Im a| ≤ ε/8`, with probability at least
`oneStepConst ε Δ ^ 2`. -/
theorem ofReal_oneStepConst_sq_le_planarBrownianMotion (x : ℂ) {ε : ℝ} (hε : 0 < ε)
    {Δ : ℝ≥0} (hΔ : 0 < Δ) {a : ℂ} (hre : |a.re| ≤ ε / 8) (him : |a.im| ≤ ε / 8) :
    ENNReal.ofReal (oneStepConst ε Δ) ^ 2 ≤
      planarBrownianMotion x {ω | (∀ t ≤ Δ, |(ω t - x).re| < 3 * ε / 4 ∧
          |(ω t - x).im| < 3 * ε / 4) ∧
        |(ω Δ - x - a).re| < ε / 16 ∧ |(ω Δ - x - a).im| < ε / 16} := by
  set S₁ : Set (ContinuousPath ℝ) :=
    {p | (∀ t ≤ Δ, |p t - x.re| < 3 * ε / 4) ∧ |p Δ - x.re - a.re| < ε / 16} with hS₁
  set S₂ : Set (ContinuousPath ℝ) :=
    {p | (∀ t ≤ Δ, |p t - x.im| < 3 * ε / 4) ∧ |p Δ - x.im - a.im| < ε / 16} with hS₂
  have hsub : reImPath ⁻¹' (S₁ ×ˢ S₂) ⊆
      {ω | (∀ t ≤ Δ, |(ω t - x).re| < 3 * ε / 4 ∧ |(ω t - x).im| < 3 * ε / 4) ∧
        |(ω Δ - x - a).re| < ε / 16 ∧ |(ω Δ - x - a).im| < ε / 16} := by
    rintro ω ⟨⟨h1, h2⟩, h3, h4⟩
    simp only [reImPath_fst_apply, reImPath_snd_apply] at h1 h2 h3 h4
    refine ⟨fun t ht => ⟨?_, ?_⟩, ?_, ?_⟩
    · simpa only [Complex.sub_re] using h1 t ht
    · simpa only [Complex.sub_im] using h3 t ht
    · simpa only [Complex.sub_re] using h2
    · simpa only [Complex.sub_im] using h4
  calc ENNReal.ofReal (oneStepConst ε Δ) ^ 2
      = ENNReal.ofReal (oneStepConst ε Δ) * ENNReal.ofReal (oneStepConst ε Δ) := sq _
    _ ≤ brownianMotion x.re S₁ * brownianMotion x.im S₂ :=
        mul_le_mul' (ofReal_oneStepConst_le_brownianMotion x.re hε hΔ hre)
          (ofReal_oneStepConst_le_brownianMotion x.im hε hΔ him)
    _ = ((brownianMotion x.re).prod (brownianMotion x.im)) (S₁ ×ˢ S₂) :=
        (Measure.prod_prod _ _).symm
    _ = (planarBrownianMotion x).map reImPath (S₁ ×ˢ S₂) := by
        rw [planarBrownianMotion_map_reImPath]
    _ = planarBrownianMotion x (reImPath ⁻¹' (S₁ ×ˢ S₂)) := by
        let e : ContinuousPath ℂ ≃ᵐ ContinuousPath ℝ × ContinuousPath ℝ :=
          { toFun := reImPath
            invFun := complexPathOfReIm
            left_inv := complexPathOfReIm_reImPath
            right_inv := reImPath_complexPathOfReIm
            measurable_toFun := measurable_reImPath
            measurable_invFun := measurable_complexPathOfReIm }
        exact e.measurableEmbedding.map_apply _ _
    _ ≤ _ := measure_mono hsub

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.oneStepConst_smul
#print axioms MatedCRT.ofReal_oneStepConst_le_brownianMotion
#print axioms MatedCRT.ofReal_oneStepConst_sq_le_planarBrownianMotion
