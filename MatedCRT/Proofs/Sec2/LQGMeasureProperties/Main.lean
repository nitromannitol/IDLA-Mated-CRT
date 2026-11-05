import MatedCRT.Proofs.Sec2.LQGMeasureProperties.Locality

/-!
# Fact 2.2 from what is genuinely cited

The dilations `z ↦ 2ⁿ z` shift the dyadic sequence of scales `2⁻ᵏ` which defines `μ_h`, so Fact 2.2 IV for
dilations reduces to the dilations by `s ∈ (1, 2)` (`lqgMeasureDilationCovariancePart_of_nonDyadic`). Fact 2.2 then
follows (`lqgMeasureProperties_of_citedInputs`) from
* non-atomicity (`LQGMeasureNonAtomicPart`, cited: GMC, DS11),
* the locality of circle averages (`ConeCircleAverageLocalityStep`, a property of the field: DS11 Section 3.1),
* conformal covariance for the non-dyadic dilations (`LQGMeasureNonDyadicDilationPart`, cited: DS11 Proposition 2.1,
  SW16).

Why the non-dyadic dilations stay cited: `HarmonicBalls.IsLQGLimit` only asks for vague convergence along
`dyadicScale k = 2⁻ᵏ`, and `IsLQGMeasure` is this limit a.s.; nothing in the definition controls the approximations at
the scales `s 2⁻ᵏ`, `s ∈ (1, 2)`. Pathwise the densities `ε^{γ²/2} e^{γ h_ε(z)}` are not comparable between `2⁻ᵏ` and
`s 2⁻ᵏ` uniformly in `z` (`h_{e^{-t}}(z)` moves like a Brownian motion in `t`), and the law of the cone field is not
invariant under a deterministic dilation. The convergence along `s 2⁻ᵏ` to the same limit is a Gaussian multiplicative
chaos estimate (an `L¹` or, for `γ < √2`, an `L²` bound on the difference of the approximations at `ε` and `s ε`, from
the covariance of the circle averages: DS11 Proposition 2.1 for a fixed `s`), and all `s` at once is SW16.
Non-atomicity in the unit disk follows from the cited Lemma 2.7 (`ae_measure_singleton_eq_zero_of_volumeGrowth`,
`NonAtomic.lean`).
-/

namespace MatedCRT.LQGMeasure

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- Multiplying the scales by `2ⁿ` shifts the dyadic sequence. -/
theorem tendsto_dyadic_shift {F : ℝ → ℝ} {l : Filter ℝ} {t : ℝ} (n : ℤ)
    (h : Tendsto (fun k => F (t * dyadicScale k)) atTop l) :
    Tendsto (fun k => F (t * 2 ^ n * dyadicScale k)) atTop l := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [← tendsto_add_atTop_iff_nat m]
    refine Tendsto.congr (fun k => ?_) h
    have h2 : (2 : ℝ) ^ m * 2⁻¹ ^ m = 1 := by rw [← mul_pow]; norm_num
    simp only [dyadicScale, zpow_natCast, pow_add]
    rw [show t * 2 ^ m * (2⁻¹ ^ k * 2⁻¹ ^ m) = t * 2⁻¹ ^ k * (2 ^ m * 2⁻¹ ^ m) by ring, h2, mul_one]
  · refine Tendsto.congr (fun k => ?_) ((tendsto_add_atTop_iff_nat m).2 h)
    simp only [dyadicScale, zpow_neg, zpow_natCast, pow_add]
    rw [← inv_pow]
    ring_nf

/-- **Fact 2.2 IV for dilations** from the non-dyadic dilations `s ∈ (1, 2)` (cited) and the definition of `μ_h`. -/
theorem lqgMeasureDilationCovariancePart_of_nonDyadic (hND : LQGMeasureNonDyadicDilationPart) :
    LQGMeasureDilationCovariancePart := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hμ
  filter_upwards [hND γ hγ hγ2 Ω P hC hcirc μ hμ, ae_continuous_circle hμ.2.1, hμ.2.2] with ω hω hcont hlim s hs
  have := hlim.isLocallyFiniteMeasure
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have hns : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hconv : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun k => ∫ z, g z ∂lqgApprox γ (hcirc ω) (‖(s : ℂ)‖ * dyadicScale k)) atTop
        (𝓝 (∫ z, g z ∂μ ω)) := by
    intro g hg hgc
    rw [hns]
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hs (by norm_num : (1 : ℝ) < 2)
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = s / 2 ^ n := ⟨_, rfl⟩
    have h2n : (0 : ℝ) < 2 ^ n := zpow_pos (by norm_num) n
    have hst : t * 2 ^ n = s := by rw [ht, div_mul_cancel₀ _ h2n.ne']
    have ht1 : 1 ≤ t := by
      rw [ht, le_div_iff₀ h2n, one_mul]
      exact hn1
    have ht2 : t < 2 := by
      rw [ht, div_lt_iff₀ h2n]
      rwa [zpow_add_one₀ two_ne_zero, mul_comm] at hn2
    have key : Tendsto (fun k => ∫ z, g z ∂lqgApprox γ (hcirc ω) (t * dyadicScale k)) atTop
        (𝓝 (∫ z, g z ∂μ ω)) := by
      rcases ht1.eq_or_lt with h1 | h1
      · simp only [← h1, one_mul]
        exact hlim.tendsto_integral g hg hgc
      · exact tendsto_of_isLQGLimit_dilation hγ hcont (by linarith) (hω t h1 ht2) hg hgc
    have := tendsto_dyadic_shift (F := fun r => ∫ z, g z ∂lqgApprox γ (hcirc ω) r) n key
    simp only [hst] at this
    exact this
  have h' := isLQGLimit_affine_of_tendsto hγ hcont hs0 0 hconv
  simp only [hns, add_zero, sub_zero] at h'
  exact h'

/-- **Fact 2.2 from the cited inputs**: non-atomicity (I, cited), the locality of circle averages (field step for II)
and conformal covariance for the non-dyadic dilations `s ∈ (1, 2)` (IV, cited). Local finiteness (I), locality (II)
given the field step, Weyl scaling (III), and translations, rotations and dyadic dilations (IV) are proved from the
definition of the LQG measure as the vague limit along `2⁻ᵏ` of the circle average approximations. -/
theorem lqgMeasureProperties_of_citedInputs (hNA : LQGMeasureNonAtomicPart) (hCL : ConeCircleAverageLocalityStep)
    (hND : LQGMeasureNonDyadicDilationPart) : LQGMeasurePropertiesStmt :=
  lqgMeasureProperties_of_steps hNA hCL (lqgMeasureDilationCovariancePart_of_nonDyadic hND)

end MatedCRT.LQGMeasure
