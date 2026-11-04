import MatedCRT.Proofs.Sec2.LQGMeasureProperties.Approx

/-!
# Fact 2.2 IV (conformal covariance for complex affine maps) from the dilation case

For `φ(z) = a z + w` the circle averages of `h ∘ φ + Q log |a|` are `(r, z) ↦ h_{|a| r}(a z + w) + Q log |a|`. By the
Lebesgue change of variables `x = a z + w` (`dz = |a|⁻² dx`) and `γ Q = 2 + γ²/2`, the circle average approximation of
`h ∘ φ + Q log |a|` at scale `ε` is the image under `φ⁻¹` of the approximation of `h` at scale `|a| ε`
(`integral_lqgApprox_affine`). Hence Fact 2.2 IV for `φ` says exactly that the approximations of `h` converge vaguely
to `μ_h` along `|a| 2⁻ᵏ` (`isLQGLimit_affine_iff`): translations and rotations come for free, and only the modulus `|a|`
matters. The dilation case (`LQGMeasureDilationCovariancePart`, cited: DS11 Proposition 2.1, SW16) gives every `|a|`.
-/

namespace MatedCRT.LQGMeasure

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The inverse `x ↦ a⁻¹ (x - w)` of the complex affine map `z ↦ a z + w`, as a homeomorphism. -/
noncomputable def affineInvHomeomorph (a : ℂ) (ha : a ≠ 0) (w : ℂ) : ℂ ≃ₜ ℂ where
  toFun x := a⁻¹ * (x - w)
  invFun z := a * z + w
  left_inv x := by
    simp only
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul, sub_add_cancel]
  right_inv z := by
    simp only
    rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Lebesgue change of variables for the complex affine map `z ↦ a z + w`. -/
theorem integral_comp_affine (G : ℂ → ℝ) {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    ∫ z, G (a * z + w) = (‖a‖ ^ 2)⁻¹ * ∫ x, G x := by
  have hrot : ∀ z, a * z = ‖a‖ • rotation (Circle.exp a.arg) z := by
    intro z
    rw [rotation_apply, Circle.coe_exp, Complex.real_smul, ← mul_assoc, Complex.norm_mul_exp_arg_mul_I]
  have h1 : ∫ z, G (a * z + w) = ∫ y, G (‖a‖ • y + w) := by
    simp only [hrot]
    exact (rotation (Circle.exp a.arg)).measurePreserving.integral_comp
      (rotation (Circle.exp a.arg)).toHomeomorph.measurableEmbedding (fun y => G (‖a‖ • y + w))
  rw [h1, Measure.integral_comp_smul volume (fun y => G (y + w)) ‖a‖, integral_add_right_eq_self,
    Complex.finrank_real_complex, smul_eq_mul, abs_of_nonneg (by positivity)]

/-- `e^{γ Q log s} = s² s^{γ²/2}` (`γ Q = 2 + γ²/2`). -/
theorem exp_lqgQ_mul_log {γ s : ℝ} (hγ : 0 < γ) (hs : 0 < s) :
    Real.exp (γ * (lqgQ γ * Real.log s)) = s ^ 2 * s ^ (γ ^ 2 / 2) := by
  rw [← Real.rpow_two, ← Real.rpow_add hs, Real.rpow_def_of_pos hs]
  congr 1
  unfold lqgQ
  field_simp

/-- **The circle average approximations under a complex affine map.** The approximation at scale `ε` of
`h ∘ φ + Q log |a|`, `φ(z) = a z + w`, is the image under `φ⁻¹` of the approximation of `h` at scale `|a| ε`. -/
theorem integral_lqgApprox_affine {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 ≤ ε) {H : ℝ → ℂ → ℝ} {a : ℂ} (ha : a ≠ 0)
    (w : ℂ) (hH : Continuous (H (‖a‖ * ε))) (g : ℂ → ℝ) :
    ∫ z, g z ∂lqgApprox γ (fun r z => H (‖a‖ * r) (a * z + w) + lqgQ γ * Real.log ‖a‖) ε =
      ∫ x, g (a⁻¹ * (x - w)) ∂lqgApprox γ H (‖a‖ * ε) := by
  have hs : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hm : Measurable fun z => H (‖a‖ * ε) (a * z + w) + lqgQ γ * Real.log ‖a‖ :=
    ((hH.comp (by fun_prop : Continuous fun z : ℂ => a * z + w)).add continuous_const).measurable
  rw [integral_lqgApprox hε hm, integral_lqgApprox (by positivity) hH.measurable]
  set G : ℂ → ℝ := fun x =>
    ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H (‖a‖ * ε) x + lqgQ γ * Real.log ‖a‖)) * g (a⁻¹ * (x - w)) with hGdef
  have hG : ∀ z, ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H (‖a‖ * ε) (a * z + w) + lqgQ γ * Real.log ‖a‖)) * g z =
      G (a * z + w) := by
    intro z
    simp only [hGdef, add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  rw [integral_congr_ae (Eventually.of_forall hG), integral_comp_affine G ha w, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hGdef]
  rw [mul_add, Real.exp_add, Real.mul_rpow hs.le hε, exp_lqgQ_mul_log hγ hs]
  field_simp

/-- **Fact 2.2 IV for one affine map, as a statement about scales.** For a field `H` with continuous circle
averages, the image of `m` under `φ⁻¹` is the LQG limit of `H ∘ φ + Q log |a|` if the approximations of `H` converge
vaguely to `m` along the scales `|a| 2⁻ᵏ`. -/
theorem isLQGLimit_affine_of_tendsto {γ : ℝ} (hγ : 0 < γ) {H : ℝ → ℂ → ℝ} {m : Measure ℂ}
    [IsLocallyFiniteMeasure m] (hH : ∀ ε, 0 < ε → Continuous (H ε)) {a : ℂ} (ha : a ≠ 0) (w : ℂ)
    (hlim : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun k => ∫ z, g z ∂lqgApprox γ H (‖a‖ * dyadicScale k)) atTop (𝓝 (∫ z, g z ∂m))) :
    IsLQGLimit γ (fun r z => H (‖a‖ * r) (a * z + w) + lqgQ γ * Real.log ‖a‖)
      (m.map fun x => a⁻¹ * (x - w)) := by
  have hs : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hψ : Continuous fun x : ℂ => a⁻¹ * (x - w) := by fun_prop
  have hfin : IsFiniteMeasureOnCompacts (m.map fun x => a⁻¹ * (x - w)) := ⟨fun K hK => by
    rw [Measure.map_apply hψ.measurable hK.measurableSet]
    exact ((affineInvHomeomorph a ha w).isCompact_preimage.2 hK).measure_lt_top⟩
  refine ⟨inferInstance, fun g hg hgc => ?_⟩
  rw [integral_map hψ.aemeasurable hg.aestronglyMeasurable]
  have hL : ∀ k, ∫ z, g z ∂lqgApprox γ (fun r z => H (‖a‖ * r) (a * z + w) + lqgQ γ * Real.log ‖a‖)
      (dyadicScale k) = ∫ x, g (a⁻¹ * (x - w)) ∂lqgApprox γ H (‖a‖ * dyadicScale k) := fun k =>
    integral_lqgApprox_affine hγ (dyadicScale_pos k).le ha w (hH _ (mul_pos hs (dyadicScale_pos k))) g
  simp only [hL]
  exact hlim _ (hg.comp hψ) (hgc.comp_homeomorph (affineInvHomeomorph a ha w))

/-- Converse of `isLQGLimit_affine_of_tendsto`: Fact 2.2 IV for `φ(z) = a z + w` gives the vague convergence of the
approximations of `H` along the scales `|a| 2⁻ᵏ`. -/
theorem tendsto_of_isLQGLimit_affine {γ : ℝ} (hγ : 0 < γ) {H : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (hH : ∀ ε, 0 < ε → Continuous (H ε)) {a : ℂ} (ha : a ≠ 0) (w : ℂ)
    (h : IsLQGLimit γ (fun r z => H (‖a‖ * r) (a * z + w) + lqgQ γ * Real.log ‖a‖)
      (m.map fun x => a⁻¹ * (x - w)))
    {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun k => ∫ z, g z ∂lqgApprox γ H (‖a‖ * dyadicScale k)) atTop (𝓝 (∫ z, g z ∂m)) := by
  have hs : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hψ : Continuous fun x : ℂ => a⁻¹ * (x - w) := by fun_prop
  have hφ : Continuous fun z : ℂ => a * z + w := by fun_prop
  have hcancel : ∀ x, a * (a⁻¹ * (x - w)) + w = x := fun x => by
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul, sub_add_cancel]
  have key := h.tendsto_integral (fun z => g (a * z + w)) (hg.comp hφ)
    (hgc.comp_homeomorph (affineInvHomeomorph a ha w).symm)
  rw [integral_map (f := fun z => g (a * z + w)) hψ.aemeasurable (hg.comp hφ).aestronglyMeasurable] at key
  have hL : ∀ k, ∫ z, g (a * z + w) ∂lqgApprox γ (fun r z => H (‖a‖ * r) (a * z + w) + lqgQ γ * Real.log ‖a‖)
      (dyadicScale k) = ∫ x, g x ∂lqgApprox γ H (‖a‖ * dyadicScale k) := fun k => by
    rw [integral_lqgApprox_affine hγ (dyadicScale_pos k).le ha w (hH _ (mul_pos hs (dyadicScale_pos k)))]
    simp only [hcancel]
  simp only [hL, hcancel] at key
  exact key

/-- The dilation case of Fact 2.2 IV in the affine form (`a = s`, `w = 0`). -/
theorem tendsto_of_isLQGLimit_dilation {γ : ℝ} (hγ : 0 < γ) {H : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (hH : ∀ ε, 0 < ε → Continuous (H ε)) {s : ℝ} (hs : 0 < s)
    (h : IsLQGLimit γ (fun r z => H (s * r) ((s : ℂ) * z) + lqgQ γ * Real.log s) (m.map fun x => (s : ℂ)⁻¹ * x))
    {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun k => ∫ z, g z ∂lqgApprox γ H (s * dyadicScale k)) atTop (𝓝 (∫ z, g z ∂m)) := by
  have hns : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  have h' : IsLQGLimit γ (fun r z => H (‖(s : ℂ)‖ * r) ((s : ℂ) * z + 0) + lqgQ γ * Real.log ‖(s : ℂ)‖)
      (m.map fun x => (s : ℂ)⁻¹ * (x - 0)) := by
    simp only [hns, add_zero, sub_zero]
    exact h
  have := tendsto_of_isLQGLimit_affine hγ hH hs0 0 h' hg hgc
  rwa [hns] at this

/-- **Fact 2.2 IV** (conformal covariance for complex affine maps) from its dilation case (cited). -/
theorem lqgMeasureConformalCovariancePart_of_dilation (hD : LQGMeasureDilationCovariancePart) :
    LQGMeasureConformalCovariancePart := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hμ
  filter_upwards [hD γ hγ hγ2 Ω P hC hcirc μ hμ, ae_continuous_circle hμ.2.1, hμ.2.2] with ω hDω hcont hlim
    a w ha
  have := hlim.isLocallyFiniteMeasure
  exact isLQGLimit_affine_of_tendsto hγ hcont ha w fun g hg hgc =>
    tendsto_of_isLQGLimit_dilation hγ hcont (norm_pos_iff.2 ha) (hDω _ (norm_pos_iff.2 ha)) hg hgc

/-- **Fact 2.2 from its cited parts**: non-atomicity (I), locality (II) and the dilation case of conformal
covariance (IV). Local finiteness (I), Weyl scaling (III), and translations and rotations (IV) are proved from the
definition of the LQG measure as a vague dyadic limit. -/
theorem lqgMeasureProperties_of_citedParts (hNA : LQGMeasureNonAtomicPart) (hII : LQGMeasureLocalityPart)
    (hD : LQGMeasureDilationCovariancePart) : LQGMeasurePropertiesStmt :=
  lqgMeasureProperties_of_parts (lqgMeasureRadonPart_of_nonAtomic hNA) hII lqgMeasureWeylScalingPart
    (lqgMeasureConformalCovariancePart_of_dilation hD)

end MatedCRT.LQGMeasure
