import MatedCRT.Proofs.Field.WholePlaneAffineCov
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import HarmonicBalls.Defs.LQG

/-!
# The LQG coordinate change of the affine transform (deterministic part)

For a sample `h : ℝ → ℂ → ℝ` (circle averages), `r > 0` and `z ∈ ℂ`, let `affH r z h s v = h(r s, r v + z) - h(r, z)`
(the circle averages of `h(r · + z) - h_r(z)`). The LQG approximations satisfy the exact identity

  `∫ g d(lqgApprox γ (affH r z h) δ) = c⁻¹ ∫ g((· - z)/r) d(lqgApprox γ h (r δ))`,  `c = r^{γQ} e^{γ h(r, z)}`,

with `γQ = 2 + γ²/2` (Duplantier-Sheffield 2011, Prop. 2.1; the LQG coordinate change of Harmonic-Balls
`LQGMeasureCoordChange`). Consequently the vague limit of the transformed approximations is `c⁻¹ · μ((· - z)/r)`
if and only if the approximations of `h` converge vaguely to `μ` along the scales `r · 2^{-k}`.
This file proves the identity and this equivalence; the convergence along `r · 2^{-k}` is not proved here.
-/

namespace MatedCRT.Field

open MeasureTheory Filter Topology HarmonicBalls

/-- The circle averages `affH r z h s v = h(r s, r v + z) - h(r, z)` of the transformed sample. -/
noncomputable def affH (r : ℝ) (z : ℂ) (h : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun s v => h (r * s) ((r : ℂ) * v + z) - h r z

/-- The coordinate change constant `c = r^{γQ} e^{γ h(r, z)}`, `γQ = 2 + γ²/2`. -/
noncomputable def coordConst (γ r : ℝ) (h : ℝ → ℂ → ℝ) (z : ℂ) : ℝ :=
  r ^ (2 + γ ^ 2 / 2) * Real.exp (γ * h r z)

/-- The coordinate change constant is positive. -/
theorem coordConst_pos (γ : ℝ) {r : ℝ} (hr : 0 < r) (h : ℝ → ℂ → ℝ) (z : ℂ) :
    0 < coordConst γ r h z :=
  mul_pos (Real.rpow_pos_of_pos hr _) (Real.exp_pos _)

/-- The integral of `g` against the LQG approximation of a continuous slice:
`∫ g d(lqgApprox γ h ε) = ∫ g(x) ε^{γ²/2} e^{γ h(ε, x)} dx`. -/
theorem integral_lqgApprox (γ : ℝ) (h : ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) (hc : Continuous (h ε))
    (g : ℂ → ℝ) :
    ∫ x, g x ∂(lqgApprox γ h ε) = ∫ x, g x * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * h ε x)) := by
  unfold lqgApprox
  have hreal : Continuous fun x => ε ^ (γ ^ 2 / 2) * Real.exp (γ * h ε x) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc))
  have hmeas : Measurable fun x => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * h ε x)) :=
    ENNReal.measurable_ofReal.comp hreal.measurable
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le)]
  ring

/-- **The approximation identity.** For `δ > 0`:
`∫ g d(lqgApprox γ (affH r z h) δ) = c⁻¹ ∫ g((x - z)/r) d(lqgApprox γ h (r δ))`, `c = coordConst γ r h z`. -/
theorem integral_lqgApprox_affine (γ : ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) (h : ℝ → ℂ → ℝ)
    (hc : ∀ ε : ℝ, 0 < ε → Continuous (h ε)) {δ : ℝ} (hδ : 0 < δ) (g : ℂ → ℝ) :
    ∫ x, g x ∂(lqgApprox γ (affH r z h) δ)
      = (coordConst γ r h z)⁻¹ * ∫ x, g ((x - z) / (r : ℂ)) ∂(lqgApprox γ h (r * δ)) := by
  have hcont_aff : Continuous (affH r z h δ) :=
    ((hc (r * δ) (mul_pos hr hδ)).comp (continuous_affine_map r z)).sub continuous_const
  rw [integral_lqgApprox γ (affH r z h) hδ hcont_aff g,
    integral_lqgApprox γ h (mul_pos hr hδ) (hc _ (mul_pos hr hδ)) (fun x => g ((x - z) / (r : ℂ)))]
  have hpull := integral_affine_pullback g (fun y => (r * δ) ^ (γ ^ 2 / 2) * Real.exp (γ * h (r * δ) y)) hr z
  rw [hpull]
  have hpt : ∀ x : ℂ, g x * (δ ^ (γ ^ 2 / 2) * Real.exp (γ * affH r z h δ x))
      = (coordConst γ r h z)⁻¹ * ((r ^ 2) * (g x * ((r * δ) ^ (γ ^ 2 / 2)
          * Real.exp (γ * h (r * δ) ((r : ℂ) * x + z))))) := by
    intro x
    have hA : (0 : ℝ) < r ^ (γ ^ 2 / 2) := Real.rpow_pos_of_pos hr _
    have hB : (0 : ℝ) < δ ^ (γ ^ 2 / 2) := Real.rpow_pos_of_pos hδ _
    have hE : (0 : ℝ) < Real.exp (γ * h r z) := Real.exp_pos _
    have hmul : (r * δ) ^ (γ ^ 2 / 2) = r ^ (γ ^ 2 / 2) * δ ^ (γ ^ 2 / 2) :=
      Real.mul_rpow hr.le hδ.le
    have hpow : r ^ (2 + γ ^ 2 / 2) = r ^ 2 * r ^ (γ ^ 2 / 2) := by
      rw [Real.rpow_add hr, Real.rpow_two]
    have hexp : Real.exp (γ * affH r z h δ x)
        = Real.exp (γ * h (r * δ) ((r : ℂ) * x + z)) / Real.exp (γ * h r z) := by
      rw [← Real.exp_sub]
      congr 1
      unfold affH
      ring
    unfold coordConst
    rw [hpow, hmul, hexp]
    field_simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, integral_const_mul]

/-- Dyadic scales are positive. -/
theorem dyadic_pos (k : ℕ) : 0 < dyadicScale k := by
  unfold dyadicScale
  positivity

/-- Multiplication by a nonzero constant preserves and reflects convergence. -/
theorem tendsto_const_mul_iff_of_ne {c : ℝ} (hc : c ≠ 0) {u : ℕ → ℝ} {a : ℝ} :
    Tendsto (fun k => c * u k) atTop (𝓝 (c * a)) ↔ Tendsto u atTop (𝓝 a) :=
  ⟨fun H => by simpa only [inv_mul_cancel_left₀ hc] using H.const_mul c⁻¹, fun H => H.const_mul c⟩

/-- Pullback of a compactly supported function under `x ↦ (x - z)/r`. -/
theorem hasCompactSupport_comp_div (f : ℂ → ℝ) (hf : HasCompactSupport f) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    HasCompactSupport (fun x => f ((x - z) / (r : ℂ))) :=
  hf.comp_homeomorph ((Homeomorph.subRight z).trans
    (Homeomorph.mulRight₀ (r : ℂ)⁻¹ (inv_ne_zero (by exact_mod_cast hr.ne'))))

/-- Pullback of a compactly supported function under `x ↦ r x + z`. -/
theorem hasCompactSupport_comp_affine (f : ℂ → ℝ) (hf : HasCompactSupport f) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    HasCompactSupport (fun x => f ((r : ℂ) * x + z)) :=
  hf.comp_homeomorph ((Homeomorph.mulLeft₀ (r : ℂ) (by exact_mod_cast hr.ne')).trans (Homeomorph.addRight z))

/-- The convergence of the transformed approximations against a continuous `f` is the convergence of the
approximations of `h` against `f ∘ S`, `S x = (x - z)/r`, along the scales `r · 2^{-k}`. -/
theorem tendsto_affine_iff (γ : ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) (h : ℝ → ℂ → ℝ)
    (hc : ∀ ε : ℝ, 0 < ε → Continuous (h ε)) (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (f : ℂ → ℝ) (hf : Continuous f) :
    Tendsto (fun k : ℕ => ∫ x, f x ∂(lqgApprox γ (affH r z h) (dyadicScale k))) atTop
        (𝓝 (∫ x, f x ∂(ENNReal.ofReal (coordConst γ r h z)⁻¹ • μ.map (fun x => (x - z) / (r : ℂ)))))
      ↔ Tendsto (fun k : ℕ => ∫ x, f ((x - z) / (r : ℂ)) ∂(lqgApprox γ h (r * dyadicScale k))) atTop
          (𝓝 (∫ x, f ((x - z) / (r : ℂ)) ∂μ)) := by
  have hc0 : (0 : ℝ) < coordConst γ r h z := coordConst_pos γ hr h z
  have hmeasS : Measurable (fun x : ℂ => (x - z) / (r : ℂ)) :=
    ((continuous_id.sub continuous_const).div_const _).measurable
  have e1 : ∀ k : ℕ, ∫ x, f x ∂(lqgApprox γ (affH r z h) (dyadicScale k))
      = (coordConst γ r h z)⁻¹ * ∫ x, f ((x - z) / (r : ℂ)) ∂(lqgApprox γ h (r * dyadicScale k)) :=
    fun k => integral_lqgApprox_affine γ hr z h hc (dyadic_pos k) f
  have e2 : ∫ x, f x ∂(ENNReal.ofReal (coordConst γ r h z)⁻¹ • μ.map (fun x => (x - z) / (r : ℂ)))
      = (coordConst γ r h z)⁻¹ * ∫ x, f ((x - z) / (r : ℂ)) ∂μ := by
    rw [integral_smul_measure, integral_map hmeasS.aemeasurable hf.aestronglyMeasurable,
      ENNReal.toReal_ofReal (inv_nonneg.2 hc0.le), smul_eq_mul]
  simp only [e1, e2]
  exact tendsto_const_mul_iff_of_ne (inv_ne_zero hc0.ne')

/-- The affine homeomorphism `x ↦ (x - z)/r` (its inverse is `x ↦ r x + z`). -/
noncomputable def divAffHomeo (z : ℂ) {r : ℝ} (hr : 0 < r) : ℂ ≃ₜ ℂ where
  toFun x := (x - z) / (r : ℂ)
  invFun x := (r : ℂ) * x + z
  left_inv x := by
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    simp only
    field_simp
    ring
  right_inv x := by
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    simp only
    field_simp
    ring
  continuous_toFun := (continuous_id.sub continuous_const).div_const _
  continuous_invFun := (continuous_const.mul continuous_id).add continuous_const

/-- A pushforward of a locally finite measure by a homeomorphism is locally finite. -/
theorem isLocallyFiniteMeasure_map_homeo (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (e : ℂ ≃ₜ ℂ) :
    IsLocallyFiniteMeasure (μ.map e) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨s, hs, hfin⟩ := IsLocallyFiniteMeasure.finiteAtNhds (μ := μ) (e.symm x)
  obtain ⟨t, hts, ht, hxt⟩ := mem_nhds_iff.1 hs
  refine ⟨e '' t, (e.isOpenMap t ht).mem_nhds ⟨e.symm x, hxt, e.apply_symm_apply x⟩, ?_⟩
  rw [Measure.map_apply e.continuous.measurable (e.isOpenMap t ht).measurableSet,
    Set.preimage_image_eq t e.injective]
  exact lt_of_le_of_lt (measure_mono hts) hfin

/-- A scalar multiple of a locally finite measure by a finite constant is locally finite. -/
theorem isLocallyFiniteMeasure_ofReal_smul (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (c : ℝ) :
    IsLocallyFiniteMeasure (ENNReal.ofReal c • μ) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨s, hs, hfin⟩ := IsLocallyFiniteMeasure.finiteAtNhds (μ := μ) x
  refine ⟨s, hs, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- **The LQG coordinate change, deterministic form.** For a sample `h` of circle averages (continuous in `z`
for each positive radius) and a locally finite `μ`, the transformed measure `c⁻¹ · μ((· - z)/r)`, `c = coordConst`,
is the γ-LQG vague limit of the circle averages `affH r z h` if and only if the approximations of `h` converge
vaguely to `μ` along the scales `r · 2^{-k}`. -/
theorem isLQGLimit_affine_iff (γ : ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) (h : ℝ → ℂ → ℝ)
    (hc : ∀ ε : ℝ, 0 < ε → Continuous (h ε)) (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] :
    IsLQGLimit γ (affH r z h) (ENNReal.ofReal (coordConst γ r h z)⁻¹ • μ.map (fun x => (x - z) / (r : ℂ)))
      ↔ ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
        Tendsto (fun k : ℕ => ∫ x, g x ∂(lqgApprox γ h (r * dyadicScale k))) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hLF : IsLocallyFiniteMeasure (μ.map (fun x => (x - z) / (r : ℂ))) :=
    isLocallyFiniteMeasure_map_homeo μ (divAffHomeo z hr)
  have hLF' : IsLocallyFiniteMeasure
      (ENNReal.ofReal (coordConst γ r h z)⁻¹ • μ.map (fun x => (x - z) / (r : ℂ))) :=
    isLocallyFiniteMeasure_ofReal_smul _ _
  constructor
  · intro hL g hg hgc
    have hgT : Continuous (fun x => g ((r : ℂ) * x + z)) := hg.comp (continuous_affine_map r z)
    have key := (tendsto_affine_iff γ hr z h hc μ (fun x => g ((r : ℂ) * x + z)) hgT).1
      (hL.tendsto_integral _ hgT (hasCompactSupport_comp_affine g hgc hr z))
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hTS : ∀ x : ℂ, (r : ℂ) * ((x - z) / (r : ℂ)) + z = x := fun x => by
      field_simp
      ring
    simpa only [hTS] using key
  · intro hg
    refine ⟨hLF', fun f hf hfc => ?_⟩
    exact (tendsto_affine_iff γ hr z h hc μ f hf).2
      (hg (fun x => f ((x - z) / (r : ℂ)))
        (hf.comp ((continuous_id.sub continuous_const).div_const _))
        (hasCompactSupport_comp_div f hfc hr z))

end MatedCRT.Field

