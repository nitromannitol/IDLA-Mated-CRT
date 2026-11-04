import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.Conditions

/-!
# Scaling of harmonic balls: the Laplacian and the mean value property

* `laplacian_comp_smul_of_contDiffOn`: `Δ(f(c ·))(y) = c² (Δf)(c y)` where `f` is `C²` near `c y`.
* `harmonicAt_comp_smul`: harmonic functions are preserved by dilations.
* Integrals and integrability for `b⁻¹ μ(R ·)` (`setIntegral_rescaledMeasure`, `integrableOn_rescaledMeasure_iff`).
* `IsHarmonicBall.rescale`: `R⁻¹ Λ` is a harmonic ball for `b⁻¹ μ(R ·)` if `Λ` is one for `μ` (centre `0`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- Multiplication by the real number `c` on `ℂ`, as a real continuous linear map. -/
noncomputable def smulCLM (c : ℝ) : ℂ →L[ℝ] ℂ := c • ContinuousLinearMap.id ℝ ℂ

theorem smulCLM_apply (c : ℝ) (z : ℂ) : smulCLM c z = c • z := rfl

/-- **The Laplacian under a dilation**: `Δ(f(c ·))(y) = c² (Δf)(c y)` if `f` is `C²` on an open set containing `c y`. -/
theorem laplacian_comp_smul_of_contDiffOn {f : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (c : ℝ) {y : ℂ} (hy : c • y ∈ U) :
    Laplacian.laplacian (fun z => f (c • z)) y = c ^ 2 * Laplacian.laplacian f (c • y) := by
  have hpre : IsOpen (smulCLM c ⁻¹' U) := hU.preimage (smulCLM c).continuous
  have hy' : y ∈ smulCLM c ⁻¹' U := hy
  have hy'' : smulCLM c y ∈ U := hy
  have key : iteratedFDeriv ℝ 2 (f ∘ smulCLM c) y =
      (iteratedFDeriv ℝ 2 f (smulCLM c y)).compContinuousLinearMap fun _ => smulCLM c := by
    have h1 := (smulCLM c).iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hy''
      (i := 2) le_rfl
    rw [iteratedFDerivWithin_of_isOpen (n := 2) hpre hy', iteratedFDerivWithin_of_isOpen (n := 2) hU hy''] at h1
    exact h1
  have hsmul : ∀ v : Fin 2 → ℂ,
      (iteratedFDeriv ℝ 2 f (smulCLM c y)).compContinuousLinearMap (fun _ => smulCLM c) v =
        c ^ 2 * iteratedFDeriv ℝ 2 f (smulCLM c y) v := by
    intro v
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hv : (fun i => smulCLM c (v i)) = fun i => (fun _ : Fin 2 => c) i • v i := rfl
    rw [hv, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  have hlap : ∀ (h : ℂ → ℝ) (x : ℂ), Laplacian.laplacian h x =
      iteratedFDeriv ℝ 2 h x ![1, 1] + iteratedFDeriv ℝ 2 h x ![Complex.I, Complex.I] :=
    fun h x => congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane h) x
  have hcomp : (fun z => f (c • z)) = f ∘ smulCLM c := rfl
  rw [hlap, hlap, hcomp, key, hsmul, hsmul, smulCLM_apply]
  ring

/-- **Harmonic functions are preserved by dilations.** -/
theorem harmonicAt_comp_smul {f : ℂ → ℝ} {c : ℝ} {x : ℂ} (hf : InnerProductSpace.HarmonicAt f (c • x)) :
    InnerProductSpace.HarmonicAt (fun z => f (c • z)) x := by
  obtain ⟨hcd, hlap⟩ := hf
  refine ⟨hcd.comp x (smulCLM c).contDiff.contDiffAt, ?_⟩
  obtain ⟨u, hu, hfu⟩ := hcd.contDiffOn le_rfl (by simp)
  obtain ⟨V, hVu, hVo, hxV⟩ := _root_.mem_nhds_iff.1 (Filter.inter_mem hu hlap)
  have hpre : smulCLM c ⁻¹' V ∈ 𝓝 x :=
    (smulCLM c).continuous.continuousAt.preimage_mem_nhds (hVo.mem_nhds hxV)
  filter_upwards [hpre] with y hy
  have hy' : c • y ∈ V := hy
  rw [laplacian_comp_smul_of_contDiffOn (y := y) hVo (hfu.mono fun z hz => (hVu hz).1) c hy']
  have h0 : Laplacian.laplacian f (c • y) = 0 := (hVu hy').2
  rw [h0, mul_zero]
  rfl

/-- The inverse dilation `x ↦ R⁻¹ x` is a measurable embedding. -/
theorem measurableEmbedding_inv_dilation {R : ℝ} (hR : R ≠ 0) : MeasurableEmbedding fun x : ℂ => (R : ℂ)⁻¹ * x :=
  (Homeomorph.mulLeft₀ _ (inv_ne_zero (Complex.ofReal_ne_zero.2 hR))).measurableEmbedding

theorem preimage_inv_dilation_preimage_dilation {R : ℝ} (hR : R ≠ 0) (B : Set ℂ) :
    (fun x : ℂ => (R : ℂ)⁻¹ * x) ⁻¹' ((fun x : ℂ => (R : ℂ) * x) ⁻¹' B) = B := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR
  ext y
  simp [hRc]

/-- Set integrals for `b⁻¹ μ(R ·)`. -/
theorem setIntegral_rescaledMeasure (μ : Measure ℂ) {R : ℝ} (hR : R ≠ 0) {b : ℝ} (hb : 0 < b) (f : ℂ → ℝ)
    (B : Set ℂ) :
    ∫ x in (fun x => (R : ℂ) * x) ⁻¹' B, f x ∂(rescaledMeasure μ R b) =
      b⁻¹ * ∫ y in B, f ((R : ℂ)⁻¹ * y) ∂μ := by
  rw [rescaledMeasure, Measure.restrict_smul, integral_smul_measure,
    (measurableEmbedding_inv_dilation hR).setIntegral_map, preimage_inv_dilation_preimage_dilation hR,
    ENNReal.toReal_ofReal (inv_nonneg.2 hb.le), smul_eq_mul]

/-- Integrability on sets for `b⁻¹ μ(R ·)`. -/
theorem integrableOn_rescaledMeasure_iff (μ : Measure ℂ) {R : ℝ} (hR : R ≠ 0) {b : ℝ} (hb : 0 < b) (f : ℂ → ℝ)
    (B : Set ℂ) :
    IntegrableOn f ((fun x => (R : ℂ) * x) ⁻¹' B) (rescaledMeasure μ R b) ↔
      IntegrableOn (fun y => f ((R : ℂ)⁻¹ * y)) B μ := by
  rw [IntegrableOn, rescaledMeasure, Measure.restrict_smul,
    integrable_smul_measure (ENNReal.ofReal_pos.2 (inv_pos.2 hb)).ne' ENNReal.ofReal_ne_top, ← IntegrableOn,
    (measurableEmbedding_inv_dilation hR).integrableOn_map_iff, preimage_inv_dilation_preimage_dilation hR]
  rfl

theorem measureReal_rescaledMeasure_preimage (μ : Measure ℂ) {R : ℝ} (hR : R ≠ 0) {b : ℝ} (hb : 0 < b)
    (B : Set ℂ) :
    (rescaledMeasure μ R b).real ((fun x => (R : ℂ) * x) ⁻¹' B) = b⁻¹ * μ.real B := by
  rw [measureReal_def, rescaledMeasure_preimage μ hR b B, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.2 hb.le), measureReal_def]

/-- **Harmonic balls are preserved by scaling**: if `Λ` is a harmonic ball for `μ` centred at `0`, then `R⁻¹ Λ` is one
for `b⁻¹ μ(R ·)`. -/
theorem IsHarmonicBall.rescale {μ : Measure ℂ} {Λ : Set ℂ} {R b : ℝ} (h : IsHarmonicBall μ Λ 0) (hR : 0 < R)
    (hb : 0 < b) : IsHarmonicBall (rescaledMeasure μ R b) ((fun x => (R : ℂ) * x) ⁻¹' Λ) 0 := by
  obtain ⟨hopen, hmem, hpos, hfin, hmv⟩ := h
  have hR0 : R ≠ 0 := hR.ne'
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0
  have hνΛ := rescaledMeasure_preimage μ hR0 b Λ
  refine ⟨hopen.preimage (continuous_const.mul continuous_id), ?_, ?_, ?_, ?_⟩
  · show (R : ℂ) * 0 ∈ Λ
    rw [mul_zero]
    exact hmem
  · rw [hνΛ]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (inv_pos.2 hb)).ne' hpos.ne'
  · rw [hνΛ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  · intro f hf
    have hg : InnerProductSpace.HarmonicOnNhd (fun y => f ((R⁻¹ : ℝ) • y)) (closure Λ) := by
      intro y hy
      apply harmonicAt_comp_smul
      apply hf
      show (R⁻¹ : ℝ) • y ∈ closure (dilation R hR0 ⁻¹' Λ)
      rw [← (dilation R hR0).preimage_closure]
      show (R : ℂ) * ((R⁻¹ : ℝ) • y) ∈ closure Λ
      rwa [Complex.real_smul, Complex.ofReal_inv, mul_inv_cancel_left₀ hRc]
    obtain ⟨hint, heq⟩ := hmv _ hg
    have hfun : (fun y => f ((R⁻¹ : ℝ) • y)) = fun y => f ((R : ℂ)⁻¹ * y) := by
      funext y
      rw [Complex.real_smul, Complex.ofReal_inv]
    rw [hfun] at hint heq
    refine ⟨(integrableOn_rescaledMeasure_iff μ hR0 hb f Λ).2 hint, ?_⟩
    have heq' : f 0 * μ.real Λ = ∫ y in Λ, f ((R : ℂ)⁻¹ * y) ∂μ := by
      simpa only [mul_zero] using heq
    rw [measureReal_rescaledMeasure_preimage μ hR0 hb Λ, setIntegral_rescaledMeasure μ hR0 hb f Λ, ← heq']
    ring

end MatedCRT
