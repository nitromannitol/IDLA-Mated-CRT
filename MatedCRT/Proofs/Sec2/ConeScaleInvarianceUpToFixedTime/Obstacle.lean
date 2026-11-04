import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.Harmonic
import HarmonicBalls.Proofs.Potential.GreenBall

/-!
# Scaling of harmonic balls: the obstacle problem (condition (c) of Theorem 2.3)

For `R, b > 0` and `ν = b⁻¹ μ(R ·)` (`rescaledMeasure`):
* the Green function of a disk is scale invariant, `G_{B_{Rρ}}(0, R x) = G_{B_ρ}(0, x)`
  (`greenFunction_ball_zero_dilation`, from HB22's explicit `greenBall`);
* `w ↦ b⁻¹ w(R ·)` maps the supersolutions for `(μ, B_{Rρ}, bt)` onto those for `(ν, B_ρ, t)`, hence
  `w̄^{B_ρ}_t[ν](x) = b⁻¹ w̄^{B_{Rρ}}_{bt}[μ](R x)` (`leastSupersolution_rescaledMeasure`) and the clusters scale
  (`cluster_rescaledMeasure`);
* weak Laplacians scale (`HasLaplacian.rescale`);
so condition (c) is preserved (`SatisfiesObstacleCharacterizationOn.rescale`), and with
`SatisfiesHarmonicBallConditionsOn.rescale` and `IsHarmonicBall.rescale` this proves the deterministic step
`ConeHarmonicBallFamilyOnScalingStep` (`coneHarmonicBallFamilyOnScalingStep`).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal Pointwise

/-- HB22's explicit Green function of the disk `B_ρ` with pole `0` is scale invariant. -/
theorem greenBall_zero_dilation {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (y : ℂ) :
    greenBall (R * ρ) 0 ((R : ℂ) * y) = greenBall ρ 0 y := by
  unfold greenBall
  congr 2
  simp only [map_zero, zero_mul, sub_zero, zero_sub, norm_neg, norm_pow, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR, abs_of_pos hρ, Complex.ofReal_mul]
  rcases eq_or_ne ‖y‖ 0 with h | h
  · simp [h]
  · field_simp

/-- **The Green function of a disk is scale invariant**: `G_{B_{Rρ}}(0, R x) = G_{B_ρ}(0, x)`. -/
theorem greenFunction_ball_zero_dilation {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (x : ℂ) :
    greenFunction (ball 0 (R * ρ)) 0 ((R : ℂ) * x) = greenFunction (ball 0 ρ) 0 x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [mul_zero, greenFunction_self, greenFunction_self]
  rcases lt_or_ge ‖x‖ ρ with hxρ | hxρ
  · have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ρ := mem_ball_self hρ
    have h0' : (0 : ℂ) ∈ ball (0 : ℂ) (R * ρ) := mem_ball_self (mul_pos hR hρ)
    have hxb : x ∈ ball (0 : ℂ) ρ := mem_ball_zero_iff.2 hxρ
    have hxb' : (R : ℂ) * x ∈ ball (0 : ℂ) (R * ρ) := by
      rw [mem_ball_zero_iff, norm_dilation hR]
      exact mul_lt_mul_of_pos_left hxρ hR
    have hRx : (0 : ℂ) ≠ (R : ℂ) * x := (mul_ne_zero (Complex.ofReal_ne_zero.2 hR.ne') hx).symm
    rw [greenFunction_ball h0' hxb' hRx, greenFunction_ball h0 hxb (Ne.symm hx), greenBall_zero_dilation hR hρ]
  · have h1 : R * ρ ≤ ‖(R : ℂ) * x‖ := by
      rw [norm_dilation hR]
      exact mul_le_mul_of_nonneg_left hxρ hR.le
    rw [greenFunction_ball_of_le_norm h1, greenFunction_ball_of_le_norm hxρ]

/-- A test function on `B_ρ`, composed with `x ↦ R⁻¹ x`, is a test function on `B_{Rρ}`. -/
theorem isTestFunction_comp_inv_dilation {φ : ℂ → ℝ} {R ρ : ℝ} (hR : 0 < R) (hφ : IsTestFunction (ball 0 ρ) φ) :
    IsTestFunction (ball 0 (R * ρ)) (fun y => φ ((R : ℂ)⁻¹ * y)) := by
  have hRc : (R : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 hR.ne')
  have hfun : (fun y => φ ((R : ℂ)⁻¹ * y)) = φ ∘ Homeomorph.mulLeft₀ _ hRc := rfl
  have hfun' : (fun y => φ ((R : ℂ)⁻¹ * y)) = φ ∘ smulCLM R⁻¹ := by
    funext y
    simp [smulCLM_apply, Complex.real_smul]
  obtain ⟨hcd, hcs, hsupp⟩ := hφ
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun']
    exact hcd.comp (smulCLM R⁻¹).contDiff
  · rw [hfun]
    exact hcs.comp_homeomorph _
  · rw [hfun, tsupport_comp_eq_preimage]
    intro y hy
    have h1 : (R : ℂ)⁻¹ * y ∈ ball (0 : ℂ) ρ := hsupp hy
    rw [mem_ball_zero_iff, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le] at h1
    rw [mem_ball_zero_iff]
    have e : ‖y‖ = R * (R⁻¹ * ‖y‖) := by field_simp
    rw [e]
    exact mul_lt_mul_of_pos_left h1 hR

/-- Integrals for `b⁻¹ μ(R ·)`. -/
theorem integral_rescaledMeasure (μ : Measure ℂ) {R : ℝ} (hR : R ≠ 0) {b : ℝ} (hb : 0 < b) (f : ℂ → ℝ) :
    ∫ x, f x ∂(rescaledMeasure μ R b) = b⁻¹ * ∫ y, f ((R : ℂ)⁻¹ * y) ∂μ := by
  rw [rescaledMeasure, integral_smul_measure, (measurableEmbedding_inv_dilation hR).integral_map,
    ENNReal.toReal_ofReal (inv_nonneg.2 hb.le), smul_eq_mul]

/-- Integrability for `b⁻¹ μ(R ·)`. -/
theorem integrable_rescaledMeasure_iff (μ : Measure ℂ) {R : ℝ} (hR : R ≠ 0) {b : ℝ} (hb : 0 < b) (f : ℂ → ℝ) :
    Integrable f (rescaledMeasure μ R b) ↔ Integrable (fun y => f ((R : ℂ)⁻¹ * y)) μ := by
  rw [rescaledMeasure, integrable_smul_measure (ENNReal.ofReal_pos.2 (inv_pos.2 hb)).ne' ENNReal.ofReal_ne_top,
    (measurableEmbedding_inv_dilation hR).integrable_map_iff]
  rfl

/-- Restriction of `b⁻¹ μ(R ·)` to a preimage under `x ↦ R x`. -/
theorem rescaledMeasure_restrict (μ : Measure ℂ) {R : ℝ} (hR : R ≠ 0) (b : ℝ) (B : Set ℂ) :
    (rescaledMeasure μ R b).restrict ((fun x => (R : ℂ) * x) ⁻¹' B) = rescaledMeasure (μ.restrict B) R b := by
  rw [rescaledMeasure, Measure.restrict_smul, (measurableEmbedding_inv_dilation hR).restrict_map,
    preimage_inv_dilation_preimage_dilation hR, rescaledMeasure]

/-- Integrability on sets under the dilation `x ↦ R x` (Lebesgue measure). -/
theorem integrableOn_comp_smul_iff {w : ℂ → ℝ} {R : ℝ} (hR : R ≠ 0) (K : Set ℂ) :
    IntegrableOn (fun x => w (R • x)) K ↔ IntegrableOn w ((fun x : ℂ => R • x) '' K) := by
  have hemb : MeasurableEmbedding fun x : ℂ => R • x := (Homeomorph.smulOfNeZero R hR).measurableEmbedding
  have hmap := Measure.map_addHaar_smul (μ := (volume : Measure ℂ)) hR
  have hc0 : ENNReal.ofReal |(R ^ Module.finrank ℝ ℂ)⁻¹| ≠ 0 :=
    (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero (pow_ne_zero _ hR)))).ne'
  have h1 := hemb.integrableOn_map_iff (f := w) (μ := volume) (s := (fun x : ℂ => R • x) '' K)
  rw [Set.preimage_image_eq K hemb.injective, hmap, IntegrableOn, Measure.restrict_smul,
    integrable_smul_measure hc0 ENNReal.ofReal_ne_top, ← IntegrableOn] at h1
  exact h1.symm

/-- Local integrability is preserved by `w ↦ c w(R ·)`. -/
theorem locallyIntegrableOn_rescale {w : ℂ → ℝ} {R ρ : ℝ} (hR : 0 < R) (c : ℝ)
    (hw : LocallyIntegrableOn w (ball 0 (R * ρ))) :
    LocallyIntegrableOn (fun x => c * w ((R : ℂ) * x)) (ball 0 ρ) := by
  rw [locallyIntegrableOn_iff isOpen_ball.isLocallyClosed] at hw ⊢
  intro K hK hKc
  have hsub : (fun x : ℂ => R • x) '' K ⊆ ball 0 (R * ρ) := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hK hx
    rw [mem_ball_zero_iff] at h1 ⊢
    rw [norm_smul, Real.norm_of_nonneg hR.le]
    exact mul_lt_mul_of_pos_left h1 hR
  have h2 := (integrableOn_comp_smul_iff hR.ne' K).2 (hw _ hsub (hKc.image (continuous_const_smul R)))
  have hfun : (fun x => c * w ((R : ℂ) * x)) = fun x => c * w (R • x) := by
    funext x
    rw [Complex.real_smul]
  rw [hfun]
  exact h2.const_mul c

/-- **Change of variables in the weak Laplacian**: with `ψ = φ(R⁻¹ ·)`,
`∫ c w(R x) Δφ(x) dx = c ∫ w(y) Δψ(y) dy`. -/
theorem integral_rescale_mul_laplacian {w φ : ℂ → ℝ} {R : ℝ} (hR : 0 < R) (hφ : ContDiff ℝ 2 φ) (c : ℝ) :
    ∫ x, c * w ((R : ℂ) * x) * Laplacian.laplacian φ x =
      c * ∫ y, w y * Laplacian.laplacian (fun y => φ ((R : ℂ)⁻¹ * y)) y := by
  have hR0 : R ≠ 0 := hR.ne'
  have hψ : ∀ y, Laplacian.laplacian (fun y => φ ((R : ℂ)⁻¹ * y)) y =
      (R⁻¹) ^ 2 * Laplacian.laplacian φ (R⁻¹ • y) := by
    intro y
    have hfun : (fun y => φ ((R : ℂ)⁻¹ * y)) = fun y => φ ((R⁻¹ : ℝ) • y) := by
      funext y
      rw [Complex.real_smul, Complex.ofReal_inv]
    rw [hfun]
    exact laplacian_comp_smul_of_contDiffOn isOpen_univ hφ.contDiffOn R⁻¹ (mem_univ _)
  simp_rw [hψ]
  have hsub := Measure.integral_comp_smul (volume : Measure ℂ)
    (fun y => w y * ((R⁻¹) ^ 2 * Laplacian.laplacian φ (R⁻¹ • y))) R
  have hFR : ∀ x : ℂ, w (R • x) * ((R⁻¹) ^ 2 * Laplacian.laplacian φ (R⁻¹ • R • x)) =
      (R⁻¹) ^ 2 * (w ((R : ℂ) * x) * Laplacian.laplacian φ x) := by
    intro x
    rw [smul_smul, inv_mul_cancel₀ hR0, one_smul, Complex.real_smul]
    ring
  simp_rw [hFR] at hsub
  have hpow : |(R ^ 2)⁻¹| = R⁻¹ ^ 2 := by
    rw [abs_of_pos (by positivity), inv_pow]
  rw [integral_const_mul, Complex.finrank_real_complex, smul_eq_mul, hpow] at hsub
  have hI := (mul_left_cancel₀ (pow_ne_zero 2 (inv_ne_zero hR0)) hsub).symm
  rw [hI, ← integral_const_mul]
  congr 1
  funext x
  ring

/-- **Supersolutions scale**: if `w` is a supersolution for `(μ, B_{Rρ}, bt)`, then `b⁻¹ w(R ·)` is one for
`(b⁻¹ μ(R ·), B_ρ, t)`. -/
theorem rescale_mem_supersolutions {μ : Measure ℂ} {R b ρ t : ℝ} (hR : 0 < R) (hb : 0 < b) (hρ : 0 < ρ)
    {w : ℂ → ℝ} (hw : w ∈ supersolutions μ (R * ρ) 0 (b * t)) :
    (fun x => b⁻¹ * w ((R : ℂ) * x)) ∈ supersolutions (rescaledMeasure μ R b) ρ 0 t := by
  obtain ⟨hcont, ⟨hloc, hle⟩, hobs⟩ := hw
  have hR0 : R ≠ 0 := hR.ne'
  have hmaps : MapsTo (fun x : ℂ => (R : ℂ) * x) (closedBall 0 ρ) (closedBall 0 (R * ρ)) := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    rw [norm_dilation hR]
    exact mul_le_mul_of_nonneg_left hx hR.le
  refine ⟨?_, ⟨locallyIntegrableOn_rescale hR b⁻¹ hloc, ?_⟩, ?_⟩
  · exact continuousOn_const.mul (hcont.comp (continuous_const.mul continuous_id).continuousOn hmaps)
  · intro φ hφ hφ0 hint
    have hψ := isTestFunction_comp_inv_dilation hR hφ
    have hψ0 : 0 ≤ fun y => φ ((R : ℂ)⁻¹ * y) := fun y => hφ0 ((R : ℂ)⁻¹ * y)
    have hψint : Integrable (fun y => φ ((R : ℂ)⁻¹ * y)) μ := (integrable_rescaledMeasure_iff μ hR0 hb φ).1 hint
    have h1 := hle _ hψ hψ0 hψint
    beta_reduce
    rw [integral_rescale_mul_laplacian hR (hφ.1.of_le (by norm_cast)) b⁻¹, integral_rescaledMeasure μ hR0 hb φ]
    exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hb.le)
  · intro x hx hx0
    have hRx0 : (R : ℂ) * x ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hR0) hx0
    have h1 := hobs _ (hmaps hx) hRx0
    rw [greenFunction_ball_zero_dilation hR hρ] at h1
    show -t * greenFunction (ball 0 ρ) 0 x ≤ b⁻¹ * w ((R : ℂ) * x)
    rw [le_inv_mul_iff₀ hb]
    linarith

/-- **The least supersolution scales**: `w̄^{B_ρ}_t[b⁻¹ μ(R ·)](x) = b⁻¹ w̄^{B_{Rρ}}_{bt}[μ](R x)`. -/
theorem leastSupersolution_rescaledMeasure (μ : Measure ℂ) {R b ρ t : ℝ} (hR : 0 < R) (hb : 0 < b) (hρ : 0 < ρ)
    (x : ℂ) :
    leastSupersolution (rescaledMeasure μ R b) ρ 0 t x =
      b⁻¹ * leastSupersolution μ (R * ρ) 0 (b * t) ((R : ℂ) * x) := by
  have hR0 : R ≠ 0 := hR.ne'
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0
  unfold leastSupersolution
  have key : b⁻¹ * sInf ((fun w => w ((R : ℂ) * x)) '' supersolutions μ (R * ρ) 0 (b * t)) =
      sInf (b⁻¹ • ((fun w => w ((R : ℂ) * x)) '' supersolutions μ (R * ρ) 0 (b * t))) := by
    rw [Real.sInf_smul_of_nonneg (inv_nonneg.2 hb.le), smul_eq_mul]
  rw [key]
  congr 1
  ext y
  simp only [mem_image, Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ supersolutions (rescaledMeasure μ R b) (R⁻¹ * (R * ρ)) 0 (b⁻¹ * (b * t)) := by
      rwa [inv_mul_cancel_left₀ hR0, inv_mul_cancel_left₀ hb.ne']
    have hw := rescale_mem_supersolutions (inv_pos.2 hR) (inv_pos.2 hb) (mul_pos hR hρ) hv'
    rw [rescaledMeasure_rescaledMeasure_inv μ hR0 hb] at hw
    refine ⟨_, ⟨_, hw, rfl⟩, ?_⟩
    simp [Complex.ofReal_inv, hRc, hb.ne']
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨_, rescale_mem_supersolutions hR hb hρ hw, rfl⟩

/-- **The clusters scale**: `cluster(b⁻¹ μ(R ·), ρ, 0, t) = R⁻¹ cluster(μ, Rρ, 0, bt)`. -/
theorem cluster_rescaledMeasure (μ : Measure ℂ) {R b ρ t : ℝ} (hR : 0 < R) (hb : 0 < b) (hρ : 0 < ρ) :
    cluster (rescaledMeasure μ R b) ρ 0 t = (fun x : ℂ => (R : ℂ) * x) ⁻¹' cluster μ (R * ρ) 0 (b * t) := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  ext x
  show x ∈ ball (0 : ℂ) ρ ∧ (x = 0 ∨ -t * greenFunction (ball 0 ρ) 0 x <
      leastSupersolution (rescaledMeasure μ R b) ρ 0 t x) ↔
    (R : ℂ) * x ∈ ball (0 : ℂ) (R * ρ) ∧ ((R : ℂ) * x = 0 ∨ -(b * t) * greenFunction (ball 0 (R * ρ)) 0 ((R : ℂ) * x) <
      leastSupersolution μ (R * ρ) 0 (b * t) ((R : ℂ) * x))
  have hball : x ∈ ball (0 : ℂ) ρ ↔ (R : ℂ) * x ∈ ball (0 : ℂ) (R * ρ) := by
    rw [mem_ball_zero_iff, mem_ball_zero_iff, norm_dilation hR]
    exact ⟨fun h => mul_lt_mul_of_pos_left h hR, fun h => lt_of_mul_lt_mul_left h hR.le⟩
  have hzero : x = 0 ↔ (R : ℂ) * x = 0 := by
    rw [mul_eq_zero]
    exact ⟨Or.inr, fun h => h.resolve_left hRc⟩
  have hineq : ∀ G L : ℝ, -t * G < b⁻¹ * L ↔ -(b * t) * G < L := by
    intro G L
    rw [lt_inv_mul_iff₀ hb]
    constructor <;> intro h <;> linarith
  rw [leastSupersolution_rescaledMeasure μ hR hb hρ x, greenFunction_ball_zero_dilation hR hρ]
  exact and_congr hball (or_congr hzero (hineq _ _))

/-- **Weak Laplacians scale**: if `Δw = m` (weakly, on `B_{Rρ}`) then `Δ(b⁻¹ w(R ·)) = b⁻¹ m(R ·)` on `B_ρ`. -/
theorem HasLaplacian.rescale {w : ℂ → ℝ} {m : Measure ℂ} {R b ρ : ℝ} (hR : 0 < R) (hb : 0 < b)
    (h : HasLaplacian w m 0 (ball 0 (R * ρ))) :
    HasLaplacian (fun x => b⁻¹ * w ((R : ℂ) * x)) (rescaledMeasure m R b) 0 (ball 0 ρ) := by
  obtain ⟨hloc, hφ⟩ := h
  refine ⟨locallyIntegrableOn_rescale hR b⁻¹ hloc, fun φ hφt => ?_⟩
  have hψ := isTestFunction_comp_inv_dilation hR hφt
  obtain ⟨hint, -, heq⟩ := hφ _ hψ
  refine ⟨(integrable_rescaledMeasure_iff m hR.ne' hb φ).2 hint, integrable_zero_measure, ?_⟩
  beta_reduce
  rw [integral_rescale_mul_laplacian hR (hφt.1.of_le (by norm_cast)) b⁻¹, heq,
    integral_rescaledMeasure m hR.ne' hb φ]
  simp

/-- **Condition (c) of Theorem 2.3 is preserved by scaling.** -/
theorem SatisfiesObstacleCharacterizationOn.rescale {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {R b T : ℝ}
    (h : SatisfiesObstacleCharacterizationOn μ Λ (b * T)) (hR : 0 < R) (hb : 0 < b) :
    SatisfiesObstacleCharacterizationOn (rescaledMeasure μ R b) (rescaledFamily Λ R b) T := by
  intro t r ht hr hsub ρ hρ
  have hR0 : R ≠ 0 := hR.ne'
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0
  have hρ0 : 0 < ρ := hr.trans hρ
  have hbt : b * t ∈ Ioo 0 (b * T) := ⟨mul_pos hb ht.1, mul_lt_mul_of_pos_left ht.2 hb⟩
  have hsub' : Λ (b * t) ⊆ ball 0 (R * r) := by
    intro y hy
    have hy' : (R : ℂ)⁻¹ * y ∈ rescaledFamily Λ R b t := by
      show (R : ℂ) * ((R : ℂ)⁻¹ * y) ∈ Λ (b * t)
      rwa [mul_inv_cancel_left₀ hRc]
    have h1 := hsub hy'
    rw [mem_ball_zero_iff, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le] at h1
    rw [mem_ball_zero_iff]
    have e : ‖y‖ = R * (R⁻¹ * ‖y‖) := by field_simp
    rw [e]
    exact mul_lt_mul_of_pos_left h1 hR
  obtain ⟨h1, h2, h3, h4⟩ := h (b * t) (R * r) hbt (mul_pos hR hr) hsub' (R * ρ) (mul_lt_mul_of_pos_left hρ hR)
  have hlsup : leastSupersolution (rescaledMeasure μ R b) ρ 0 t =
      fun x => b⁻¹ * leastSupersolution μ (R * ρ) 0 (b * t) ((R : ℂ) * x) :=
    funext fun x => leastSupersolution_rescaledMeasure μ hR hb hρ0 x
  have hmaps : MapsTo (fun x : ℂ => (R : ℂ) * x) (closedBall 0 ρ) (closedBall 0 (R * ρ)) := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    rw [norm_dilation hR]
    exact mul_le_mul_of_nonneg_left hx hR.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cluster_rescaledMeasure μ hR hb hρ0]
    show dilation R hR0 ⁻¹' Λ (b * t) = interior (closure (dilation R hR0 ⁻¹' cluster μ (R * ρ) 0 (b * t)))
    rw [← (dilation R hR0).preimage_closure, ← (dilation R hR0).preimage_interior, ← h1]
  · rw [hlsup]
    exact continuousOn_const.mul (h2.comp (continuous_const.mul continuous_id).continuousOn hmaps)
  · rw [hlsup, show rescaledFamily Λ R b t = (fun x => (R : ℂ) * x) ⁻¹' Λ (b * t) from rfl,
      rescaledMeasure_restrict μ hR0 b]
    exact HasLaplacian.rescale hR hb h3
  · intro x hx
    rw [hlsup]
    have hRx : (R : ℂ) * x ∈ sphere (0 : ℂ) (R * ρ) := by
      rw [mem_sphere_zero_iff_norm, norm_dilation hR, mem_sphere_zero_iff_norm.1 hx]
    simp [h4 _ hRx]

/-- **Scaling of harmonic balls** (the deterministic step `ConeHarmonicBallFamilyOnScalingStep`, line 582): if
`{Λ_t}_{0 < t < bT}` is a family of harmonic balls for `μ` with the properties of Theorem 2.3, then
`{R⁻¹ Λ_{bt}}_{0 < t < T}` is one for `b⁻¹ μ(R ·)`. -/
theorem coneHarmonicBallFamilyOnScalingStep : ConeHarmonicBallFamilyOnScalingStep := by
  intro μ Λ R b T hR hb h
  exact ⟨fun t ht => IsHarmonicBall.rescale (h.1 (b * t) ⟨mul_pos hb ht.1, mul_lt_mul_of_pos_left ht.2 hb⟩) hR hb,
    SatisfiesHarmonicBallConditionsOn.rescale h.2.1 hR hb, h.2.2.rescale hR hb⟩

end MatedCRT
