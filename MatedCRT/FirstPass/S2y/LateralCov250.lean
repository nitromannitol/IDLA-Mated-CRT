import MatedCRT.Proofs.Field.WholePlaneLateralCov
import MatedCRT.Proofs.Measurability.ConePairing
import HarmonicBalls.FirstPass.S11c.ShiftObs11_7
import HarmonicBalls.FirstPass.S11i.LogPotentialFubini
import HarmonicBalls.FirstPass.S11i.DilationMixing

/-!
# The lateral covariance kernel and Fubini for the lateral pairing

The lateral covariance kernel is `K_L(x,y) = wholePlaneCov x y - radialCov ‖x‖ ‖y‖`, which equals
`log (max ‖x‖ ‖y‖) - log ‖x - y‖` off the diagonal (Duplantier-Sheffield, arXiv:1409.7055, Section 3.1). This file
proves: the kernel is integrable against products of test functions, and Fubini for `E[X · ∫ g(y) A(y) dy]`.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology Real Metric HarmonicBalls
open scoped ENNReal

namespace MatedCRT.LQGMeasure

section Kernel

/-- The lateral covariance kernel `K_L(x,y) = wholePlaneCov x y - radialCov ‖x‖ ‖y‖`. -/
noncomputable def latKernel (x y : ℂ) : ℝ :=
  wholePlaneCov x y - MatedCRT.Field.ConeRadial.radialCov ‖x‖ ‖y‖

/-- Off the diagonal, `K_L(x,y) = log max(‖x‖,‖y‖) - log ‖x - y‖`. -/
lemma latKernel_eq {x y : ℂ} (hxy : x ≠ y) :
    latKernel x y = Real.log (max ‖x‖ ‖y‖) - Real.log ‖x - y‖ := by
  have h1 : 0 < max ‖x‖ 1 := lt_max_of_lt_right one_pos
  have h2 : 0 < max ‖y‖ 1 := lt_max_of_lt_right one_pos
  have h3 : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  unfold latKernel wholePlaneCov MatedCRT.Field.ConeRadial.radialCov
  rw [Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']
  ring

/-- The diagonal is Lebesgue-null in `ℂ × ℂ`. -/
lemma diag_null : (volume.prod volume : Measure (ℂ × ℂ)) {p : ℂ × ℂ | p.1 = p.2} = 0 := by
  have hm : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} := measurableSet_eq_fun measurable_fst measurable_snd
  rw [Measure.measure_prod_null hm]
  refine Eventually.of_forall fun x => ?_
  have : Prod.mk x ⁻¹' {p : ℂ × ℂ | p.1 = p.2} = {x} := by
    ext y; simp [eq_comm]
  simp [this]

lemma exists_radius {f : ℂ → ℝ} (hf : IsTestFunction univ f) : ∃ R : ℝ, ∀ x, f x ≠ 0 → ‖x‖ ≤ R := by
  obtain ⟨R, hR⟩ := hf.2.1.isCompact.isBounded.subset_closedBall (0 : ℂ)
  exact ⟨R, fun x hx => by simpa using hR (subset_tsupport f hx)⟩

lemma integrable_mul_log_norm {f : ℂ → ℝ} (hf : IsTestFunction univ f) :
    Integrable (fun x => f x * Real.log ‖x‖) := by
  simpa using HarmonicBalls.S11c.integrable_mul_logNorm_sub hf 0

lemma abs_log_max_le (a b : ℝ) : |Real.log (max a b)| ≤ |Real.log a| + |Real.log b| := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; linarith [abs_nonneg (Real.log a)]
  · rw [max_eq_left h]; linarith [abs_nonneg (Real.log b)]

lemma integrable_prod_mul_log_max {f g : ℂ → ℝ} (hf : IsTestFunction univ f) (hg : IsTestFunction univ g) :
    Integrable (fun p : ℂ × ℂ => f p.1 * g p.2 * Real.log (max ‖p.1‖ ‖p.2‖)) (volume.prod volume) := by
  have hfm : Measurable f := hf.1.continuous.measurable
  have hgm : Measurable g := hg.1.continuous.measurable
  have hf0 : Integrable f := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
  have hg0 : Integrable g := hg.1.continuous.integrable_of_hasCompactSupport hg.2.1
  have hf1 := (integrable_mul_log_norm hf).norm
  have hg1 := (integrable_mul_log_norm hg).norm
  have hB : Integrable (fun p : ℂ × ℂ => ‖f p.1 * Real.log ‖p.1‖‖ * ‖g p.2‖ +
      ‖f p.1‖ * ‖g p.2 * Real.log ‖p.2‖‖) (volume.prod volume) :=
    (Integrable.mul_prod hf1 hg0.norm).add (Integrable.mul_prod hf0.norm hg1)
  refine hB.mono' ?_ ?_
  · fun_prop
  · refine Eventually.of_forall fun p => ?_
    have h := abs_log_max_le ‖p.1‖ ‖p.2‖
    simp only [Real.norm_eq_abs, abs_mul]
    have hf0' := abs_nonneg (f p.1)
    have hg0' := abs_nonneg (g p.2)
    nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg hf0' hg0')]

/-- The lateral kernel is integrable against a product of two test functions. -/
lemma integrable_prod_latKernel {f g : ℂ → ℝ} (hf : IsTestFunction univ f) (hg : IsTestFunction univ g) :
    Integrable (fun p : ℂ × ℂ => f p.1 * g p.2 * latKernel p.1 p.2) (volume.prod volume) := by
  obtain ⟨R₁, hR₁⟩ := exists_radius hf
  obtain ⟨R₂, hR₂⟩ := exists_radius hg
  have hlog : Integrable (fun p : ℂ × ℂ => f p.1 * g p.2 * Real.log ‖p.1 - p.2‖) (volume.prod volume) := by
    have h := integrable_uncurry_mul_logPotential hf hg (R := max R₁ R₂) (c := 1)
      (fun x hx => (hR₁ x hx).trans (le_max_left _ _)) (fun z hz => (hR₂ z hz).trans (le_max_right _ _))
      zero_le_one le_rfl
    refine h.congr (Eventually.of_forall fun p => ?_)
    simp [Function.uncurry, one_smul, mul_assoc]
  have hA := (integrable_prod_mul_log_max hf hg).sub hlog
  refine hA.congr ?_
  have hae : ∀ᵐ p ∂(volume.prod volume : Measure (ℂ × ℂ)), p.1 ≠ p.2 := by
    rw [ae_iff]; simpa using diag_null
  filter_upwards [hae] with p hp
  simp only [Pi.sub_apply]
  rw [latKernel_eq hp]
  ring

end Kernel

section Fubini

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Fubini for `E[X · ∫ g(y) A_ω(y) dy] = ∫ g(y) E[X A_·(y)] dy`, for a jointly measurable family `A ω y`, a square
integrable `X`, a test function `g` supported in `closedBall 0 R`, and the integrability of `y ↦ E[A(y)²]` on the ball. -/
lemma integral_mul_integral_swap [IsProbabilityMeasure P] {A : Ω → ℂ → ℝ}
    (hAm : Measurable (fun p : Ω × ℂ => A p.1 p.2)) {X : Ω → ℝ} (hX : MemLp X 2 P)
    {g : ℂ → ℝ} (hg : IsTestFunction univ g) {R : ℝ} (hgR : ∀ y, g y ≠ 0 → ‖y‖ ≤ R)
    (hAL2 : ∀ᵐ y ∂(volume.restrict (closedBall (0 : ℂ) R)), MemLp (fun ω => A ω y) 2 P)
    (hAint : IntegrableOn (fun y => ∫ ω, (A ω y) ^ 2 ∂P) (closedBall (0 : ℂ) R)) :
    ∫ ω, X ω * (∫ y, g y * A ω y) ∂P = ∫ y, g y * (∫ ω, X ω * A ω y ∂P) := by
  obtain ⟨C, hC⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2.1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set B := closedBall (0 : ℂ) R with hBdef
  have hBm : MeasurableSet B := measurableSet_closedBall
  set ind : ℂ → ℝ := B.indicator fun _ => (1 : ℝ) with hind_def
  have hind : Integrable ind volume := (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator hBm
  have hX2 : Integrable (fun ω => X ω ^ 2) P := hX.integrable_sq
  -- the square term `ind(y) A_ω(y)²` is integrable on the product
  have hH : Integrable (fun p : Ω × ℂ => ind p.2 * A p.1 p.2 ^ 2) (P.prod (volume : Measure ℂ)) := by
    have hHm : Measurable (fun p : Ω × ℂ => ind p.2 * A p.1 p.2 ^ 2) :=
      ((measurable_const.indicator hBm).comp measurable_snd).mul (hAm.pow_const 2)
    refine (integrable_prod_iff' hHm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · have h1 : ∀ᵐ y ∂(volume : Measure ℂ), y ∈ B → Integrable (fun ω => ind y * A ω y ^ 2) P := by
        rw [← ae_restrict_iff' hBm]
        filter_upwards [hAL2, ae_restrict_mem hBm] with y hy hyB
        have hy2 := hy.integrable_sq
        refine (hy2.const_mul 1).congr (Eventually.of_forall fun ω => ?_)
        simp [hind_def, Set.indicator_of_mem hyB]
      filter_upwards [h1] with y hy
      by_cases hyB : y ∈ B
      · exact hy hyB
      · have : (fun ω => ind y * A ω y ^ 2) = fun _ => 0 := by
          funext ω; simp [hind_def, Set.indicator_of_notMem hyB]
        rw [this]; exact integrable_zero _ _ _
    · refine ((integrable_indicator_iff hBm).2 hAint).congr (Eventually.of_forall fun y => ?_)
      by_cases hyB : y ∈ B
      · simp [hind_def, Set.indicator_of_mem hyB, Real.norm_eq_abs, sq_abs]
      · simp [hind_def, Set.indicator_of_notMem hyB]
  -- the joint integrability of the integrand `X(ω) g(y) A_ω(y)`
  have hFint : Integrable (fun p : Ω × ℂ => X p.1 * (g p.2 * A p.1 p.2)) (P.prod (volume : Measure ℂ)) := by
    have hG : Integrable (fun p : Ω × ℂ => (C / 2) * (X p.1 ^ 2 * ind p.2) + (C / 2) * (ind p.2 * A p.1 p.2 ^ 2))
        (P.prod (volume : Measure ℂ)) :=
      ((Integrable.mul_prod hX2 hind).const_mul (C / 2)).add (hH.const_mul (C / 2))
    refine hG.mono' ?_ ?_
    · have hgm : Measurable g := hg.1.continuous.measurable
      have hXm' : AEStronglyMeasurable (fun p : Ω × ℂ => X p.1) (P.prod (volume : Measure ℂ)) :=
        hX.aestronglyMeasurable.comp_fst
      exact hXm'.mul (((hgm.comp measurable_snd).mul hAm).aestronglyMeasurable)
    · refine Eventually.of_forall fun p => ?_
      obtain ⟨ω, y⟩ := p
      by_cases hyB : y ∈ B
      · have hgC : |g y| ≤ C := by simpa using hC y
        simp only [hind_def, Set.indicator_of_mem hyB, Real.norm_eq_abs, abs_mul]
        nlinarith [mul_le_mul_of_nonneg_right hgC (mul_nonneg (abs_nonneg (X ω)) (abs_nonneg (A ω y))),
          mul_nonneg hC0 (sq_nonneg (|X ω| - |A ω y|)), sq_abs (X ω), sq_abs (A ω y)]
      · have hgy : g y = 0 := by
          by_contra hne; exact hyB (by simpa [B] using hgR y hne)
        simp [hind_def, Set.indicator_of_notMem hyB, hgy]
  calc ∫ ω, X ω * (∫ y, g y * A ω y) ∂P
      = ∫ ω, (∫ y, X ω * (g y * A ω y)) ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        exact (integral_const_mul (X ω) _).symm
    _ = ∫ y, ∫ ω, X ω * (g y * A ω y) ∂P := integral_integral_swap hFint
    _ = ∫ y, g y * (∫ ω, X ω * A ω y ∂P) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        have : ∀ ω, X ω * (g y * A ω y) = g y * (X ω * A ω y) := fun ω => by ring
        simp_rw [this]
        exact integral_const_mul _ _

end Fubini

end MatedCRT.LQGMeasure
