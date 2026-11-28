import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1PosProof
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGP
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgKolm
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGDimension.LFPP.SegCombLaw
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreFM
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Mixing of the normalized dilation of the whole-plane GFF modulo `2πχ`

`IGFieldDilationMixing` (`ZeroConeLemmaA1PosProof.lean`) states that for a whole-plane GFF `h` normalized by
`h_1(0) = 0` and an independent uniform phase `u` on `[0, 2πχ)`, the normalized dilation by `2` of the law of the
circle-average array `(ρ, w) ↦ u + h_ρ(w)` is mixing (the whole-plane GFF analogue of Lemma A.1 in Remark A.2 of
Gwynne–Miller–Sheffield, arXiv:1705.11161; the written argument).

The proof (`igFieldDilationMixing`).
* Mixing on all measurable sets follows from mixing on the measurable cylinders, which form a generating ring of
  sets (`tendsto_measure_inter_preimage_of_isSetRing`).
* A cylinder over finitely many indices is an event for the phase coordinate `f(1, 0)` and the increments
  `f(x) − f(1, 0)` (`igMixCoord`). On the array of `(h, u)` these are `u + h_1(0)` and the circle-average
  increments `h_x − h_1(0)`; after `n` normalized dilations they are `u + h_{2^n}(0)` modulo `2πχ` and the
  increments `h_{2^n x} − h_{2^n}(0)` (`exists_igMixCoord_iterate`).
* Characters `exp(i(σ a + ⟨s, b⟩))` of the first vector and `exp(i(2π m a'/(2πχ) + ⟨t, b'⟩))`, `m ∈ ℤ`, of the
  second have asymptotically uncorrelated values (`tendsto_igMix_char`): integrating the independent uniform phase
  factors the expectation (`integral_cexp_phase_add_inGSpan`); for `m = 0` the covariances of `h_x − h_1(0)` and
  `h_{2^n y} − h_{2^n}(0)` tend to `0` (Newton's theorem, `tendsto_incCov_scale`), and for `m ≠ 0` the variance
  `n log 2` of `h_{2^n}(0)` makes the Gaussian characteristic function tend to `0`.
* The characters are the exponential monomials of a torus (phase modulo `2πχ`, increments modulo `2L`) whose span
  is uniformly dense; bounded measurable functions are approximated in `L¹` of the fixed laws, which gives the
  convergence for all events of the torus (`tendsto_igMixCorr_indicator_of_dense`); the cylinder events agree with
  torus events outside a box of small probability (`tendsto_igMix_cyl`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal symmDiff

namespace MatedCRT

/-! ### Mixing from a generating ring of sets -/

section AbstractMixing

variable {α : Type*} [mα : MeasurableSpace α] {μ : Measure α}

theorem abs_measureReal_inter_preimage_sub_le [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) (n : ℕ) {S₁ S₂ A B : Set α} (hS₁ : MeasurableSet S₁)
    (hS₂ : MeasurableSet S₂) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |μ.real (S₁ ∩ T^[n] ⁻¹' S₂) - μ.real (A ∩ T^[n] ⁻¹' B)| ≤
      μ.real (A ∆ S₁) + μ.real (B ∆ S₂) := by
  have hS : MeasurePreserving T^[n] μ μ := hT.iterate n
  have hpre : μ.real (T^[n] ⁻¹' (B ∆ S₂)) = μ.real (B ∆ S₂) := by
    simp only [measureReal_def]
    rw [hS.measure_preimage (hB.symmDiff hS₂).nullMeasurableSet]
  calc |μ.real (S₁ ∩ T^[n] ⁻¹' S₂) - μ.real (A ∩ T^[n] ⁻¹' B)|
      ≤ μ.real ((S₁ ∩ T^[n] ⁻¹' S₂) ∆ (A ∩ T^[n] ⁻¹' B)) :=
        abs_measureReal_sub_le_measureReal_symmDiff
          (hS₁.inter (hS.measurable hS₂)).nullMeasurableSet
          (hA.inter (hS.measurable hB)).nullMeasurableSet
    _ ≤ μ.real ((A ∆ S₁) ∪ T^[n] ⁻¹' (B ∆ S₂)) := by
        refine measureReal_mono ?_
        intro x hx
        simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_union] at hx ⊢
        tauto
    _ ≤ μ.real (A ∆ S₁) + μ.real (T^[n] ⁻¹' (B ∆ S₂)) := measureReal_union_le _ _
    _ = μ.real (A ∆ S₁) + μ.real (B ∆ S₂) := by rw [hpre]

/-- **Mixing on a generating ring of sets implies mixing** (Walters, *An introduction to ergodic theory*,
Theorem 1.17): if `T` preserves the probability measure `μ`, the ring of sets `C` generates the σ-algebra and covers
the space up to a null set, and `μ(A ∩ T^{-n} B) → μ(A) μ(B)` for `A, B ∈ C`, then the same holds for all
measurable sets. -/
theorem tendsto_measure_inter_preimage_of_isSetRing [IsProbabilityMeasure μ] {C : Set (Set α)}
    (hC : IsSetRing C) (hcov : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0)
    (hgen : mα = MeasurableSpace.generateFrom C) {T : α → α} (hT : MeasurePreserving T μ μ)
    (hmix : ∀ A ∈ C, ∀ B ∈ C,
      Tendsto (fun n : ℕ => μ.real (A ∩ T^[n] ⁻¹' B)) atTop (𝓝 (μ.real A * μ.real B)))
    {S₁ S₂ : Set α} (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂) :
    Tendsto (fun n : ℕ => μ (S₁ ∩ T^[n] ⁻¹' S₂)) atTop (𝓝 (μ S₁ * μ S₂)) := by
  have hmeasC : ∀ B ∈ C, MeasurableSet B := fun B hB => by
    have : MeasurableSet[MeasurableSpace.generateFrom C] B :=
      MeasurableSpace.measurableSet_generateFrom hB
    rwa [← hgen] at this
  have hreal : Tendsto (fun n : ℕ => μ.real (S₁ ∩ T^[n] ⁻¹' S₂)) atTop
      (𝓝 (μ.real S₁ * μ.real S₂)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < ε / 8 := by positivity
    obtain ⟨A, hAC, hA⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC hcov hgen hS₁
      (ENNReal.ofReal_pos.2 hδ)
    obtain ⟨B, hBC, hB⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC hcov hgen hS₂
      (ENNReal.ofReal_pos.2 hδ)
    have hAm := hmeasC A hAC
    have hBm := hmeasC B hBC
    have hdA : μ.real (A ∆ S₁) < ε / 8 := ENNReal.toReal_lt_of_lt_ofReal hA
    have hdB : μ.real (B ∆ S₂) < ε / 8 := ENNReal.toReal_lt_of_lt_ofReal hB
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hmix A hAC B hBC) (ε / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := abs_measureReal_inter_preimage_sub_le hT n hS₁ hS₂ hAm hBm
    have h2A : |μ.real A - μ.real S₁| ≤ μ.real (A ∆ S₁) :=
      abs_measureReal_sub_le_measureReal_symmDiff hAm.nullMeasurableSet hS₁.nullMeasurableSet
    have h2B : |μ.real B - μ.real S₂| ≤ μ.real (B ∆ S₂) :=
      abs_measureReal_sub_le_measureReal_symmDiff hBm.nullMeasurableSet hS₂.nullMeasurableSet
    have h4 : |μ.real A * μ.real B - μ.real S₁ * μ.real S₂| ≤ μ.real (A ∆ S₁) + μ.real (B ∆ S₂) := by
      have e : μ.real A * μ.real B - μ.real S₁ * μ.real S₂ =
          (μ.real A - μ.real S₁) * μ.real B + μ.real S₁ * (μ.real B - μ.real S₂) := by ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg measureReal_nonneg]
        calc |μ.real A - μ.real S₁| * μ.real B ≤ |μ.real A - μ.real S₁| * 1 :=
              mul_le_mul_of_nonneg_left measureReal_le_one (abs_nonneg _)
          _ ≤ μ.real (A ∆ S₁) := by rw [mul_one]; exact h2A
      · rw [abs_mul, abs_of_nonneg measureReal_nonneg]
        calc μ.real S₁ * |μ.real B - μ.real S₂| ≤ 1 * |μ.real B - μ.real S₂| :=
              mul_le_mul_of_nonneg_right measureReal_le_one (abs_nonneg _)
          _ ≤ μ.real (B ∆ S₂) := by rw [one_mul]; exact h2B
    have hNn := hN n hn
    rw [Real.dist_eq] at hNn ⊢
    have t1 := abs_sub_le (μ.real (S₁ ∩ T^[n] ⁻¹' S₂)) (μ.real (A ∩ T^[n] ⁻¹' B))
      (μ.real S₁ * μ.real S₂)
    have t2 := abs_sub_le (μ.real (A ∩ T^[n] ⁻¹' B)) (μ.real A * μ.real B) (μ.real S₁ * μ.real S₂)
    linarith
  have hfin : ∀ n : ℕ, μ (S₁ ∩ T^[n] ⁻¹' S₂) ≠ ∞ := fun n => measure_ne_top _ _
  rw [← ENNReal.tendsto_toReal_iff hfin
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]
  simpa only [measureReal_def, ENNReal.toReal_mul] using hreal

end AbstractMixing

/-! ### Correlations along a sequence of random elements with a fixed law -/

section Corr

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The correlation sequence `E[f(Ξ) g(Υₙ)] − E[f(Ξ)] E[g(Υₙ)]`. -/
def igMixCorr {E₁ E₂ : Type*} (P : Measure Ω) (Ξ : Ω → E₁) (Υ : ℕ → Ω → E₂) (f : E₁ → ℂ)
    (g : E₂ → ℂ) (n : ℕ) : ℂ :=
  ∫ ω, f (Ξ ω) * g (Υ n ω) ∂P - (∫ ω, f (Ξ ω) ∂P) * ∫ ω, g (Υ n ω) ∂P

variable {E₁ E₂ : Type*} [MeasurableSpace E₁] [MeasurableSpace E₂]

theorem integrable_comp_of_norm_le [IsFiniteMeasure P] {E : Type*} [MeasurableSpace E] {Ξ : Ω → E}
    (hΞ : Measurable Ξ) {f : E → ℂ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    Integrable (fun ω => f (Ξ ω)) P :=
  Integrable.of_bound (hf.comp hΞ).aestronglyMeasurable C (Eventually.of_forall fun _ => hC _)

theorem integrable_comp_mul_of_norm_le [IsFiniteMeasure P] {Ξ : Ω → E₁} {Υ : Ω → E₂}
    (hΞ : Measurable Ξ) (hΥ : Measurable Υ) {f : E₁ → ℂ} {g : E₂ → ℂ} (hf : Measurable f)
    (hg : Measurable g) {Cf Cg : ℝ} (hfC : ∀ y, ‖f y‖ ≤ Cf) (hgC : ∀ y, ‖g y‖ ≤ Cg) :
    Integrable (fun ω => f (Ξ ω) * g (Υ ω)) P := by
  refine Integrable.of_bound ((hf.comp hΞ).mul (hg.comp hΥ)).aestronglyMeasurable (Cf * Cg)
    (Eventually.of_forall fun ω => ?_)
  have h1 := hfC (Ξ ω)
  have h2 := hgC (Υ ω)
  show ‖f (Ξ ω) * g (Υ ω)‖ ≤ Cf * Cg
  rw [norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

omit [MeasurableSpace E₂] in
/-- Bound of the correlation by the `L¹` norm of the first function. -/
theorem norm_igMixCorr_le_left [IsProbabilityMeasure P] {Ξ : Ω → E₁} (Υ : ℕ → Ω → E₂)
    (hΞ : Measurable Ξ) {f : E₁ → ℂ} {g : E₂ → ℂ}
    (hf : Measurable f) {Cf Cg : ℝ} (hfC : ∀ y, ‖f y‖ ≤ Cf)
    (hgC : ∀ y, ‖g y‖ ≤ Cg) (n : ℕ) :
    ‖igMixCorr P Ξ Υ f g n‖ ≤ 2 * Cg * ∫ y, ‖f y‖ ∂(P.map Ξ) := by
  have hfΞ := integrable_comp_of_norm_le (P := P) hΞ hf hfC
  have hmap : ∫ y, ‖f y‖ ∂(P.map Ξ) = ∫ ω, ‖f (Ξ ω)‖ ∂P :=
    integral_map hΞ.aemeasurable hf.norm.aestronglyMeasurable
  rw [hmap]
  have h1 : ‖∫ ω, f (Ξ ω) * g (Υ n ω) ∂P‖ ≤ ∫ ω, Cg * ‖f (Ξ ω)‖ ∂P := by
    refine norm_integral_le_of_norm_le (hfΞ.norm.const_mul Cg) (Eventually.of_forall fun ω => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hgC _) (norm_nonneg _)
  rw [integral_const_mul] at h1
  have h2 : ‖∫ ω, g (Υ n ω) ∂P‖ ≤ Cg := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => g (Υ n ω)) (C := Cg)
      (Eventually.of_forall fun ω => hgC _)
    simpa using this
  have h3 : ‖∫ ω, f (Ξ ω) ∂P‖ ≤ ∫ ω, ‖f (Ξ ω)‖ ∂P := norm_integral_le_integral_norm _
  have h0 : 0 ≤ ∫ ω, ‖f (Ξ ω)‖ ∂P := integral_nonneg fun _ => norm_nonneg _
  unfold igMixCorr
  calc ‖∫ ω, f (Ξ ω) * g (Υ n ω) ∂P - (∫ ω, f (Ξ ω) ∂P) * ∫ ω, g (Υ n ω) ∂P‖
      ≤ ‖∫ ω, f (Ξ ω) * g (Υ n ω) ∂P‖ + ‖(∫ ω, f (Ξ ω) ∂P) * ∫ ω, g (Υ n ω) ∂P‖ := norm_sub_le _ _
    _ ≤ Cg * ∫ ω, ‖f (Ξ ω)‖ ∂P + (∫ ω, ‖f (Ξ ω)‖ ∂P) * Cg := by
        refine add_le_add h1 ?_
        rw [norm_mul]
        exact mul_le_mul h3 h2 (norm_nonneg _) h0
    _ = 2 * Cg * ∫ ω, ‖f (Ξ ω)‖ ∂P := by ring

omit [MeasurableSpace E₁] in
/-- Bound of the correlation by the `L¹` norm of the second function. -/
theorem norm_igMixCorr_le_right [IsProbabilityMeasure P] (Ξ : Ω → E₁) {Υ : ℕ → Ω → E₂}
    (hΥ : ∀ n, Measurable (Υ n)) {f : E₁ → ℂ} {g : E₂ → ℂ}
    (hg : Measurable g) {Cf Cg : ℝ} (hfC : ∀ y, ‖f y‖ ≤ Cf)
    (hgC : ∀ y, ‖g y‖ ≤ Cg) (hCf : 0 ≤ Cf) (n : ℕ) :
    ‖igMixCorr P Ξ Υ f g n‖ ≤ 2 * Cf * ∫ y, ‖g y‖ ∂(P.map (Υ n)) := by
  have hgΥ := integrable_comp_of_norm_le (P := P) (hΥ n) hg hgC
  have hmap : ∫ y, ‖g y‖ ∂(P.map (Υ n)) = ∫ ω, ‖g (Υ n ω)‖ ∂P :=
    integral_map (hΥ n).aemeasurable hg.norm.aestronglyMeasurable
  rw [hmap]
  have h1 : ‖∫ ω, f (Ξ ω) * g (Υ n ω) ∂P‖ ≤ ∫ ω, Cf * ‖g (Υ n ω)‖ ∂P := by
    refine norm_integral_le_of_norm_le (hgΥ.norm.const_mul Cf) (Eventually.of_forall fun ω => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hfC _) (norm_nonneg _)
  rw [integral_const_mul] at h1
  have h2 : ‖∫ ω, f (Ξ ω) ∂P‖ ≤ Cf := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => f (Ξ ω)) (C := Cf)
      (Eventually.of_forall fun ω => hfC _)
    simpa using this
  have h3 : ‖∫ ω, g (Υ n ω) ∂P‖ ≤ ∫ ω, ‖g (Υ n ω)‖ ∂P := norm_integral_le_integral_norm _
  unfold igMixCorr
  calc ‖∫ ω, f (Ξ ω) * g (Υ n ω) ∂P - (∫ ω, f (Ξ ω) ∂P) * ∫ ω, g (Υ n ω) ∂P‖
      ≤ ‖∫ ω, f (Ξ ω) * g (Υ n ω) ∂P‖ + ‖(∫ ω, f (Ξ ω) ∂P) * ∫ ω, g (Υ n ω) ∂P‖ := norm_sub_le _ _
    _ ≤ Cf * ∫ ω, ‖g (Υ n ω)‖ ∂P + Cf * ∫ ω, ‖g (Υ n ω)‖ ∂P := by
        refine add_le_add h1 ?_
        rw [norm_mul]
        exact mul_le_mul h2 h3 (norm_nonneg _) hCf
    _ = 2 * Cf * ∫ ω, ‖g (Υ n ω)‖ ∂P := by ring

/-- Bilinearity of the correlation. -/
theorem igMixCorr_sub_sub [IsFiniteMeasure P] {Ξ : Ω → E₁} {Υ : ℕ → Ω → E₂}
    (hΞ : Measurable Ξ) (hΥ : ∀ n, Measurable (Υ n)) {f f' : E₁ → ℂ} {g g' : E₂ → ℂ}
    (hf : Measurable f) (hf' : Measurable f') (hg : Measurable g) (hg' : Measurable g')
    {Cf Cf' Cg Cg' : ℝ} (hfC : ∀ y, ‖f y‖ ≤ Cf) (hf'C : ∀ y, ‖f' y‖ ≤ Cf') (hgC : ∀ y, ‖g y‖ ≤ Cg)
    (hg'C : ∀ y, ‖g' y‖ ≤ Cg') (n : ℕ) :
    igMixCorr P Ξ Υ f g n - igMixCorr P Ξ Υ f' g' n =
      igMixCorr P Ξ Υ (f - f') g n + igMixCorr P Ξ Υ f' (g - g') n := by
  have iF := integrable_comp_of_norm_le (P := P) hΞ hf hfC
  have iF' := integrable_comp_of_norm_le (P := P) hΞ hf' hf'C
  have iG := integrable_comp_of_norm_le (P := P) (hΥ n) hg hgC
  have iG' := integrable_comp_of_norm_le (P := P) (hΥ n) hg' hg'C
  have iFG := integrable_comp_mul_of_norm_le (P := P) hΞ (hΥ n) hf hg hfC hgC
  have iF'G := integrable_comp_mul_of_norm_le (P := P) hΞ (hΥ n) hf' hg hf'C hgC
  have iF'G' := integrable_comp_mul_of_norm_le (P := P) hΞ (hΥ n) hf' hg' hf'C hg'C
  simp only [igMixCorr, Pi.sub_apply, sub_mul, mul_sub]
  rw [integral_sub iFG iF'G, integral_sub iF iF', integral_sub iF'G iF'G', integral_sub iG iG']
  ring

theorem igMixCorr_indicator [IsFiniteMeasure P] {Ξ : Ω → E₁} {Υ : ℕ → Ω → E₂}
    (hΞ : Measurable Ξ) (hΥ : ∀ n, Measurable (Υ n)) {A : Set E₁} {B : Set E₂}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    igMixCorr P Ξ Υ (A.indicator 1) (B.indicator 1) n =
      ((P.real (Ξ ⁻¹' A ∩ Υ n ⁻¹' B) - P.real (Ξ ⁻¹' A) * P.real (Υ n ⁻¹' B) : ℝ) : ℂ) := by
  have key : ∀ S : Set Ω, MeasurableSet S →
      ∫ ω, S.indicator (fun _ => (1 : ℂ)) ω ∂P = (P.real S : ℂ) := fun S hS => by
    rw [integral_indicator hS, setIntegral_const, Complex.real_smul, mul_one]
  have e1 : (fun ω => A.indicator (1 : E₁ → ℂ) (Ξ ω) * B.indicator (1 : E₂ → ℂ) (Υ n ω)) =
      (Ξ ⁻¹' A ∩ Υ n ⁻¹' B).indicator (fun _ => (1 : ℂ)) := by
    funext ω
    by_cases h1 : Ξ ω ∈ A <;> by_cases h2 : Υ n ω ∈ B <;>
      simp [h1, h2]
  have e2 : (fun ω => A.indicator (1 : E₁ → ℂ) (Ξ ω)) = (Ξ ⁻¹' A).indicator (fun _ => (1 : ℂ)) := by
    funext ω
    by_cases h1 : Ξ ω ∈ A <;> simp [h1]
  have e3 : (fun ω => B.indicator (1 : E₂ → ℂ) (Υ n ω)) =
      (Υ n ⁻¹' B).indicator (fun _ => (1 : ℂ)) := by
    funext ω
    by_cases h2 : Υ n ω ∈ B <;> simp [h2]
  simp only [igMixCorr]
  rw [e1, e2, e3, key _ ((hΞ hA).inter (hΥ n hB)), key _ (hΞ hA), key _ (hΥ n hB)]
  push_cast
  ring

end Corr

/-! ### Dense families of continuous functions on compact spaces -/

section Dense

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem abs_sub_clamp_le {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |a - max 0 (min 1 b)| ≤ |a - b| := by
  rcases le_total b 0 with hb | hb
  · rw [min_eq_right (hb.trans zero_le_one), max_eq_left hb, sub_zero, abs_of_nonneg ha0,
      abs_of_nonneg (by linarith)]
    linarith
  · rcases le_total b 1 with hb1 | hb1
    · rw [min_eq_right hb1, max_eq_right hb]
    · rw [min_eq_left hb1, max_eq_right zero_le_one, abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]
      linarith

/-- An indicator function is approximated in `L¹` by an element of a dense subspace of continuous functions
bounded by `2`. -/
theorem exists_mem_integral_norm_indicator_sub_le {𝕋 : Type*} [TopologicalSpace 𝕋] [CompactSpace 𝕋]
    [TopologicalSpace.MetrizableSpace 𝕋] [MeasurableSpace 𝕋] [BorelSpace 𝕋]
    {D : Submodule ℂ C(𝕋, ℂ)} (hD : D.topologicalClosure = ⊤) (ν : Measure 𝕋)
    [IsProbabilityMeasure ν] {A : Set 𝕋} (hA : MeasurableSet A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p ∈ D, (∀ y, ‖p y‖ ≤ 2) ∧ ∫ y, ‖A.indicator (1 : 𝕋 → ℂ) y - p y‖ ∂ν ≤ 2 * δ := by
  have hF : Measurable (A.indicator (1 : 𝕋 → ℝ)) := measurable_one.indicator hA
  have hF01 : ∀ y, 0 ≤ A.indicator (1 : 𝕋 → ℝ) y ∧ A.indicator (1 : 𝕋 → ℝ) y ≤ 1 := fun y => by
    by_cases hy : y ∈ A <;> simp [hy]
  have hFb : ∀ y, |A.indicator (1 : 𝕋 → ℝ) y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (hF01 y).1]; exact (hF01 y).2
  obtain ⟨g, hg⟩ := LQGMetric.DFGPS.L217.exists_boundedContinuous_integral_abs_sub_le ν hF hFb hδ
  let g' : C(𝕋, ℂ) := ⟨fun y => ((max 0 (min 1 (g y)) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.min g.continuous))⟩
  have hg'apply : ∀ y, g' y = ((max 0 (min 1 (g y)) : ℝ) : ℂ) := fun _ => rfl
  have hcast : ∀ y, A.indicator (1 : 𝕋 → ℂ) y = ((A.indicator (1 : 𝕋 → ℝ) y : ℝ) : ℂ) := fun y => by
    by_cases hy : y ∈ A <;> simp [hy]
  have hg'le : ∀ y, ‖A.indicator (1 : 𝕋 → ℂ) y - g' y‖ ≤ |A.indicator (1 : 𝕋 → ℝ) y - g y| := by
    intro y
    rw [hcast, hg'apply, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_sub_clamp_le (hF01 y).1 (hF01 y).2
  have hg'n : ∀ y, ‖g' y‖ ≤ 1 := fun y => by
    rw [hg'apply, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor
    · have := le_max_left 0 (min 1 (g y)); linarith
    · exact max_le zero_le_one (min_le_left _ _)
  have hmem : g' ∈ closure (D : Set C(𝕋, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, hD]; trivial
  obtain ⟨p, hpD, hp⟩ := Metric.mem_closure_iff.1 hmem (min 1 δ) (lt_min one_pos hδ)
  have hpt : ∀ y, ‖g' y - p y‖ ≤ min 1 δ := fun y => by
    have := ContinuousMap.dist_apply_le_dist (f := g') (g := p) y
    rw [dist_eq_norm] at this
    exact this.trans hp.le
  refine ⟨p, hpD, fun y => ?_, ?_⟩
  · have e : p y = g' y - (g' y - p y) := by ring
    rw [e]
    calc ‖g' y - (g' y - p y)‖ ≤ ‖g' y‖ + ‖g' y - p y‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hg'n y) ((hpt y).trans (min_le_left _ _))
      _ = 2 := by norm_num
  · have hint1 : Integrable (fun y => |A.indicator (1 : 𝕋 → ℝ) y - g y| + δ) ν := by
      refine Integrable.add ?_ (integrable_const δ)
      refine Integrable.of_bound (hF.sub g.continuous.measurable).abs.aestronglyMeasurable (1 + ‖g‖)
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_abs]
      refine (abs_sub _ _).trans (add_le_add (hFb y) ?_)
      simpa [Real.norm_eq_abs] using g.norm_coe_le_norm y
    have hpw : ∀ y, ‖A.indicator (1 : 𝕋 → ℂ) y - p y‖ ≤ |A.indicator (1 : 𝕋 → ℝ) y - g y| + δ := by
      intro y
      calc ‖A.indicator (1 : 𝕋 → ℂ) y - p y‖
          ≤ ‖A.indicator (1 : 𝕋 → ℂ) y - g' y‖ + ‖g' y - p y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ |A.indicator (1 : 𝕋 → ℝ) y - g y| + δ :=
          add_le_add (hg'le y) ((hpt y).trans (min_le_right _ _))
    calc ∫ y, ‖A.indicator (1 : 𝕋 → ℂ) y - p y‖ ∂ν
        ≤ ∫ y, (|A.indicator (1 : 𝕋 → ℝ) y - g y| + δ) ∂ν :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint1
            (Eventually.of_forall hpw)
      _ = ∫ y, |A.indicator (1 : 𝕋 → ℝ) y - g y| ∂ν + δ := by
          rw [integral_add (hint1.sub (integrable_const δ) |>.congr
            (Eventually.of_forall fun y => by simp)) (integrable_const δ)]
          simp
      _ ≤ 2 * δ := by linarith

variable {𝕋₁ 𝕋₂ : Type*} [TopologicalSpace 𝕋₁] [CompactSpace 𝕋₁] [MeasurableSpace 𝕋₁]
  [BorelSpace 𝕋₁] [TopologicalSpace 𝕋₂] [CompactSpace 𝕋₂] [MeasurableSpace 𝕋₂] [BorelSpace 𝕋₂]

theorem integrable_continuousMap_comp [IsFiniteMeasure P] (f : C(𝕋₁, ℂ)) {Ξ : Ω → 𝕋₁}
    (hΞ : Measurable Ξ) : Integrable (fun ω => f (Ξ ω)) P :=
  integrable_comp_of_norm_le hΞ f.continuous.measurable fun y => f.norm_coe_le_norm y

theorem igMixCorr_add_left [IsFiniteMeasure P] {Ξ : Ω → 𝕋₁} {Υ : ℕ → Ω → 𝕋₂}
    (hΞ : Measurable Ξ) (hΥ : ∀ n, Measurable (Υ n)) (f f' : C(𝕋₁, ℂ)) (g : C(𝕋₂, ℂ)) :
    igMixCorr P Ξ Υ ⇑(f + f') g = igMixCorr P Ξ Υ f g + igMixCorr P Ξ Υ f' g := by
  funext n
  have i1 := integrable_continuousMap_comp (P := P) f hΞ
  have i2 := integrable_continuousMap_comp (P := P) f' hΞ
  have i3 := integrable_comp_mul_of_norm_le (P := P) hΞ (hΥ n) f.continuous.measurable
    g.continuous.measurable (fun y => f.norm_coe_le_norm y) (fun y => g.norm_coe_le_norm y)
  have i4 := integrable_comp_mul_of_norm_le (P := P) hΞ (hΥ n) f'.continuous.measurable
    g.continuous.measurable (fun y => f'.norm_coe_le_norm y) (fun y => g.norm_coe_le_norm y)
  simp only [igMixCorr, Pi.add_apply, ContinuousMap.coe_add, add_mul]
  rw [integral_add i3 i4, integral_add i1 i2]
  ring

theorem igMixCorr_add_right [IsFiniteMeasure P] {Ξ : Ω → 𝕋₁} {Υ : ℕ → Ω → 𝕋₂}
    (hΞ : Measurable Ξ) (hΥ : ∀ n, Measurable (Υ n)) (f : C(𝕋₁, ℂ)) (g g' : C(𝕋₂, ℂ)) :
    igMixCorr P Ξ Υ f ⇑(g + g') = igMixCorr P Ξ Υ f g + igMixCorr P Ξ Υ f g' := by
  funext n
  have i1 := integrable_continuousMap_comp (P := P) g (hΥ n)
  have i2 := integrable_continuousMap_comp (P := P) g' (hΥ n)
  have i3 := integrable_comp_mul_of_norm_le (P := P) hΞ (hΥ n) f.continuous.measurable
    g.continuous.measurable (fun y => f.norm_coe_le_norm y) (fun y => g.norm_coe_le_norm y)
  have i4 := integrable_comp_mul_of_norm_le (P := P) hΞ (hΥ n) f.continuous.measurable
    g'.continuous.measurable (fun y => f.norm_coe_le_norm y) (fun y => g'.norm_coe_le_norm y)
  simp only [igMixCorr, Pi.add_apply, ContinuousMap.coe_add, mul_add]
  rw [integral_add i3 i4, integral_add i1 i2]
  ring

omit [CompactSpace 𝕋₁] [MeasurableSpace 𝕋₁] [BorelSpace 𝕋₁] [CompactSpace 𝕋₂] [MeasurableSpace 𝕋₂]
  [BorelSpace 𝕋₂] in
theorem igMixCorr_smul_left {Ξ : Ω → 𝕋₁} {Υ : ℕ → Ω → 𝕋₂} (c : ℂ) (f : C(𝕋₁, ℂ))
    (g : C(𝕋₂, ℂ)) : igMixCorr P Ξ Υ ⇑(c • f) g = c • igMixCorr P Ξ Υ f g := by
  funext n
  simp only [igMixCorr, Pi.smul_apply, ContinuousMap.coe_smul, smul_eq_mul, mul_assoc]
  rw [integral_const_mul, integral_const_mul]
  ring

omit [CompactSpace 𝕋₁] [MeasurableSpace 𝕋₁] [BorelSpace 𝕋₁] [CompactSpace 𝕋₂] [MeasurableSpace 𝕋₂]
  [BorelSpace 𝕋₂] in
theorem igMixCorr_smul_right {Ξ : Ω → 𝕋₁} {Υ : ℕ → Ω → 𝕋₂} (c : ℂ) (f : C(𝕋₁, ℂ))
    (g : C(𝕋₂, ℂ)) : igMixCorr P Ξ Υ f ⇑(c • g) = c • igMixCorr P Ξ Υ f g := by
  funext n
  simp only [igMixCorr, Pi.smul_apply, ContinuousMap.coe_smul, smul_eq_mul]
  rw [integral_const_mul, show (fun ω => f (Ξ ω) * (c * g (Υ n ω))) =
    fun ω => c * (f (Ξ ω) * g (Υ n ω)) from funext fun ω => by ring, integral_const_mul]
  ring

/-- Convergence of the correlations on the spans of two families of continuous functions. -/
theorem tendsto_igMixCorr_span [IsFiniteMeasure P] {ι₁ ι₂ : Type*} (e₁ : ι₁ → C(𝕋₁, ℂ))
    (e₂ : ι₂ → C(𝕋₂, ℂ)) {Ξ : Ω → 𝕋₁} {Υ : ℕ → Ω → 𝕋₂} (hΞ : Measurable Ξ)
    (hΥ : ∀ n, Measurable (Υ n))
    (hchar : ∀ a b, Tendsto (igMixCorr P Ξ Υ (e₁ a) (e₂ b)) atTop (𝓝 0)) :
    ∀ f ∈ Submodule.span ℂ (Set.range e₁), ∀ g ∈ Submodule.span ℂ (Set.range e₂),
      Tendsto (igMixCorr P Ξ Υ f g) atTop (𝓝 0) := by
  have hright : ∀ a, ∀ g ∈ Submodule.span ℂ (Set.range e₂),
      Tendsto (igMixCorr P Ξ Υ (e₁ a) g) atTop (𝓝 0) := by
    intro a g hg
    induction hg using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact hchar a b
    | zero =>
      have h0 : igMixCorr P Ξ Υ (e₁ a) ⇑(0 : C(𝕋₂, ℂ)) = fun _ => 0 := by
        funext n; simp [igMixCorr]
      rw [h0]; exact tendsto_const_nhds
    | add y y' _ _ hy hy' =>
      rw [igMixCorr_add_right hΞ hΥ]
      have := hy.add hy'
      rw [add_zero] at this
      exact this
    | smul c y _ hy =>
      rw [igMixCorr_smul_right]
      have := hy.const_smul c
      rw [smul_zero] at this
      exact this
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact hright a
  | zero =>
    intro g _
    have h0 : igMixCorr P Ξ Υ ⇑(0 : C(𝕋₁, ℂ)) g = fun _ => 0 := by
      funext n; simp [igMixCorr]
    rw [h0]; exact tendsto_const_nhds
  | add x x' _ _ hx hx' =>
    intro g hg
    rw [igMixCorr_add_left hΞ hΥ]
    have := (hx g hg).add (hx' g hg)
    rw [add_zero] at this
    exact this
  | smul c x _ hx =>
    intro g hg
    rw [igMixCorr_smul_left]
    have := (hx g hg).const_smul c
    rw [smul_zero] at this
    exact this

/-- **Convergence of correlations of events from a dense family.** -/
theorem tendsto_igMixCorr_indicator_of_dense [TopologicalSpace.MetrizableSpace 𝕋₁]
    [TopologicalSpace.MetrizableSpace 𝕋₂] [IsProbabilityMeasure P]
    {D₁ : Submodule ℂ C(𝕋₁, ℂ)} {D₂ : Submodule ℂ C(𝕋₂, ℂ)} (hD₁ : D₁.topologicalClosure = ⊤)
    (hD₂ : D₂.topologicalClosure = ⊤) {Ξ : Ω → 𝕋₁} {Υ : ℕ → Ω → 𝕋₂} (hΞ : Measurable Ξ)
    (hΥ : ∀ n, Measurable (Υ n)) (hlaw : ∀ n, P.map (Υ n) = P.map (Υ 0))
    (hcorr : ∀ f ∈ D₁, ∀ g ∈ D₂, Tendsto (igMixCorr P Ξ Υ f g) atTop (𝓝 0))
    {A : Set 𝕋₁} {B : Set 𝕋₂} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (igMixCorr P Ξ Υ (A.indicator 1) (B.indicator 1)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / 32 := by positivity
  have : IsProbabilityMeasure (P.map Ξ) :=
    (Measure.isProbabilityMeasure_map_iff hΞ.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (P.map (Υ 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hΥ 0).aemeasurable).mpr inferInstance
  obtain ⟨p, hpD, hp2, hpA⟩ := exists_mem_integral_norm_indicator_sub_le hD₁ (P.map Ξ) hA hδ
  obtain ⟨q, hqD, hq2, hqB⟩ := exists_mem_integral_norm_indicator_sub_le hD₂ (P.map (Υ 0)) hB hδ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hcorr p hpD q hqD) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hNn := hN n hn
  rw [dist_zero_right] at hNn ⊢
  have hAm : Measurable (A.indicator (1 : 𝕋₁ → ℂ)) := measurable_one.indicator hA
  have hBm : Measurable (B.indicator (1 : 𝕋₂ → ℂ)) := measurable_one.indicator hB
  have hA1 : ∀ y, ‖A.indicator (1 : 𝕋₁ → ℂ) y‖ ≤ 1 := fun y => by by_cases hy : y ∈ A <;> simp [hy]
  have hB1 : ∀ y, ‖B.indicator (1 : 𝕋₂ → ℂ) y‖ ≤ 1 := fun y => by by_cases hy : y ∈ B <;> simp [hy]
  have hpm : Measurable (⇑p) := p.continuous.measurable
  have hqm : Measurable (⇑q) := q.continuous.measurable
  have hsplit := igMixCorr_sub_sub (P := P) hΞ hΥ hAm hpm hBm hqm hA1 hp2 hB1 hq2 n
  have hAp3 : ∀ y, ‖(A.indicator (1 : 𝕋₁ → ℂ) - ⇑p) y‖ ≤ 3 := fun y => by
    rw [Pi.sub_apply]
    exact (norm_sub_le _ _).trans (by linarith [hA1 y, hp2 y])
  have hBq3 : ∀ y, ‖(B.indicator (1 : 𝕋₂ → ℂ) - ⇑q) y‖ ≤ 3 := fun y => by
    rw [Pi.sub_apply]
    exact (norm_sub_le _ _).trans (by linarith [hB1 y, hq2 y])
  have hb1 := norm_igMixCorr_le_left (P := P) Υ hΞ (hAm.sub hpm) hAp3 hB1 n
  have hb2 := norm_igMixCorr_le_right (P := P) Ξ hΥ (hBm.sub hqm) hp2 hBq3 zero_le_two n
  rw [hlaw n] at hb2
  simp only [Pi.sub_apply] at hb1 hb2
  have hx : igMixCorr P Ξ Υ (A.indicator 1) (B.indicator 1) n =
      igMixCorr P Ξ Υ p q n + (igMixCorr P Ξ Υ (A.indicator 1) (B.indicator 1) n -
        igMixCorr P Ξ Υ p q n) := by ring
  rw [hx, hsplit]
  calc ‖igMixCorr P Ξ Υ p q n + (igMixCorr P Ξ Υ (A.indicator 1 - ⇑p) (B.indicator 1) n +
        igMixCorr P Ξ Υ p (B.indicator 1 - ⇑q) n)‖
      ≤ ‖igMixCorr P Ξ Υ p q n‖ + (‖igMixCorr P Ξ Υ (A.indicator 1 - ⇑p) (B.indicator 1) n‖ +
        ‖igMixCorr P Ξ Υ p (B.indicator 1 - ⇑q) n‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ < ε := by linarith

end Dense

/-! ### The Gaussian circle-average increments -/

section Gauss

open LQGMetric LQGMetric.CircleAvg LQGDimension.SegLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → Field} {u : Ω → ℝ}

omit [MeasurableSpace Ω] in
theorem inGSpan_cInc {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    InGSpan (incProc h) (cInc h r z s w) :=
  InGSpan.eval (X := incProc h) ((⟨r, hr⟩, z), (⟨s, hs⟩, w))

/-- The circle-average increments at scale `2^n`: `h_{2^n x}(2^n w) − h_{2^n}(0)` at the indices of positive
radius, `0` at the others. -/
def igMixGauss (h : Ω → Field) (J : Finset (ℝ × ℂ)) (n : ℕ) (ω : Ω) (x : J) : ℝ :=
  if 0 < (x : ℝ × ℂ).1 then
    cInc h ((2 : ℝ) ^ n * (x : ℝ × ℂ).1) ((((2 : ℝ) ^ n : ℝ) : ℂ) * (x : ℝ × ℂ).2) ((2 : ℝ) ^ n) 0 ω
  else 0

omit [MeasurableSpace Ω] in
theorem inGSpan_igMixGauss (J : Finset (ℝ × ℂ)) (n : ℕ) (x : J) :
    InGSpan (incProc h) (fun ω => igMixGauss h J n ω x) := by
  by_cases hx : 0 < (x : ℝ × ℂ).1
  · simp only [igMixGauss, hx, ↓reduceIte]
    exact inGSpan_cInc (by positivity) (by positivity) _ _
  · simp only [igMixGauss, hx, ↓reduceIte]
    exact InGSpan.zero

omit [MeasurableSpace Ω] in
theorem inGSpan_sum_igMixGauss (J : Finset (ℝ × ℂ)) (n : ℕ) (s : J → ℝ) :
    InGSpan (incProc h) (fun ω => ∑ x, s x * igMixGauss h J n ω x) :=
  InGSpan.finset_sum _ fun x _ => (inGSpan_igMixGauss J n x).const_mul (s x)

theorem hasGaussianLaw_of_inGSpan (hh : IsWholePlaneGFF h P) {Z : Ω → ℝ}
    (hZ : InGSpan (incProc h) Z) : HasGaussianLaw Z P :=
  hZ.hasGaussianLaw (isGaussianProcess_incProc hh)

theorem integral_eq_zero_of_inGSpan (hh : IsWholePlaneGFF h P) {Z : Ω → ℝ}
    (hZ : InGSpan (incProc h) Z) : ∫ ω, Z ω ∂P = 0 :=
  hZ.integral_eq_zero (isGaussianProcess_incProc hh) fun t => integral_cInc hh t.1.1.2 t.2.1.2 _ _

theorem memLp_of_inGSpan (hh : IsWholePlaneGFF h P) {Z : Ω → ℝ} (hZ : InGSpan (incProc h) Z) :
    MemLp Z 2 P :=
  (hasGaussianLaw_of_inGSpan hh hZ).memLp_two

/-- **Phase–field factorization.** For an independent phase `u` and a finite linear combination `Z` of
circle-average increments of a normalized whole-plane GFF,
`E[exp(i(α(u + h_1(0)) + Z))] = E[exp(iαu)] exp(−Var(Z)/2)`. -/
theorem integral_cexp_phase_add_inGSpan (hh : IsNormalizedWPGFF h P) (hum : Measurable u)
    (hind : IndepFun h u P) {Z : Ω → ℝ} (hZ : InGSpan (incProc h) Z) (α : ℝ) :
    ∫ ω, Complex.exp (((α * (u ω + circleAvg (h ω) 1 0) + Z ω : ℝ) : ℂ) * Complex.I) ∂P =
      (∫ ω, Complex.exp (((α * u ω : ℝ) : ℂ) * Complex.I) ∂P) *
        ((Real.exp (-(Var[Z; P] / 2)) : ℝ) : ℂ) := by
  have hG := hasGaussianLaw_of_inGSpan hh.1 hZ
  have h0 := integral_eq_zero_of_inGSpan hh.1 hZ
  have hchar := integral_cexp_mul_I_of_hasGaussianLaw hG h0
  obtain ⟨I, β, hZeq⟩ := hZ
  let F : Field → ℝ := fun g => ∑ p ∈ I, β p * (circleAvg g p.1.1 p.1.2 - circleAvg g p.2.1 p.2.2)
  have hFm : Measurable F := Finset.measurable_sum _ fun p _ =>
    measurable_const.mul ((measurable_circleAvg_left _ _).sub (measurable_circleAvg_left _ _))
  have hZF : ∀ ω, Z ω = F (h ω) := fun ω => by rw [hZeq]; rfl
  have hae : (fun ω => Complex.exp (((α * (u ω + circleAvg (h ω) 1 0) + Z ω : ℝ) : ℂ) * Complex.I))
      =ᵐ[P] fun ω => Complex.exp (((F (h ω) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((α * u ω : ℝ) : ℂ) * Complex.I) := by
    filter_upwards [hh.2] with ω hω
    rw [hω, hZF ω, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfac := hind.integral_comp_mul_comp hh.1.measurable.aemeasurable hum.aemeasurable
    (f := fun g => Complex.exp (((F g : ℝ) : ℂ) * Complex.I))
    (g := fun v : ℝ => Complex.exp (((α * v : ℝ) : ℂ) * Complex.I))
    ((Complex.measurable_ofReal.comp hFm).mul_const _).cexp.aestronglyMeasurable
    ((Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul_const _).cexp.aestronglyMeasurable
  have hfac' : ∫ ω, Complex.exp (((F (h ω) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((α * u ω : ℝ) : ℂ) * Complex.I) ∂P =
      (∫ ω, Complex.exp (((F (h ω) : ℝ) : ℂ) * Complex.I) ∂P) *
        ∫ ω, Complex.exp (((α * u ω : ℝ) : ℂ) * Complex.I) ∂P := hfac
  rw [integral_congr_ae hae, hfac']
  have hchar' : ∫ ω, Complex.exp (((F (h ω) : ℝ) : ℂ) * Complex.I) ∂P =
      ((Real.exp (-(Var[Z; P] / 2)) : ℝ) : ℂ) := by
    rw [← hchar]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [hZF ω])
  rw [hchar', mul_comm]

theorem variance_add_ge [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : MemLp X 2 P)
    (hY : MemLp Y 2 P) : Var[Y; P] / 2 - Var[X; P] ≤ Var[fun ω => X ω + Y ω; P] := by
  have hU : MemLp (fun ω => X ω + Y ω) 2 P := hX.add hY
  have h1 := variance_add hU hX
  have h2 := variance_sub hU hX
  have h3 : Var[(fun ω => X ω + Y ω) - X; P] = Var[Y; P] := by
    congr 1; funext ω; simp
  have h4 : 0 ≤ Var[(fun ω => X ω + Y ω) + X; P] := variance_nonneg _ _
  rw [h3] at h2
  linarith

theorem variance_add_le [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : MemLp X 2 P)
    (hY : MemLp Y 2 P) : Var[fun ω => X ω + Y ω; P] ≤ 2 * Var[X; P] + 2 * Var[Y; P] := by
  have h1 := variance_add hX hY
  have h2 := variance_sub hX hY
  have h4 : 0 ≤ Var[X - Y; P] := variance_nonneg _ _
  have e : Var[fun ω => X ω + Y ω; P] = Var[X + Y; P] := rfl
  rw [e]
  linarith

/-! #### Newton's theorem at large scales -/

theorem abs_circLog_scale_sub_le (n : ℕ) {S : ℝ} (hS : 0 < S) (W y : ℂ)
    (hy : ‖y‖ ≤ (2 : ℝ) ^ n) :
    |circLog ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S) y - circLog 0 ((2 : ℝ) ^ n) y -
      Real.log (max S ‖W‖)| ≤ ‖y‖ / ((2 : ℝ) ^ n * S) := by
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hm : 0 < (2 : ℝ) ^ n * S := mul_pos h2n hS
  rw [circLog_eq_log_max hm, circLog_eq_log_max h2n]
  have hy' : max ((2 : ℝ) ^ n) ‖(0 : ℂ) - y‖ = (2 : ℝ) ^ n := by
    rw [zero_sub, norm_neg]; exact max_eq_left hy
  rw [hy']
  have hB : max ((2 : ℝ) ^ n * S) ‖(((2 : ℝ) ^ n : ℝ) : ℂ) * W‖ = (2 : ℝ) ^ n * max S ‖W‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2n, mul_max_of_nonneg _ _ h2n.le]
  have hlogB : Real.log ((2 : ℝ) ^ n * max S ‖W‖) = Real.log ((2 : ℝ) ^ n) + Real.log (max S ‖W‖) :=
    Real.log_mul h2n.ne' (lt_max_of_lt_left hS).ne'
  have key : Real.log (max ((2 : ℝ) ^ n * S) ‖(((2 : ℝ) ^ n : ℝ) : ℂ) * W - y‖) -
      Real.log ((2 : ℝ) ^ n) - Real.log (max S ‖W‖) =
      Real.log (max ((2 : ℝ) ^ n * S) ‖(((2 : ℝ) ^ n : ℝ) : ℂ) * W - y‖) -
        Real.log (max ((2 : ℝ) ^ n * S) ‖(((2 : ℝ) ^ n : ℝ) : ℂ) * W‖) := by
    rw [hB, hlogB]; ring
  rw [key]
  refine (LQGMetric.CircleAvg.abs_log_sub_log_le hm (le_max_left _ _) (le_max_left _ _)).trans ?_
  refine (div_le_div_iff_of_pos_right hm).2 ?_
  rw [max_comm ((2 : ℝ) ^ n * S), max_comm ((2 : ℝ) ^ n * S)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [sub_sub_cancel_left, norm_neg]

theorem abs_circCov_scale_sub_le (n : ℕ) {S : ℝ} (hS : 0 < S) (W c : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hcρ : ‖c‖ + ρ ≤ (2 : ℝ) ^ n) :
    |circCov c ρ ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S) - circCov c ρ 0 ((2 : ℝ) ^ n) -
      Real.log (max S ‖W‖)| ≤ (‖c‖ + ρ) / ((2 : ℝ) ^ n * S) := by
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hci1 : CircleIntegrable (circLog ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S)) c ρ :=
    ((continuous_circLog (mul_pos h2n hS).ne' _).continuousOn).circleIntegrable'
  have hci2 : CircleIntegrable (circLog 0 ((2 : ℝ) ^ n)) c ρ :=
    ((continuous_circLog h2n.ne' _).continuousOn).circleIntegrable'
  set L := Real.log (max S ‖W‖)
  set E := (‖c‖ + ρ) / ((2 : ℝ) ^ n * S)
  have hsub : circCov c ρ ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S) -
      circCov c ρ 0 ((2 : ℝ) ^ n) = Real.circleAverage (fun y =>
        circLog ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S) y - circLog 0 ((2 : ℝ) ^ n) y) c ρ := by
    simp only [circCov]
    rw [Real.circleAverage_fun_sub hci1 hci2]
  have hfi : CircleIntegrable (fun y =>
      circLog ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S) y - circLog 0 ((2 : ℝ) ^ n) y) c ρ :=
    hci1.sub hci2
  have hpt : ∀ y ∈ Metric.sphere c |ρ|,
      |circLog ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S) y - circLog 0 ((2 : ℝ) ^ n) y - L| ≤ E := by
    intro y hy
    have hyc : ‖y - c‖ = ρ := by
      rw [← dist_eq_norm, ← abs_of_pos hρ]; exact hy
    have hyn : ‖y‖ ≤ ‖c‖ + ρ := by
      calc ‖y‖ = ‖c + (y - c)‖ := by rw [add_sub_cancel]
        _ ≤ ‖c‖ + ‖y - c‖ := norm_add_le _ _
        _ = ‖c‖ + ρ := by rw [hyc]
    refine (abs_circLog_scale_sub_le n hS W y (hyn.trans hcρ)).trans ?_
    exact (div_le_div_iff_of_pos_right (mul_pos h2n hS)).2 hyn
  rw [hsub, abs_le]
  constructor
  · have hc : CircleIntegrable (fun _ : ℂ => L - E) c ρ := circleIntegrable_const _ _ _
    have := Real.circleAverage_mono_on_of_le_circle (hc.sub hfi) (a := 0) fun y hy => by
      have := (abs_le.1 (hpt y hy)).1
      simp only [Pi.sub_apply]
      linarith
    rw [Real.circleAverage_sub hc hfi, Real.circleAverage_const] at this
    linarith
  · have := Real.circleAverage_mono_on_of_le_circle hfi (a := L + E) fun y hy => by
      have := (abs_le.1 (hpt y hy)).2
      linarith
    linarith

/-- **Decorrelation of the small and the large scales** (Newton's theorem): the covariance of `h_r(z) − h_1(0)`
and `h_{2^n S}(2^n W) − h_{2^n}(0)` tends to `0`. -/
theorem tendsto_incCov_scale {z : ℂ} {r : ℝ} (hr : 0 < r) (W : ℂ) {S : ℝ} (hS : 0 < S) :
    Tendsto (fun n : ℕ => incCov z r 0 1 ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S) 0
      ((2 : ℝ) ^ n)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hev : ∀ᶠ n : ℕ in atTop, ‖z‖ + r + 1 ≤ (2 : ℝ) ^ n := hpow.eventually_ge_atTop _
  have hbound : Tendsto (fun n : ℕ => (‖z‖ + r + 1) / S * ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp hpow).const_mul ((‖z‖ + r + 1) / S)
    simpa using this
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [hev] with n hn
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have e1 := abs_circCov_scale_sub_le n hS W z hr (by linarith)
  have e2 := abs_circCov_scale_sub_le n hS W 0 one_pos
    (by have := norm_nonneg z; simp only [norm_zero]; linarith)
  set L := Real.log (max S ‖W‖)
  have hexp : incCov z r 0 1 ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S) 0 ((2 : ℝ) ^ n) =
      -(circCov z r ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S) - circCov z r 0 ((2 : ℝ) ^ n) - L) +
        (circCov 0 1 ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S) - circCov 0 1 0 ((2 : ℝ) ^ n) - L) := by
    simp only [incCov]; ring
  rw [Real.norm_eq_abs, hexp]
  calc |-(circCov z r ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S) - circCov z r 0 ((2 : ℝ) ^ n) - L) +
        (circCov 0 1 ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S) - circCov 0 1 0 ((2 : ℝ) ^ n) - L)|
      ≤ |circCov z r ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S) - circCov z r 0 ((2 : ℝ) ^ n) - L| +
        |circCov 0 1 ((((2 : ℝ) ^ n : ℝ) : ℂ) * W) ((2 : ℝ) ^ n * S) - circCov 0 1 0 ((2 : ℝ) ^ n) - L| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
    _ ≤ (‖z‖ + r) / ((2 : ℝ) ^ n * S) + (‖(0 : ℂ)‖ + 1) / ((2 : ℝ) ^ n * S) := add_le_add e1 e2
    _ = (‖z‖ + r + 1) / S * ((2 : ℝ) ^ n)⁻¹ := by
        rw [norm_zero, zero_add, ← add_div, mul_comm ((2 : ℝ) ^ n) S, ← div_div,
          div_eq_mul_inv _ ((2 : ℝ) ^ n)]

theorem tendsto_cov_igMixGauss (hh : IsWholePlaneGFF h P) (J K : Finset (ℝ × ℂ)) (x : J) (k : K) :
    Tendsto (fun n : ℕ => cov[fun ω => igMixGauss h J 0 ω x, fun ω => igMixGauss h K n ω k; P])
      atTop (𝓝 0) := by
  by_cases hx : 0 < (x : ℝ × ℂ).1
  · by_cases hk : 0 < (k : ℝ × ℂ).1
    · have hcov : ∀ n : ℕ, cov[fun ω => igMixGauss h J 0 ω x, fun ω => igMixGauss h K n ω k; P] =
          incCov ((((2 : ℝ) ^ 0 : ℝ) : ℂ) * (x : ℝ × ℂ).2) ((2 : ℝ) ^ 0 * (x : ℝ × ℂ).1) 0 ((2 : ℝ) ^ 0)
            ((((2 : ℝ) ^ n : ℝ) : ℂ) * (k : ℝ × ℂ).2) ((2 : ℝ) ^ n * (k : ℝ × ℂ).1) 0 ((2 : ℝ) ^ n) := by
        intro n
        simp only [igMixGauss, hx, hk, ↓reduceIte]
        exact covariance_cInc hh (by positivity) (by positivity) (by positivity) (by positivity) _ _ _ _
      simp only [hcov, pow_zero, one_mul, Complex.ofReal_one]
      exact tendsto_incCov_scale hx _ hk
    · simp [igMixGauss, hk, covariance]
  · simp [igMixGauss, hx, covariance]

end Gauss

/-! ### Coordinates of the cylinders -/

section Coord

/-- The coordinates of an array on a finite set of indices: the phase coordinate `f(1, 0)` and, at indices of
positive radius, the increment `f(x) − f(1, 0)`. -/
def igMixCoord (J : Finset (ℝ × ℂ)) (f : ℝ × ℂ → ℝ) : ℝ × (J → ℝ) :=
  (f (1, 0), fun x => if 0 < (x : ℝ × ℂ).1 then f x - f (1, 0) else f x)

/-- The values on `J` recovered from the coordinates. -/
def igMixRecover (J : Finset (ℝ × ℂ)) (p : ℝ × (J → ℝ)) : J → ℝ :=
  fun x => if 0 < (x : ℝ × ℂ).1 then p.1 + p.2 x else p.2 x

theorem igMixRecover_igMixCoord (J : Finset (ℝ × ℂ)) (f : ℝ × ℂ → ℝ) :
    igMixRecover J (igMixCoord J f) = J.restrict f := by
  funext x
  simp only [igMixRecover, igMixCoord, Finset.restrict]
  split_ifs <;> ring

theorem measurable_igMixCoord (J : Finset (ℝ × ℂ)) : Measurable (igMixCoord J) := by
  refine (measurable_pi_apply _).prodMk (Measurable.of_eval fun x => ?_)
  by_cases hx : 0 < (x : ℝ × ℂ).1
  · simp only [hx, ↓reduceIte]
    exact (measurable_pi_apply _).sub (measurable_pi_apply _)
  · simp only [hx, ↓reduceIte]
    exact measurable_pi_apply _

theorem measurable_igMixRecover (J : Finset (ℝ × ℂ)) : Measurable (igMixRecover J) := by
  refine Measurable.of_eval fun x => ?_
  by_cases hx : 0 < (x : ℝ × ℂ).1
  · simp only [igMixRecover, hx, ↓reduceIte]
    exact measurable_fst.add ((measurable_pi_apply x).comp measurable_snd)
  · simp only [igMixRecover, hx, ↓reduceIte]
    exact (measurable_pi_apply x).comp measurable_snd

/-- **The iterates of the normalized dilation by `2`.** -/
theorem igDilationStep_two_iterate (γ : ℝ) {n : ℕ} (hn : 1 ≤ n) (f : ℝ × ℂ → ℝ) :
    ∃ k : ℤ, ∀ x : ℝ × ℂ, (igDilationStep γ 2)^[n] f x =
      if 0 < x.1 then f ((2 : ℝ) ^ n * x.1, (((2 : ℝ) ^ n : ℝ) : ℂ) * x.2) - k * (2 * Real.pi * igChi γ)
      else 0 := by
  have hstep : ∀ (g : ℝ × ℂ → ℝ) (y : ℝ × ℂ), igDilationStep γ 2 g y =
      if 0 < y.1 then g (2 * y.1, ((2 : ℝ) : ℂ) * y.2) -
        ((⌊g (2, 0) / (2 * Real.pi * igChi γ)⌋ : ℤ) : ℝ) * (2 * Real.pi * igChi γ) else 0 :=
    fun _ _ => rfl
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨⌊f (2, 0) / (2 * Real.pi * igChi γ)⌋, fun x => ?_⟩
    rw [Function.iterate_one, hstep, pow_one]
  | succ n hn ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + ⌊(igDilationStep γ 2)^[n] f (2, 0) / (2 * Real.pi * igChi γ)⌋, fun x => ?_⟩
    rw [Function.iterate_succ_apply', hstep]
    by_cases hx : 0 < x.1
    · have h2x : 0 < (2 * x.1, ((2 : ℝ) : ℂ) * x.2).1 := by dsimp only; positivity
      rw [ite_eq_left hx, ite_eq_left hx, hk, ite_eq_left h2x]
      have hpt : ((2 : ℝ) ^ n * (2 * x.1, ((2 : ℝ) : ℂ) * x.2).1,
          (((2 : ℝ) ^ n : ℝ) : ℂ) * (2 * x.1, ((2 : ℝ) : ℂ) * x.2).2) =
          ((2 : ℝ) ^ (n + 1) * x.1, (((2 : ℝ) ^ (n + 1) : ℝ) : ℂ) * x.2) := by
        ext <;> simp [pow_succ] <;> ring
      rw [hpt]
      push_cast
      ring
    · rw [ite_eq_right hx, ite_eq_right hx]

theorem igMixCoord_igPosCircleProcess (J : Finset (ℝ × ℂ)) (g : Field) (v : ℝ) :
    igMixCoord J (igPosCircleProcess g v) =
      (v + LQGMetric.circleAvg g 1 0, fun x : J => if 0 < (x : ℝ × ℂ).1 then
        LQGMetric.circleAvg g (x : ℝ × ℂ).1 (x : ℝ × ℂ).2 - LQGMetric.circleAvg g 1 0 else 0) := by
  have h1 : igPosCircleProcess g v (1, 0) = v + LQGMetric.circleAvg g 1 0 :=
    igPosCircleProcess_of_pos g v (x := ((1 : ℝ), (0 : ℂ))) one_pos
  refine Prod.ext h1 (funext fun x => ?_)
  simp only [igMixCoord]
  by_cases hx : 0 < (x : ℝ × ℂ).1
  · rw [ite_eq_left hx, ite_eq_left hx, igPosCircleProcess_of_pos g v hx, h1]
    ring
  · rw [ite_eq_right hx, ite_eq_right hx, igPosCircleProcess_of_nonpos g v hx]

theorem exists_igMixCoord_iterate (γ : ℝ) (K : Finset (ℝ × ℂ)) {n : ℕ} (hn : 1 ≤ n) (g : Field)
    (v : ℝ) :
    ∃ k : ℤ, igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess g v)) =
      (v + LQGMetric.circleAvg g ((2 : ℝ) ^ n) 0 - k * (2 * Real.pi * igChi γ),
        fun x : K => if 0 < (x : ℝ × ℂ).1 then
          LQGMetric.circleAvg g ((2 : ℝ) ^ n * (x : ℝ × ℂ).1) ((((2 : ℝ) ^ n : ℝ) : ℂ) * (x : ℝ × ℂ).2) -
            LQGMetric.circleAvg g ((2 : ℝ) ^ n) 0 else 0) := by
  obtain ⟨k, hk⟩ := igDilationStep_two_iterate γ hn (igPosCircleProcess g v)
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have ho : (igDilationStep γ 2)^[n] (igPosCircleProcess g v) (1, 0) =
      v + LQGMetric.circleAvg g ((2 : ℝ) ^ n) 0 - k * (2 * Real.pi * igChi γ) := by
    rw [hk]
    dsimp only
    rw [ite_eq_left one_pos, mul_one, mul_zero,
      igPosCircleProcess_of_pos g v (x := ((2 : ℝ) ^ n, (0 : ℂ))) h2n]
  refine ⟨k, Prod.ext ho (funext fun x => ?_)⟩
  simp only [igMixCoord]
  by_cases hx : 0 < (x : ℝ × ℂ).1
  · rw [ite_eq_left hx, ite_eq_left hx, ho, hk, ite_eq_left hx,
      igPosCircleProcess_of_pos g v (x := ((2 : ℝ) ^ n * (x : ℝ × ℂ).1,
        (((2 : ℝ) ^ n : ℝ) : ℂ) * (x : ℝ × ℂ).2)) (mul_pos h2n hx)]
    ring
  · rw [ite_eq_right hx, ite_eq_right hx, hk, ite_eq_right hx]

end Coord

/-! ### Characters, the torus and the box -/

section Torus

/-- The character `exp(i(α a + ⟨s, b⟩))` of the coordinates `(a, b)`. -/
def igMixChar {ι : Type*} [Fintype ι] (α : ℝ) (s : ι → ℝ) (p : ℝ × (ι → ℝ)) : ℂ :=
  Complex.exp (((α * p.1 + ∑ i, s i * p.2 i : ℝ) : ℂ) * Complex.I)

theorem cexp_ofReal_add_two_pi_mul_int (x : ℝ) (j : ℤ) :
    Complex.exp (((x + 2 * Real.pi * j : ℝ) : ℂ) * Complex.I) = Complex.exp ((x : ℂ) * Complex.I) := by
  have h1 : (((x + 2 * Real.pi * j : ℝ) : ℂ) * Complex.I) =
      (x : ℂ) * Complex.I + (j : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The torus coordinates: the phase modulo `d` and the increments modulo `2L`. -/
def igMixTorus (d L : ℝ) (J : Finset (ℝ × ℂ)) (p : ℝ × (J → ℝ)) : UnitAddTorus (Option J) :=
  fun i => Option.elim i ((p.1 / d : ℝ) : UnitAddCircle) fun x => ((p.2 x / (2 * L) : ℝ) : UnitAddCircle)

/-- The representative in the box `[0, d) × [−L, L)^J` of a point of the torus. -/
def igMixSection (d L : ℝ) (J : Finset (ℝ × ℂ)) (y : UnitAddTorus (Option J)) : ℝ × (J → ℝ) :=
  (d * (AddCircle.equivIco 1 0 (y none) : ℝ),
    fun x => 2 * L * (AddCircle.equivIco 1 (-1 / 2) (y (some x)) : ℝ))

/-- The box `[0, d) × [−L, L)^J`. -/
def igMixBox (d L : ℝ) (J : Finset (ℝ × ℂ)) : Set (ℝ × (J → ℝ)) :=
  {p | p.1 ∈ Ico 0 d ∧ ∀ x, p.2 x ∈ Ico (-L) L}

theorem measurableSet_igMixBox (d L : ℝ) (J : Finset (ℝ × ℂ)) : MeasurableSet (igMixBox d L J) := by
  simp only [igMixBox, Set.ofPred_and, Set.ofPred_forall]
  exact (measurableSet_Ico.preimage measurable_fst).inter
    (MeasurableSet.iInter fun x => measurableSet_Ico.preimage ((measurable_pi_apply x).comp measurable_snd))

theorem measurable_igMixTorus (d L : ℝ) (J : Finset (ℝ × ℂ)) : Measurable (igMixTorus d L J) := by
  have hmk : Measurable (fun t : ℝ => (t : UnitAddCircle)) := (AddCircle.measurePreserving_mk 1 0).measurable
  refine Measurable.of_eval fun i => ?_
  cases i with
  | none => exact hmk.comp (measurable_fst.div_const _)
  | some x => exact hmk.comp (((measurable_pi_apply x).comp measurable_snd).div_const _)

theorem measurable_igMixSection (d L : ℝ) (J : Finset (ℝ × ℂ)) : Measurable (igMixSection d L J) := by
  refine (measurable_const.mul (measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco 1 0).measurable.comp (measurable_pi_apply none)))).prodMk
    (Measurable.of_eval fun x => measurable_const.mul (measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco 1 (-1 / 2)).measurable.comp (measurable_pi_apply (some x)))))

theorem igMixSection_igMixTorus {d L : ℝ} (hd : 0 < d) (hL : 0 < L) {J : Finset (ℝ × ℂ)}
    {p : ℝ × (J → ℝ)} (hp : p ∈ igMixBox d L J) : igMixSection d L J (igMixTorus d L J p) = p := by
  obtain ⟨hp1, hp2⟩ := hp
  refine Prod.ext ?_ (funext fun x => ?_)
  · have hmem : p.1 / d ∈ Ico (0 : ℝ) (0 + 1) := by
      rw [zero_add]
      exact ⟨div_nonneg hp1.1 hd.le, (div_lt_one hd).2 hp1.2⟩
    show d * (AddCircle.equivIco 1 0 ((p.1 / d : ℝ) : UnitAddCircle) : ℝ) = p.1
    rw [AddCircle.equivIco_coe_eq hmem]
    show d * (p.1 / d) = p.1
    field_simp
  · have hmem : p.2 x / (2 * L) ∈ Ico (-1 / 2 : ℝ) (-1 / 2 + 1) := by
      obtain ⟨h1, h2⟩ := hp2 x
      constructor
      · rw [le_div_iff₀ (by positivity)]; linarith
      · rw [div_lt_iff₀ (by positivity)]; linarith
    show 2 * L * (AddCircle.equivIco 1 (-1 / 2) ((p.2 x / (2 * L) : ℝ) : UnitAddCircle) : ℝ) = p.2 x
    rw [AddCircle.equivIco_coe_eq hmem]
    show 2 * L * (p.2 x / (2 * L)) = p.2 x
    field_simp

theorem mFourier_igMixTorus (d L : ℝ) (J : Finset (ℝ × ℂ)) (n : Option J → ℤ) (p : ℝ × (J → ℝ)) :
    UnitAddTorus.mFourier n (igMixTorus d L J p) =
      igMixChar (2 * Real.pi * n none / d) (fun x => 2 * Real.pi * n (some x) / (2 * L)) p := by
  show (∏ i, fourier (n i) (igMixTorus d L J p i)) = _
  rw [Fintype.prod_option]
  simp only [igMixTorus, Option.elim, fourier_coe_apply, igMixChar]
  rw [← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  push_cast
  rw [add_mul, Finset.sum_mul]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun x _ => by ring

theorem tendsto_measureReal_compl_igMixBox {d : ℝ} {J : Finset (ℝ × ℂ)} (ρ : Measure (ℝ × (J → ℝ)))
    [IsProbabilityMeasure ρ] (h1 : ρ {p | p.1 ∈ Ico 0 d} = 1) :
    Tendsto (fun L : ℕ => ρ.real (igMixBox d L J)ᶜ) atTop (𝓝 0) := by
  have hmono : Monotone fun L : ℕ => igMixBox d L J := by
    intro L L' hLL' p hp
    have hc : (L : ℝ) ≤ L' := Nat.cast_le.2 hLL'
    refine ⟨hp.1, fun x => ⟨?_, ?_⟩⟩
    · have := (hp.2 x).1; linarith
    · have := (hp.2 x).2; linarith
  have hU : ⋃ L : ℕ, igMixBox d L J = {p | p.1 ∈ Ico 0 d} := by
    ext p
    simp only [mem_iUnion, mem_ofPred_eq, igMixBox]
    constructor
    · rintro ⟨L, hL⟩; exact hL.1
    · intro hp
      obtain ⟨L, hL⟩ := exists_nat_gt (∑ x, |p.2 x|)
      refine ⟨L, hp, fun x => ⟨?_, ?_⟩⟩
      · have h1 : |p.2 x| ≤ ∑ y, |p.2 y| :=
          Finset.single_le_sum (f := fun y => |p.2 y|) (fun y _ => abs_nonneg _) (Finset.mem_univ x)
        have := neg_abs_le (p.2 x); linarith
      · have h1 : |p.2 x| ≤ ∑ y, |p.2 y| :=
          Finset.single_le_sum (f := fun y => |p.2 y|) (fun y _ => abs_nonneg _) (Finset.mem_univ x)
        have := le_abs_self (p.2 x); linarith
  have ht := tendsto_measure_iUnion_atTop (μ := ρ) hmono
  rw [hU, h1] at ht
  have ht' : Tendsto (fun L : ℕ => ρ.real (igMixBox d L J)) atTop (𝓝 1) := by
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp ht
    simpa [measureReal_def, Function.comp_def] using this
  have := ht'.const_sub 1
  simp only [sub_self] at this
  refine this.congr fun L => ?_
  rw [measureReal_compl (measurableSet_igMixBox d L J), probReal_univ]

end Torus

/-! ### Asymptotic independence of the characters -/

section Char

open LQGMetric LQGMetric.CircleAvg LQGDimension.SegLaw

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → Field} {u : Ω → ℝ} {γ : ℝ}

theorem norm_integral_cexp_le [IsProbabilityMeasure P] (X : Ω → ℝ) :
    ‖∫ ω, Complex.exp (((X ω : ℝ) : ℂ) * Complex.I) ∂P‖ ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => Complex.exp (((X ω : ℝ) : ℂ) * Complex.I))
    (C := 1) (Eventually.of_forall fun ω => le_of_eq (Complex.norm_exp_ofReal_mul_I _))
  simpa using this

/-- **Asymptotic independence of the characters of the array and of its iterated normalized dilations.** -/
theorem tendsto_igMix_char (hγ : γ ∈ Ioo (0 : ℝ) 2) (hh : IsNormalizedWPGFF h P) (hum : Measurable u)
    (hulaw : P.map u = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)]) (hind : IndepFun h u P)
    (J K : Finset (ℝ × ℂ)) (σ : ℝ) (s : J → ℝ) (m : ℤ) (t : K → ℝ) :
    Tendsto (igMixCorr P (fun ω => igMixCoord J (igPosCircleProcess (h ω) (u ω)))
      (fun n ω => igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess (h ω) (u ω))))
      (igMixChar σ s) (igMixChar (2 * Real.pi * m / (2 * Real.pi * igChi γ)) t)) atTop (𝓝 0) := by
  have hP : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have hd : 0 < 2 * Real.pi * igChi γ := by
    have := Sec1.igChi_pos hγ.1 hγ.2
    positivity
  set d := 2 * Real.pi * igChi γ with hd_def
  set c : ℝ := 2 * Real.pi * m / d with hc_def
  set A : Ω → ℝ := fun ω => ∑ x, s x * igMixGauss h J 0 ω x with hA_def
  set B : ℕ → Ω → ℝ := fun n ω => ∑ k, t k * igMixGauss h K n ω k with hB_def
  set G : ℕ → Ω → ℝ := fun n => cInc h ((2 : ℝ) ^ n) 0 1 0 with hG_def
  have hAs : InGSpan (incProc h) A := inGSpan_sum_igMixGauss J 0 s
  have hBs : ∀ n, InGSpan (incProc h) (B n) := fun n => inGSpan_sum_igMixGauss K n t
  have hGs : ∀ n, InGSpan (incProc h) (G n) := fun n => inGSpan_cInc (by positivity) one_pos 0 0
  have hAL : MemLp A 2 P := memLp_of_inGSpan hh.1 hAs
  have hBL : ∀ n, MemLp (B n) 2 P := fun n => memLp_of_inGSpan hh.1 (hBs n)
  have hGL : ∀ n, MemLp (G n) 2 P := fun n => memLp_of_inGSpan hh.1 (hGs n)
  set φ : ℝ → ℂ := fun α => ∫ ω, Complex.exp (((α * u ω : ℝ) : ℂ) * Complex.I) ∂P with hφ_def
  have hφ1 : ∀ α, ‖φ α‖ ≤ 1 := fun α => norm_integral_cexp_le (P := P) fun ω => α * u ω
  -- pointwise forms of the characters
  have hX : ∀ ω, igMixChar σ s (igMixCoord J (igPosCircleProcess (h ω) (u ω))) =
      Complex.exp (((σ * (u ω + circleAvg (h ω) 1 0) + A ω : ℝ) : ℂ) * Complex.I) := by
    intro ω
    rw [igMixCoord_igPosCircleProcess]
    simp only [igMixChar, hA_def, igMixGauss, cInc, pow_zero, one_mul, Complex.ofReal_one]
  have hY : ∀ n, 1 ≤ n → ∀ ω,
      igMixChar c t (igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess (h ω) (u ω)))) =
        Complex.exp (((c * (u ω + circleAvg (h ω) 1 0) + (B n ω + c * G n ω) : ℝ) : ℂ) *
          Complex.I) := by
    intro n hn ω
    obtain ⟨k, hk⟩ := exists_igMixCoord_iterate γ K hn (h ω) (u ω)
    rw [hk]
    simp only [igMixChar]
    have hcd : c * d = 2 * Real.pi * m := by rw [hc_def]; field_simp
    have hsum : (∑ x : K, t x * (if 0 < (x : ℝ × ℂ).1 then
        circleAvg (h ω) ((2 : ℝ) ^ n * (x : ℝ × ℂ).1) ((((2 : ℝ) ^ n : ℝ) : ℂ) * (x : ℝ × ℂ).2) -
          circleAvg (h ω) ((2 : ℝ) ^ n) 0 else 0)) = B n ω := rfl
    rw [hsum]
    have hlin : c * (u ω + circleAvg (h ω) ((2 : ℝ) ^ n) 0 - k * d) + B n ω =
        (c * (u ω + circleAvg (h ω) 1 0) + (B n ω + c * G n ω)) +
          2 * Real.pi * ((-(m * k) : ℤ) : ℝ) := by
      simp only [hG_def, cInc]
      push_cast
      linear_combination (-(k : ℝ)) * hcd
    rw [hlin, cexp_ofReal_add_two_pi_mul_int]
  -- the three integrals
  have I1 : ∫ ω, igMixChar σ s (igMixCoord J (igPosCircleProcess (h ω) (u ω))) ∂P =
      φ σ * ((Real.exp (-(Var[A; P] / 2)) : ℝ) : ℂ) :=
    (integral_congr_ae (Eventually.of_forall hX)).trans
      (integral_cexp_phase_add_inGSpan hh hum hind hAs σ)
  have I2 : ∀ n, 1 ≤ n →
      ∫ ω, igMixChar c t (igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess (h ω) (u ω)))) ∂P =
        φ c * ((Real.exp (-(Var[fun ω => B n ω + c * G n ω; P] / 2)) : ℝ) : ℂ) := fun n hn =>
    (integral_congr_ae (Eventually.of_forall (hY n hn))).trans
      (integral_cexp_phase_add_inGSpan hh hum hind ((hBs n).add ((hGs n).const_mul c)) c)
  have I12 : ∀ n, 1 ≤ n →
      ∫ ω, igMixChar σ s (igMixCoord J (igPosCircleProcess (h ω) (u ω))) *
        igMixChar c t (igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess (h ω) (u ω)))) ∂P =
        φ (σ + c) * ((Real.exp (-(Var[fun ω => A ω + (B n ω + c * G n ω); P] / 2)) : ℝ) : ℂ) := by
    intro n hn
    refine (integral_congr_ae (Eventually.of_forall fun ω => ?_)).trans
      (integral_cexp_phase_add_inGSpan hh hum hind (hAs.add ((hBs n).add ((hGs n).const_mul c)))
        (σ + c))
    rw [hX, hY n hn, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hE : ∀ᶠ n in atTop,
      φ (σ + c) * ((Real.exp (-(Var[fun ω => A ω + (B n ω + c * G n ω); P] / 2)) : ℝ) : ℂ) -
        (φ σ * ((Real.exp (-(Var[A; P] / 2)) : ℝ) : ℂ)) *
          (φ c * ((Real.exp (-(Var[fun ω => B n ω + c * G n ω; P] / 2)) : ℝ) : ℂ)) =
      igMixCorr P (fun ω => igMixCoord J (igPosCircleProcess (h ω) (u ω)))
        (fun n ω => igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess (h ω) (u ω))))
        (igMixChar σ s) (igMixChar c t) n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [igMixCorr]
    rw [I12 n hn, I1, I2 n hn]
  refine Tendsto.congr' hE ?_
  -- the variances of the far increments are constant (scale invariance)
  have hΦ : Measurable fun ω => igPosCircleProcess (h ω) (u ω) :=
    measurable_igPosCircleProcess_comp hh.1.measurable hum
  have hT : MeasurePreserving (igDilationStep γ 2) (P.map fun ω => igPosCircleProcess (h ω) (u ω))
      (P.map fun ω => igPosCircleProcess (h ω) (u ω)) :=
    measurePreserving_igDilationStep hγ two_pos hh hulaw hind
  set gB : ℝ × (K → ℝ) → ℝ := fun q => ∑ k, t k * q.2 k with hgB_def
  have hgB : Measurable gB :=
    Finset.measurable_sum _ fun k _ => measurable_const.mul ((measurable_pi_apply k).comp measurable_snd)
  set VB : ℝ := Var[gB; (P.map fun ω => igPosCircleProcess (h ω) (u ω)).map (igMixCoord K)]
  have hVB : ∀ n, 1 ≤ n → Var[B n; P] = VB := by
    intro n hn
    have hYm : Measurable fun ω =>
        igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess (h ω) (u ω))) :=
      (measurable_igMixCoord K).comp (((measurable_igDilationStep γ 2).iterate n).comp hΦ)
    have hBY : B n = gB ∘ fun ω => igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess (h ω) (u ω))) := by
      funext ω
      obtain ⟨k, hk⟩ := exists_igMixCoord_iterate γ K hn (h ω) (u ω)
      simp only [Function.comp_apply, hgB_def]
      rw [hk]
      rfl
    have hlaw : P.map (fun ω => igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess (h ω) (u ω)))) =
        (P.map fun ω => igPosCircleProcess (h ω) (u ω)).map (igMixCoord K) := by
      rw [show (fun ω => igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess (h ω) (u ω)))) =
          (igMixCoord K ∘ (igDilationStep γ 2)^[n]) ∘ fun ω => igPosCircleProcess (h ω) (u ω) from rfl,
        ← Measure.map_map ((measurable_igMixCoord K).comp ((measurable_igDilationStep γ 2).iterate n)) hΦ,
        ← Measure.map_map (measurable_igMixCoord K) ((measurable_igDilationStep γ 2).iterate n),
        (hT.iterate n).map_eq]
    rw [hBY, ← variance_map hgB.aemeasurable hYm.aemeasurable, hlaw]
  have hVA0 : 0 ≤ Var[A; P] := variance_nonneg _ _
  rcases eq_or_ne m 0 with hm | hm
  · -- the phase frequency vanishes
    have hc0 : c = 0 := by rw [hc_def, hm]; simp
    have hφ0 : φ 0 = 1 := by simp [hφ_def]
    simp only [hc0, zero_mul, add_zero, hφ0, one_mul]
    -- covariance of the near and far increments
    have hC : Tendsto (fun n => cov[A, B n; P]) atTop (𝓝 0) := by
      have hsum : ∀ n, cov[A, B n; P] = ∑ x : J, ∑ k : K,
          s x * t k * cov[fun ω => igMixGauss h J 0 ω x, fun ω => igMixGauss h K n ω k; P] := by
        intro n
        rw [hA_def, hB_def]
        simp only
        rw [covariance_fun_sum_fun_sum
          (fun x => (memLp_of_inGSpan hh.1 (inGSpan_igMixGauss J 0 x)).const_mul (s x))
          (fun k => (memLp_of_inGSpan hh.1 (inGSpan_igMixGauss K n k)).const_mul (t k))]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ => ?_
        rw [covariance_const_mul_left, covariance_const_mul_right]
        ring
      simp only [hsum]
      rw [show (0 : ℝ) = ∑ x : J, ∑ k : K, s x * t k * 0 by simp]
      exact tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun k _ =>
        (tendsto_cov_igMixGauss hh.1 J K x k).const_mul _
    have hCn : Tendsto (fun n => -cov[A, B n; P]) atTop (𝓝 0) := by simpa using hC.neg
    have hexpC : Tendsto (fun n => Real.exp (-cov[A, B n; P]) - 1) atTop (𝓝 0) := by
      have := ((Real.continuous_exp.tendsto 0).comp hCn).sub_const 1
      simpa [Function.comp_def] using this
    have hexpA : Tendsto (fun n => |Real.exp (-cov[A, B n; P]) - 1|) atTop (𝓝 0) := by
      simpa using hexpC.abs
    refine squeeze_zero_norm' ?_ hexpA
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hv := variance_add hAL (hBL n)
    have hv' : Var[fun ω => A ω + B n ω; P] = Var[A; P] + 2 * cov[A, B n; P] + Var[B n; P] := hv
    rw [hv']
    have hVB0 : 0 ≤ Var[B n; P] := variance_nonneg _ _
    have hfac : ((Real.exp (-((Var[A; P] + 2 * cov[A, B n; P] + Var[B n; P]) / 2)) : ℝ) : ℂ) -
        ((Real.exp (-(Var[A; P] / 2)) : ℝ) : ℂ) * ((Real.exp (-(Var[B n; P] / 2)) : ℝ) : ℂ) =
        ((Real.exp (-(Var[A; P] / 2)) * Real.exp (-(Var[B n; P] / 2)) *
          (Real.exp (-cov[A, B n; P]) - 1) : ℝ) : ℂ) := by
      push_cast
      rw [show -((Var[A; P] + 2 * cov[A, B n; P] + Var[B n; P]) / 2 : ℂ) =
        -(Var[A; P] / 2 : ℂ) + -(Var[B n; P] / 2 : ℂ) + -(cov[A, B n; P] : ℂ) by ring,
        Complex.exp_add, Complex.exp_add]
      ring
    rw [show φ σ * ((Real.exp (-((Var[A; P] + 2 * cov[A, B n; P] + Var[B n; P]) / 2)) : ℝ) : ℂ) -
        φ σ * ((Real.exp (-(Var[A; P] / 2)) : ℝ) : ℂ) * ((Real.exp (-(Var[B n; P] / 2)) : ℝ) : ℂ) =
        φ σ * (((Real.exp (-((Var[A; P] + 2 * cov[A, B n; P] + Var[B n; P]) / 2)) : ℝ) : ℂ) -
        ((Real.exp (-(Var[A; P] / 2)) : ℝ) : ℂ) * ((Real.exp (-(Var[B n; P] / 2)) : ℝ) : ℂ)) by ring,
      hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have e1 : Real.exp (-(Var[A; P] / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have e2 : Real.exp (-(Var[B n; P] / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hab : 0 ≤ |Real.exp (-cov[A, B n; P]) - 1| := abs_nonneg _
    calc ‖φ σ‖ * (Real.exp (-(Var[A; P] / 2)) * Real.exp (-(Var[B n; P] / 2)) *
          |Real.exp (-cov[A, B n; P]) - 1|)
        ≤ 1 * (1 * 1 * |Real.exp (-cov[A, B n; P]) - 1|) := by
          gcongr
          · exact hφ1 σ
    _ = |Real.exp (-cov[A, B n; P]) - 1| := by ring
  · -- the phase frequency does not vanish: the variance of `h_{2^n}(0)` diverges
    have hc : c ≠ 0 := by
      rw [hc_def]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (Int.cast_ne_zero.2 hm))
        hd.ne'
    have hVG : ∀ n : ℕ, Var[fun ω => c * G n ω; P] = c ^ 2 * (n * Real.log 2) := by
      intro n
      rw [variance_const_mul, hG_def]
      simp only
      rw [variance_cInc_one hh.1 (by positivity) 0, Real.log_pow, abs_of_nonneg]
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)
    have hlin : ∀ M : ℝ, Tendsto (fun n : ℕ => c ^ 2 * (n * Real.log 2) / 2 - M) atTop atTop := by
      intro M
      have hpos : 0 < c ^ 2 * Real.log 2 / 2 := by
        have := Real.log_pos one_lt_two
        positivity
      have := (tendsto_natCast_atTop_atTop.const_mul_atTop hpos).atTop_add (tendsto_const_nhds (x := -M))
      refine this.congr fun n => ?_
      ring
    have hdiv : ∀ V : ℕ → ℝ, (∀ᶠ n in atTop, c ^ 2 * (n * Real.log 2) / 2 - (2 * Var[A; P] + 2 * VB) ≤ V n) →
        Tendsto (fun n => Real.exp (-(V n / 2))) atTop (𝓝 0) := by
      intro V hV
      have hVt : Tendsto V atTop atTop := tendsto_atTop_mono' atTop hV (hlin _)
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hVt.atTop_div_const two_pos))
    have hlow12 : ∀ᶠ n in atTop, c ^ 2 * (n * Real.log 2) / 2 - (2 * Var[A; P] + 2 * VB) ≤
        Var[fun ω => A ω + (B n ω + c * G n ω); P] := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have e : (fun ω => A ω + (B n ω + c * G n ω)) = fun ω => (A ω + B n ω) + c * G n ω := by
        funext ω; ring
      rw [e]
      have h1 : Var[fun ω => c * G n ω; P] / 2 - Var[fun ω => A ω + B n ω; P] ≤
          Var[fun ω => (A ω + B n ω) + c * G n ω; P] :=
        variance_add_ge (P := P) (X := fun ω => A ω + B n ω) (hAL.add (hBL n)) ((hGL n).const_mul c)
      have h2 := variance_add_le (P := P) hAL (hBL n)
      rw [hVG n] at h1
      rw [hVB n hn] at h2
      linarith
    have hlow2 : ∀ᶠ n in atTop, c ^ 2 * (n * Real.log 2) / 2 - (2 * Var[A; P] + 2 * VB) ≤
        Var[fun ω => B n ω + c * G n ω; P] := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have h1 := variance_add_ge (P := P) (hBL n) ((hGL n).const_mul c)
      rw [hVG n, hVB n hn] at h1
      have hVB0 : 0 ≤ VB := by rw [← hVB n hn]; exact variance_nonneg _ _
      linarith
    have t12 := hdiv _ hlow12
    have t2 := hdiv _ hlow2
    refine squeeze_zero_norm' ?_ (by simpa using t12.add t2)
    refine Eventually.of_forall fun n => ?_
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc ‖φ (σ + c)‖ * Real.exp (-(Var[fun ω => A ω + (B n ω + c * G n ω); P] / 2))
          ≤ 1 * Real.exp (-(Var[fun ω => A ω + (B n ω + c * G n ω); P] / 2)) := by
            gcongr; exact hφ1 _
        _ = _ := one_mul _
    · rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      have e1 : Real.exp (-(Var[A; P] / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      calc ‖φ σ‖ * Real.exp (-(Var[A; P] / 2)) *
            (‖φ c‖ * Real.exp (-(Var[fun ω => B n ω + c * G n ω; P] / 2)))
          ≤ 1 * 1 * (1 * Real.exp (-(Var[fun ω => B n ω + c * G n ω; P] / 2))) := by
            gcongr
            · exact hφ1 _
            · exact hφ1 _
        _ = _ := by ring

end Char

/-! ### Assembly -/

section Assembly

open LQGMetric

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → Field} {u : Ω → ℝ} {γ : ℝ}

theorem measureReal_preimage_eq_map {β : Type*} [MeasurableSpace β] {f : Ω → β} (hf : Measurable f)
    {S : Set β} (hS : MeasurableSet S) : P.real (f ⁻¹' S) = (P.map f).real S := by
  rw [measureReal_def, measureReal_def, Measure.map_apply hf hS]

theorem abs_measureReal_inter_sub_le [IsProbabilityMeasure P] {E E' F F' G H : Set Ω}
    (hE : MeasurableSet E) (hE' : MeasurableSet E') (hF : MeasurableSet F) (hF' : MeasurableSet F')
    (hEG : E ∆ E' ⊆ G) (hFH : F ∆ F' ⊆ H) :
    |(P.real (E ∩ F) - P.real E * P.real F) - (P.real (E' ∩ F') - P.real E' * P.real F')| ≤
      2 * (P.real G + P.real H) := by
  have h1 : |P.real (E ∩ F) - P.real (E' ∩ F')| ≤ P.real G + P.real H := by
    refine (abs_measureReal_sub_le_measureReal_symmDiff (hE.inter hF).nullMeasurableSet
      (hE'.inter hF').nullMeasurableSet).trans ((measureReal_mono ?_).trans (measureReal_union_le _ _))
    intro ω hω
    have h1 := @hEG ω
    have h2 := @hFH ω
    simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union] at hω h1 h2 ⊢
    tauto
  have hE1 : |P.real E - P.real E'| ≤ P.real G :=
    (abs_measureReal_sub_le_measureReal_symmDiff hE.nullMeasurableSet hE'.nullMeasurableSet).trans
      (measureReal_mono hEG)
  have hF1 : |P.real F - P.real F'| ≤ P.real H :=
    (abs_measureReal_sub_le_measureReal_symmDiff hF.nullMeasurableSet hF'.nullMeasurableSet).trans
      (measureReal_mono hFH)
  have h2 : |P.real E * P.real F - P.real E' * P.real F'| ≤ P.real G + P.real H := by
    have e : P.real E * P.real F - P.real E' * P.real F' =
        (P.real E - P.real E') * P.real F + P.real E' * (P.real F - P.real F') := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg measureReal_nonneg]
      calc |P.real E - P.real E'| * P.real F ≤ |P.real E - P.real E'| * 1 :=
            mul_le_mul_of_nonneg_left measureReal_le_one (abs_nonneg _)
        _ ≤ P.real G := by rw [mul_one]; exact hE1
    · rw [abs_mul, abs_of_nonneg measureReal_nonneg]
      calc P.real E' * |P.real F - P.real F'| ≤ 1 * |P.real F - P.real F'| :=
            mul_le_mul_of_nonneg_right measureReal_le_one (abs_nonneg _)
        _ ≤ P.real H := by rw [one_mul]; exact hF1
  have e : (P.real (E ∩ F) - P.real E * P.real F) - (P.real (E' ∩ F') - P.real E' * P.real F') =
      (P.real (E ∩ F) - P.real (E' ∩ F')) - (P.real E * P.real F - P.real E' * P.real F') := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith

/-- **Asymptotic independence of the cylinder events of the array and of its iterated normalized
dilations.** -/
theorem tendsto_igMix_cyl (hγ : γ ∈ Ioo (0 : ℝ) 2) (hh : IsNormalizedWPGFF h P) (hum : Measurable u)
    (hulaw : P.map u = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)]) (hind : IndepFun h u P)
    (J K : Finset (ℝ × ℂ)) {A' : Set (ℝ × (J → ℝ))} {B' : Set (ℝ × (K → ℝ))}
    (hA' : MeasurableSet A') (hB' : MeasurableSet B') :
    Tendsto (fun n : ℕ =>
      P.real ((fun ω => igMixCoord J (igPosCircleProcess (h ω) (u ω))) ⁻¹' A' ∩
        (fun ω => igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess (h ω) (u ω)))) ⁻¹' B') -
      P.real ((fun ω => igMixCoord J (igPosCircleProcess (h ω) (u ω))) ⁻¹' A') *
        P.real ((fun ω => igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess (h ω) (u ω)))) ⁻¹'
          B')) atTop (𝓝 0) := by
  have hP : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have hd : 0 < 2 * Real.pi * igChi γ := by
    have := Sec1.igChi_pos hγ.1 hγ.2
    positivity
  set d := 2 * Real.pi * igChi γ with hd_def
  have hΦ : Measurable fun ω => igPosCircleProcess (h ω) (u ω) :=
    measurable_igPosCircleProcess_comp hh.1.measurable hum
  set μ := P.map fun ω => igPosCircleProcess (h ω) (u ω) with hμ_def
  have hμP : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hΦ.aemeasurable).mpr inferInstance
  have hT : MeasurePreserving (igDilationStep γ 2) μ μ :=
    measurePreserving_igDilationStep hγ two_pos hh hulaw hind
  set X : Ω → ℝ × (J → ℝ) := fun ω => igMixCoord J (igPosCircleProcess (h ω) (u ω)) with hX_def
  set Y : ℕ → Ω → ℝ × (K → ℝ) :=
    fun n ω => igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess (h ω) (u ω))) with hY_def
  have hXm : Measurable X := (measurable_igMixCoord J).comp hΦ
  have hYm : ∀ n, Measurable (Y n) := fun n =>
    (measurable_igMixCoord K).comp (((measurable_igDilationStep γ 2).iterate n).comp hΦ)
  have hlawX : P.map X = μ.map (igMixCoord J) := (Measure.map_map (measurable_igMixCoord J) hΦ).symm
  have hlawY : ∀ n, P.map (Y n) = μ.map (igMixCoord K) := fun n => by
    rw [show Y n = (igMixCoord K ∘ (igDilationStep γ 2)^[n]) ∘ fun ω => igPosCircleProcess (h ω) (u ω)
        from rfl,
      ← Measure.map_map ((measurable_igMixCoord K).comp ((measurable_igDilationStep γ 2).iterate n)) hΦ,
      ← Measure.map_map (measurable_igMixCoord K) ((measurable_igDilationStep γ 2).iterate n),
      (hT.iterate n).map_eq]
  have hphase : ∀ I : Finset (ℝ × ℂ), (μ.map (igMixCoord I)) {p | p.1 ∈ Ico 0 d} = 1 := by
    intro I
    have hfm : MeasurableSet {p : ℝ × (I → ℝ) | p.1 ∈ Ico 0 d} := measurableSet_Ico.preimage measurable_fst
    rw [Measure.map_map (measurable_igMixCoord I) hΦ,
      Measure.map_apply ((measurable_igMixCoord I).comp hΦ) hfm]
    have hset : (igMixCoord I ∘ fun ω => igPosCircleProcess (h ω) (u ω)) ⁻¹' {p | p.1 ∈ Ico 0 d} =
        (fun ω => u ω + circleAvg (h ω) 1 0) ⁻¹' Ico 0 d := by
      ext ω
      simp only [Set.mem_preimage, Function.comp_apply, Set.mem_ofPred_eq,
        igMixCoord_igPosCircleProcess]
    have hsm : Measurable fun ω => u ω + circleAvg (h ω) 1 0 :=
      hum.add ((measurable_circleAvg_left 1 0).comp hh.1.measurable)
    rw [hset, ← Measure.map_apply hsm measurableSet_Ico]
    have hae : (fun ω => u ω + circleAvg (h ω) 1 0) =ᵐ[P] u :=
      hh.2.mono fun ω hω => by simp [hω]
    rw [Measure.map_congr hae, hulaw, ProbabilityTheory.cond_apply measurableSet_Ico, Set.inter_self,
      ENNReal.inv_mul_cancel]
    · simp [Real.volume_Ico, hd]
    · simp [Real.volume_Ico]
  have : IsProbabilityMeasure (μ.map (igMixCoord J)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_igMixCoord J).aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (μ.map (igMixCoord K)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_igMixCoord K).aemeasurable).mpr inferInstance
  have hbJ := tendsto_measureReal_compl_igMixBox (μ.map (igMixCoord J)) (hphase J)
  have hbK := tendsto_measureReal_compl_igMixBox (μ.map (igMixCoord K)) (hphase K)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L₀, hLJ, hLK, hL1⟩ : ∃ L₀ : ℕ, (μ.map (igMixCoord J)).real (igMixBox d L₀ J)ᶜ < ε / 8 ∧
      (μ.map (igMixCoord K)).real (igMixBox d L₀ K)ᶜ < ε / 8 ∧ 1 ≤ L₀ :=
    ((hbJ.eventually (gt_mem_nhds (by positivity))).and
      ((hbK.eventually (gt_mem_nhds (by positivity))).and (eventually_ge_atTop 1))).exists
  have hL : (0 : ℝ) < (L₀ : ℝ) := by exact_mod_cast hL1
  set L : ℝ := (L₀ : ℝ) with hL_def
  set Ξ : Ω → UnitAddTorus (Option J) := fun ω => igMixTorus d L J (X ω) with hΞ_def
  set Υ : ℕ → Ω → UnitAddTorus (Option K) := fun n ω => igMixTorus d L K (Y (n + 1) ω) with hΥ_def
  have hΞ : Measurable Ξ := (measurable_igMixTorus d L J).comp hXm
  have hΥ : ∀ n, Measurable (Υ n) := fun n => (measurable_igMixTorus d L K).comp (hYm (n + 1))
  have hlawΥ : ∀ n, P.map (Υ n) = P.map (Υ 0) := fun n => by
    rw [show Υ n = igMixTorus d L K ∘ Y (n + 1) from rfl, show Υ 0 = igMixTorus d L K ∘ Y (0 + 1) from rfl,
      ← Measure.map_map (measurable_igMixTorus d L K) (hYm (n + 1)),
      ← Measure.map_map (measurable_igMixTorus d L K) (hYm (0 + 1)), hlawY, hlawY]
  have hcorr : ∀ f ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Option J))),
      ∀ g ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Option K))),
      Tendsto (igMixCorr P Ξ Υ f g) atTop (𝓝 0) := by
    refine tendsto_igMixCorr_span _ _ hΞ hΥ fun a b => ?_
    have h5 := tendsto_igMix_char hγ hh hum hulaw hind J K (2 * Real.pi * a none / d)
      (fun x => 2 * Real.pi * a (some x) / (2 * L)) (b none) (fun k => 2 * Real.pi * b (some k) / (2 * L))
    refine (h5.comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
    simp only [Function.comp_apply, igMixCorr, hΞ_def, hΥ_def, mFourier_igMixTorus]
    rfl
  have hmain := tendsto_igMixCorr_indicator_of_dense UnitAddTorus.span_mFourier_closure_eq_top
    UnitAddTorus.span_mFourier_closure_eq_top hΞ hΥ hlawΥ hcorr
    ((measurable_igMixSection d L J) hA') ((measurable_igMixSection d L K) hB')
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hmain (ε / 4) (by positivity)
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hNk := hN k (by omega)
  rw [dist_zero_right, igMixCorr_indicator hΞ hΥ ((measurable_igMixSection d L J) hA')
    ((measurable_igMixSection d L K) hB'), Complex.norm_real, Real.norm_eq_abs] at hNk
  rw [Real.dist_eq, sub_zero]
  have hEG : (X ⁻¹' A') ∆ (Ξ ⁻¹' (igMixSection d L J ⁻¹' A')) ⊆ X ⁻¹' (igMixBox d L J)ᶜ := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    intro hbox
    have hsec := igMixSection_igMixTorus hd hL hbox
    simp only [Set.mem_symmDiff, Set.mem_preimage, hΞ_def, hsec] at hω
    tauto
  have hFH : (Y (k + 1) ⁻¹' B') ∆ (Υ k ⁻¹' (igMixSection d L K ⁻¹' B')) ⊆
      Y (k + 1) ⁻¹' (igMixBox d L K)ᶜ := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    intro hbox
    have hsec := igMixSection_igMixTorus hd hL hbox
    simp only [Set.mem_symmDiff, Set.mem_preimage, hΥ_def, hsec] at hω
    tauto
  have hcmp := abs_measureReal_inter_sub_le (P := P) (hXm hA') (hΞ ((measurable_igMixSection d L J) hA'))
    (hYm (k + 1) hB') (hΥ k ((measurable_igMixSection d L K) hB')) hEG hFH
  have hG : P.real (X ⁻¹' (igMixBox d L J)ᶜ) < ε / 8 := by
    rw [measureReal_preimage_eq_map hXm (measurableSet_igMixBox d L J).compl, hlawX]; exact hLJ
  have hH : P.real (Y (k + 1) ⁻¹' (igMixBox d L K)ᶜ) < ε / 8 := by
    rw [measureReal_preimage_eq_map (hYm (k + 1)) (measurableSet_igMixBox d L K).compl, hlawY]; exact hLK
  have habs := abs_sub_abs_le_abs_sub
    (P.real (X ⁻¹' A' ∩ Y (k + 1) ⁻¹' B') - P.real (X ⁻¹' A') * P.real (Y (k + 1) ⁻¹' B'))
    (P.real (Ξ ⁻¹' (igMixSection d L J ⁻¹' A') ∩ Υ k ⁻¹' (igMixSection d L K ⁻¹' B')) -
      P.real (Ξ ⁻¹' (igMixSection d L J ⁻¹' A')) * P.real (Υ k ⁻¹' (igMixSection d L K ⁻¹' B')))
  linarith

/-- **Mixing for a measurable phase.** -/
theorem igFieldDilationMixing_of_measurable (hγ : γ ∈ Ioo (0 : ℝ) 2) (hh : IsNormalizedWPGFF h P)
    (hum : Measurable u) (hulaw : P.map u = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)])
    (hind : IndepFun h u P) {S₁ S₂ : Set (ℝ × ℂ → ℝ)} (hS₁ : MeasurableSet S₁)
    (hS₂ : MeasurableSet S₂) :
    Tendsto (fun n : ℕ => (P.map fun ω => igPosCircleProcess (h ω) (u ω))
        (S₁ ∩ (igDilationStep γ 2)^[n] ⁻¹' S₂)) atTop
      (𝓝 ((P.map fun ω => igPosCircleProcess (h ω) (u ω)) S₁ *
        (P.map fun ω => igPosCircleProcess (h ω) (u ω)) S₂)) := by
  have hP : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have hΦ : Measurable fun ω => igPosCircleProcess (h ω) (u ω) :=
    measurable_igPosCircleProcess_comp hh.1.measurable hum
  set μ := P.map fun ω => igPosCircleProcess (h ω) (u ω) with hμ_def
  have hμP : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hΦ.aemeasurable).mpr inferInstance
  have hT : MeasurePreserving (igDilationStep γ 2) μ μ :=
    measurePreserving_igDilationStep hγ two_pos hh hulaw hind
  refine tendsto_measure_inter_preimage_of_isSetRing isSetRing_measurableCylinders
    ⟨{univ}, Set.countable_singleton _, Set.singleton_subset_iff.2 (univ_mem_measurableCylinders _),
      by simp⟩ generateFrom_measurableCylinders.symm hT ?_ hS₁ hS₂
  intro A hA B hB
  obtain ⟨J, SA, hSA, rfl⟩ := (mem_measurableCylinders A).1 hA
  obtain ⟨K, SB, hSB, rfl⟩ := (mem_measurableCylinders B).1 hB
  have hA' : MeasurableSet (igMixRecover J ⁻¹' SA) := measurable_igMixRecover J hSA
  have hB' : MeasurableSet (igMixRecover K ⁻¹' SB) := measurable_igMixRecover K hSB
  have hcylA : cylinder J SA = igMixCoord J ⁻¹' (igMixRecover J ⁻¹' SA) := by
    ext f
    rw [mem_cylinder, Set.mem_preimage, Set.mem_preimage, igMixRecover_igMixCoord]
  have hcylB : cylinder K SB = igMixCoord K ⁻¹' (igMixRecover K ⁻¹' SB) := by
    ext f
    rw [mem_cylinder, Set.mem_preimage, Set.mem_preimage, igMixRecover_igMixCoord]
  have hcAm : MeasurableSet (cylinder J SA : Set (ℝ × ℂ → ℝ)) := by
    rw [hcylA]; exact measurable_igMixCoord J hA'
  have hcBm : MeasurableSet (cylinder K SB : Set (ℝ × ℂ → ℝ)) := by
    rw [hcylB]; exact measurable_igMixCoord K hB'
  have hcore := tendsto_igMix_cyl hγ hh hum hulaw hind J K hA' hB'
  have e1 : ∀ n : ℕ, μ.real (cylinder J SA ∩ (igDilationStep γ 2)^[n] ⁻¹' cylinder K SB) =
      P.real ((fun ω => igMixCoord J (igPosCircleProcess (h ω) (u ω))) ⁻¹' (igMixRecover J ⁻¹' SA) ∩
        (fun ω => igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess (h ω) (u ω)))) ⁻¹'
          (igMixRecover K ⁻¹' SB)) := fun n => by
    rw [hμ_def, ← measureReal_preimage_eq_map hΦ
      (hcAm.inter (((measurable_igDilationStep γ 2).iterate n) hcBm)), hcylA, hcylB]
    rfl
  have e2 : μ.real (cylinder J SA) =
      P.real ((fun ω => igMixCoord J (igPosCircleProcess (h ω) (u ω))) ⁻¹' (igMixRecover J ⁻¹' SA)) := by
    rw [hμ_def, ← measureReal_preimage_eq_map hΦ hcAm, hcylA]
    rfl
  have e3 : ∀ n : ℕ, μ.real (cylinder K SB) =
      P.real ((fun ω => igMixCoord K ((igDilationStep γ 2)^[n] (igPosCircleProcess (h ω) (u ω)))) ⁻¹'
        (igMixRecover K ⁻¹' SB)) := fun n => by
    have hpre : μ.real ((igDilationStep γ 2)^[n] ⁻¹' cylinder K SB) = μ.real (cylinder K SB) := by
      simp only [measureReal_def]
      rw [(hT.iterate n).measure_preimage hcBm.nullMeasurableSet]
    rw [← hpre, hμ_def, ← measureReal_preimage_eq_map hΦ (((measurable_igDilationStep γ 2).iterate n) hcBm),
      hcylB]
    rfl
  have := hcore.add_const (μ.real (cylinder J SA) * μ.real (cylinder K SB))
  rw [zero_add] at this
  refine this.congr fun n => ?_
  rw [e1 n, e2, e3 n]
  ring

end Assembly

/-- **Mixing of the whole-plane GFF modulo `2πχ` under the normalized dilation by `2`** (`IGFieldDilationMixing`;
Gwynne–Miller–Sheffield, arXiv:1705.11161, Remark A.2, in its mixing form). -/
theorem igFieldDilationMixing (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) : IGFieldDilationMixing γ hγ := by
  intro Ω' _ P' h u hh hulaw hind S₁ S₂ hS₁ hS₂
  have hP : IsProbabilityMeasure P' := hh.1.gaussian.isProbabilityMeasure
  have huae : AEMeasurable u P' := aemeasurable_of_map_eq_igUniform hulaw
  have hμ : (P'.map fun ω => igPosCircleProcess (h ω) (u ω)) =
      P'.map fun ω => igPosCircleProcess (h ω) (huae.mk u ω) := by
    refine Measure.map_congr ?_
    filter_upwards [huae.ae_eq_mk] with ω hω
    simp only [hω]
  have hulaw' : P'.map (huae.mk u) = volume[|Ico (0 : ℝ) (2 * Real.pi * igChi γ)] := by
    rw [← Measure.map_congr huae.ae_eq_mk]
    exact hulaw
  have hind' : IndepFun h (huae.mk u) P' := hind.congr (ae_eq_refl _) huae.ae_eq_mk
  rw [hμ]
  exact igFieldDilationMixing_of_measurable hγ hh huae.measurable_mk hulaw' hind' hS₁ hS₂

end MatedCRT
