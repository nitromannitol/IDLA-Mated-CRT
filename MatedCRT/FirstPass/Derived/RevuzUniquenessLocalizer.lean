import MatedCRT.FirstPass.Derived.RevuzWindowFormula

/-!
# Localizers and the first moment of the window integral

Two elementary inputs of the uniqueness theorem for the Revuz correspondence of positive continuous additive
functionals of planar Brownian motion (Revuz–Yor (1999), Chapter X, Theorem 2.6).

* A σ-finite measure admits an increasing sequence of measurable localizers `0 ≤ h_j ≤ 1` of finite integral
  with `h_j(x) = 1` for all large `j`, namely the indicators of the spanning sets.
* The first moment of the regularized window integral under Lebesgue starts is linear in the window length:
  `∫ dz E_z ∫_{(0,h]} g(B_s) dĀ_s = h · ∫ g dμ_A` for `h ≥ 0`, where `μ_A` is the Revuz measure. Consequently, if
  `∫ g dμ_A < ∞`, then for Lebesgue-almost every start `z` the expected window integral is finite for every window
  length.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- **Localizers for a σ-finite measure.** A σ-finite measure `μ` admits measurable functions `0 ≤ h_j ≤ 1` of
finite `μ`-integral, increasing in `j`, such that every point `x` has `h_j(x) = 1` for all large `j`. -/
theorem exists_localizer_of_sigmaFinite {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] :
    ∃ h : ℕ → α → ℝ≥0∞, (∀ j, Measurable (h j)) ∧ (∀ j x, h j x ≤ 1) ∧
      (∀ j, ∫⁻ x, h j x ∂μ < ∞) ∧ (∀ x, Monotone fun j => h j x) ∧ ∀ x, ∀ᶠ j in atTop, h j x = 1 := by
  refine ⟨fun j => (spanningSets μ j).indicator 1,
    fun j => measurable_one.indicator (measurableSet_spanningSets μ j), fun j x => ?_, fun j => ?_,
    fun x i j hij => ?_, fun x => ?_⟩
  · by_cases hx : x ∈ spanningSets μ j <;> simp [hx]
  · rw [lintegral_indicator_one (measurableSet_spanningSets μ j)]
    exact measure_spanningSets_lt_top μ j
  · exact indicator_le_indicator_of_subset (monotone_spanningSets μ hij) (fun _ => zero_le) x
  · filter_upwards [eventually_ge_atTop (spanningSetsIndex μ x)] with j hj
    exact indicator_of_mem (monotone_spanningSets μ hj (mem_spanningSetsIndex μ x)) _

/-- The regularized window integral is monotone in the window length. -/
theorem clockWindowIntegral_mono (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (g : ℂ → ℝ≥0∞) {h h' : ℝ} (hh : h ≤ h')
    (ω : ContinuousPath ℂ) : clockWindowIntegral A g h ω ≤ clockWindowIntegral A g h' ω :=
  lintegral_mono_set (Ioc_subset_Ioc_right hh)

/-- **First moment of the regularized window integral.** For a positive continuous additive functional `A` of
planar Brownian motion, every measurable `g ≥ 0` and every window length `h ≥ 0`,
`∫ dz E_z ∫_{(0,h]} g(B_s) dĀ_s = h · ∫ g dμ_A`. -/
theorem lintegral_clockWindowIntegral_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) {h : ℝ} (hh : 0 ≤ h) :
    ∫⁻ z, ∫⁻ ω, clockWindowIntegral A g h ω ∂planarLaw z =
      ENNReal.ofReal h * ∫⁻ y, g y ∂revuz planarLaw A := by
  rw [← lintegral_setLIntegral_Ioc_window_eq hA 0 hg h]
  exact lintegral_setLIntegral_Ioc_eq_ofReal_mul_lintegral_revuz hA 0 hg hh

/-- The expected regularized window integral is measurable in the starting point. -/
theorem measurable_lintegral_clockWindowIntegral {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t))
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) (h : ℝ) :
    Measurable fun z => ∫⁻ ω, clockWindowIntegral A g h ω ∂planarLaw z :=
  (Measure.measurable_lintegral (measurable_clockWindowIntegral hA hg h)).comp measurable_planarLaw

/-- **Finiteness of the expected window integral for almost every start.** If `∫ g dμ_A < ∞`, then for
Lebesgue-almost every starting point `z`, `E_z ∫_{(0,h]} g(B_s) dĀ_s < ∞` for every window length `h`. -/
theorem ae_lintegral_clockWindowIntegral_lt_top {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) (hfin : ∫⁻ y, g y ∂revuz planarLaw A ≠ ∞) :
    ∀ᵐ z, ∀ h : ℝ, ∫⁻ ω, clockWindowIntegral A g h ω ∂planarLaw z < ∞ := by
  have hn : ∀ n : ℕ, ∀ᵐ z, ∫⁻ ω, clockWindowIntegral A g n ω ∂planarLaw z < ∞ := fun n =>
    ae_lt_top (measurable_lintegral_clockWindowIntegral hA.meas hg n) (by
      rw [lintegral_clockWindowIntegral_eq hA hg n.cast_nonneg]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
  filter_upwards [ae_all_iff.2 hn] with z hz h
  obtain ⟨n, hn⟩ := exists_nat_ge h
  exact (lintegral_mono fun ω => clockWindowIntegral_mono A g hn ω).trans_lt (hz n)

end MatedCRT
