import MatedCRT.Steps.Sec3.ConvergenceNormalizedExitTime

/-!
# Uniform approximation under the truncated Green integral

This estimate is the deterministic integration step in Lemma 3.7, Step 2.
It applies directly to uniform Green-kernel convergence away from the pole;
no Hölder estimate on the annulus is required.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology

/-- Uniform approximation on a finite-measure set bounds the difference of
the corresponding integrals by the approximation error times its mass. -/
theorem abs_setIntegral_sub_le_of_uniform_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {D : Set α} {f g : α → ℝ} {δ : ℝ}
    (hD : μ D < ⊤) (hf : IntegrableOn f D μ) (hg : IntegrableOn g D μ)
    (hbound : ∀ x ∈ D, |f x - g x| ≤ δ) :
    |(∫ x in D, f x ∂μ) - ∫ x in D, g x ∂μ| ≤ δ * μ.real D := by
  rw [← integral_sub hf hg]
  change ‖∫ x in D, (f - g) x ∂μ‖ ≤ δ * μ.real D
  apply norm_setIntegral_le_of_norm_le_const_ae' hD
  exact Filter.Eventually.of_forall fun x hx => by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hbound x hx

/-- Uniform convergence on a finite-measure set passes to integrals whenever
the functions and their limit are integrable on that set. -/
theorem tendsto_setIntegral_of_uniformOn {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {D : Set α} {l : Filter ι} {F : ι → α → ℝ} {g : α → ℝ}
    (hD : μ D < ⊤) (hF : ∀ i, IntegrableOn (F i) D μ) (hg : IntegrableOn g D μ)
    (hconv : TendstoUniformlyOn F g l D) :
    Tendsto (fun i => ∫ x in D, F i x ∂μ) l (𝓝 (∫ x in D, g x ∂μ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hmass⟩ := exists_pos_mul_lt hε (μ.real D)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hconv) δ hδ] with i hi
  have hbound : ∀ x ∈ D, |F i x - g x| ≤ δ := by
    intro x hx
    have := hi x hx
    simpa only [Real.dist_eq, abs_sub_comm] using this.le
  have h := abs_setIntegral_sub_le_of_uniform_bound hD (hF i) hg hbound
  rw [Real.dist_eq]
  exact lt_of_le_of_lt h (by simpa [mul_comm] using hmass)

end MatedCRT
