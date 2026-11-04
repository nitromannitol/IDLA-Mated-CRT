import MatedCRT.Steps.Sec3.ConvergenceNormalizedExitTime

/-!
# Uniform approximation under the truncated Green integral

This estimate is the deterministic integration step in Lemma 3.7, Step 2.
It applies directly to uniform Green-kernel convergence away from the pole;
no Hölder estimate on the annulus is required.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped ENNReal

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

/-- Uniform convergence in probability passes to integrals against a random
measure if the mass of the integration set is bounded in probability and the
integrands are almost surely integrable. No measurability of the random
measure or the events is needed. -/
theorem tendstoInProbability_setIntegral_of_uniformOn
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (μ : Ω → Measure α) (D : Set α)
    (F : ℝ → Ω → α → ℝ) (g : Ω → α → ℝ)
    (hmass : ∀ e : ℝ≥0∞, 0 < e → ∃ K : ℝ, 0 < K ∧
      P {ω | ENNReal.ofReal K < μ ω D} ≤ e)
    (hint : ∀ ε, 0 < ε → ∀ᵐ ω ∂P, IntegrableOn (F ε ω) D (μ ω) ∧ IntegrableOn (g ω) D (μ ω))
    (hconv : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun ε => P {ω | ∃ x ∈ D, δ < |F ε ω x - g ω x|}) (𝓝[>] 0) (𝓝 0)) :
    TendstoInProbability P (fun ε ω => ∫ x in D, F ε ω x ∂μ ω)
      (fun ω => ∫ x in D, g ω x ∂μ ω) := by
  classical
  intro t ht
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨K, hK, hKprob⟩ := hmass (e / 2) he2
  let δ := t / (K + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (K + 1) = t := by
    dsimp [δ]
    field_simp
  have hsmall := ENNReal.tendsto_nhds_zero.1 (hconv δ hδ) (e / 2) he2
  filter_upwards [hsmall, self_mem_nhdsWithin] with ε hε hεpos
  calc
    P {ω | t < |(∫ x in D, F ε ω x ∂μ ω) - ∫ x in D, g ω x ∂μ ω|} ≤
        P ({ω | ∃ x ∈ D, δ < |F ε ω x - g ω x|} ∪
          {ω | ENNReal.ofReal K < μ ω D}) := by
      apply measure_mono_ae
      filter_upwards [hint ε hεpos] with ω hω
      intro hbad
      by_contra hno
      have hmassle : μ ω D ≤ ENNReal.ofReal K := le_of_not_gt (fun h => hno (Or.inr h))
      have hfin : μ ω D < ⊤ := hmassle.trans_lt ENNReal.ofReal_lt_top
      have hreal : (μ ω).real D ≤ K := by
        have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmassle
        simpa [Measure.real, ENNReal.toReal_ofReal hK.le] using h
      have hbound : ∀ x ∈ D, |F ε ω x - g ω x| ≤ δ := by
        intro x hx
        exact le_of_not_gt (fun h => hno (Or.inl ⟨x, hx, h⟩))
      have h := abs_setIntegral_sub_le_of_uniform_bound hfin hω.1 hω.2 hbound
      have hδmass := mul_nonneg hδ.le (sub_nonneg.mpr hreal)
      linarith
    _ ≤ _ := measure_union_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add hε hKprob
    _ = e := ENNReal.add_halves e

end MatedCRT
