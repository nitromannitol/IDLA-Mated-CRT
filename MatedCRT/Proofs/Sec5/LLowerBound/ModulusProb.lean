import MatedCRT.Proofs.Sec5.LLowerBound.ProperProb

/-! Measurable moduli of continuity for the space-filling curve. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- A uniform modulus bound on a fixed time interval is closed in the
compact-open topology on continuous paths. -/
theorem isClosed_curve_modulus (T δ d : ℝ) :
    IsClosed {f : C(ℝ, ℂ) | ∀ s ∈ Icc (-T) T, ∀ t ∈ Icc (-T) T,
      dist s t ≤ δ → dist (f s) (f t) ≤ d} := by
  have heq : {f : C(ℝ, ℂ) | ∀ s ∈ Icc (-T) T, ∀ t ∈ Icc (-T) T,
      dist s t ≤ δ → dist (f s) (f t) ≤ d} =
      ⋂ s : ℝ, ⋂ (_ : s ∈ Icc (-T) T), ⋂ t : ℝ, ⋂ (_ : t ∈ Icc (-T) T),
        ⋂ (_ : dist s t ≤ δ), {f : C(ℝ, ℂ) | dist (f s) (f t) ≤ d} := by
    ext f
    simp only [mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_iInter fun t =>
    isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le ((continuous_eval_const s).dist (continuous_eval_const t)) continuous_const

/-- For a measurable random continuous path, the probability of violating a
fixed modulus bound on a compact time interval tends to zero as the time
increment shrinks. -/
theorem tendsto_measure_curve_modulus {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (η : Ω → C(ℝ, ℂ)) (hη : Measurable η)
    (T d : ℝ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => P {ω | ∃ s ∈ Icc (-T) T, ∃ t ∈ Icc (-T) T,
      dist s t ≤ 1 / ((n : ℝ) + 1) ∧ d < dist (η ω s) (η ω t)}) atTop (𝓝 0) := by
  let E : ℕ → Set Ω := fun n => {ω | ∃ s ∈ Icc (-T) T, ∃ t ∈ Icc (-T) T,
    dist s t ≤ 1 / ((n : ℝ) + 1) ∧ d < dist (η ω s) (η ω t)}
  apply tendsto_measure_zero_of_ae_eventually_not_mem P E
  · intro n
    have heq : E n = (η ⁻¹' {f : C(ℝ, ℂ) | ∀ s ∈ Icc (-T) T, ∀ t ∈ Icc (-T) T,
        dist s t ≤ 1 / ((n : ℝ) + 1) → dist (f s) (f t) ≤ d})ᶜ := by
      ext ω
      simp only [E, mem_ofPred_eq, mem_compl_iff, mem_preimage, not_forall, not_le, exists_prop]
    rw [heq]
    exact (((isClosed_curve_modulus T _ d).measurableSet.preimage hη).compl).nullMeasurableSet
  · apply Eventually.of_forall
    intro ω
    have hu : UniformContinuousOn (η ω) (Icc (-T) T) :=
      isCompact_Icc.uniformContinuousOn_of_continuous (η ω).continuous.continuousOn
    obtain ⟨δ, hδ, huδ⟩ := Metric.uniformContinuousOn_iff.mp hu d hd
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < δ :=
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)).eventually (Iio_mem_nhds hδ)
    filter_upwards [hsmall] with n hn
    rintro ⟨s, hs, t, ht, hst, hdist⟩
    exact (not_lt_of_ge (huδ s hs t ht (lt_of_le_of_lt hst hn)).le) hdist

/-- The compact-interval modulus bound applies to the curve of every valid
mating-of-trees environment. -/
theorem MatedCRTEnv.IsValid.tendsto_measure_curve_modulus {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (T d : ℝ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => S.P {ω | ∃ s ∈ Icc (-T) T, ∃ t ∈ Icc (-T) T,
      dist s t ≤ 1 / ((n : ℝ) + 1) ∧ d < dist (S.η ω s) (S.η ω t)}) atTop (𝓝 0) := by
  let _ : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, htie⟩ := hS.matingOfTrees
  have h := _root_.MatedCRT.tendsto_measure_curve_modulus S.P η' hC.measurable_curves.2.1 T d hd
  have heq (n : ℕ) : S.P {ω | ∃ s ∈ Icc (-T) T, ∃ t ∈ Icc (-T) T,
      dist s t ≤ 1 / ((n : ℝ) + 1) ∧ d < dist (S.η ω s) (S.η ω t)} =
      S.P {ω | ∃ s ∈ Icc (-T) T, ∃ t ∈ Icc (-T) T,
        dist s t ≤ 1 / ((n : ℝ) + 1) ∧ d < dist (η' ω s) (η' ω t)} := by
    apply measure_congr
    filter_upwards [htie] with ω hω
    simp only [hω.1]
  simpa only [← heq] using h

/-- A properness cutoff and a modulus of continuity give a uniform positive
lower bound on the area of balls centered in a bounded region. -/
theorem ball_mass_lower_of_curve_modulus {μ : Measure ℂ} {η : ℝ → ℂ}
    {ρ T δ d : ℝ} (hη : IsAreaParametrized μ η) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : 0 < d)
    (hescape : ∀ t : ℝ, T ≤ |t| → ρ + 1 ≤ ‖η t‖)
    (hmod : ∀ s ∈ Icc (-(T + 1)) (T + 1), ∀ t ∈ Icc (-(T + 1)) (T + 1),
      dist s t ≤ δ → dist (η s) (η t) ≤ d / 2)
    {z : ℂ} (hz : z ∈ ball 0 ρ) : ENNReal.ofReal δ ≤ μ (ball z d) := by
  obtain ⟨t, ht⟩ := hη.2.2.1 z
  have hzt : ‖η t‖ < ρ := by simpa [mem_ball, dist_zero_right, ht] using hz
  have htT : |t| < T := by
    by_contra h
    have := hescape t (le_of_not_gt h)
    linarith
  have htB : t ∈ Icc (-(T + 1)) (T + 1) := by
    have := abs_lt.1 htT
    constructor <;> linarith
  have hsub : η '' Icc t (t + δ) ⊆ ball z d := by
    rintro _ ⟨s, hs, rfl⟩
    have hsB : s ∈ Icc (-(T + 1)) (T + 1) := by
      obtain ⟨hsl, hsr⟩ := hs
      obtain ⟨htl, htr⟩ := htB
      have ht' := abs_lt.1 htT
      constructor <;> linarith
    have hdist : dist s t ≤ δ := by
      obtain ⟨hsl, hsr⟩ := hs
      rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ s - t)]
      linarith
    have h := hmod s hsB t htB hdist
    rw [mem_ball, ← ht]
    linarith
  have hmeasure := measure_mono (μ := μ) hsub
  rw [hη.2.2.2 t (t + δ) (by linarith)] at hmeasure
  simpa using hmeasure

end MatedCRT
