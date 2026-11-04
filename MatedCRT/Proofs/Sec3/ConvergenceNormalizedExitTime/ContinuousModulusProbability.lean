import MatedCRT.Proofs.Sec5.LLowerBound.ModulusProb

/-! Modulus of continuity for a random continuous function on a compact set. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- A prescribed modulus bound is closed in the compact-open topology. -/
theorem isClosed_continuousMap_modulus {α : Type*} [PseudoMetricSpace α]
    (δ t : ℝ) : IsClosed {f : C(α, ℝ) | ∀ x y, dist x y ≤ δ → dist (f x) (f y) ≤ t} := by
  have heq : {f : C(α, ℝ) | ∀ x y, dist x y ≤ δ → dist (f x) (f y) ≤ t} =
      ⋂ x : α, ⋂ y : α, ⋂ (_ : dist x y ≤ δ), {f : C(α, ℝ) | dist (f x) (f y) ≤ t} := by
    ext f
    simp only [mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
    isClosed_le ((continuous_eval_const x).dist (continuous_eval_const y)) continuous_const

/-- The modulus of a measurable random continuous function on a compact
metric space is small with probability tending to one. -/
theorem tendsto_measure_continuousMap_modulus
    {Ω α : Type*} [MeasurableSpace Ω] [PseudoMetricSpace α] [CompactSpace α]
    (P : Measure Ω) [IsFiniteMeasure P] (U : Ω → C(α, ℝ)) (hU : Measurable U)
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => P {ω | ∃ x y : α,
      dist x y ≤ 1 / ((n : ℝ) + 1) ∧ t < dist (U ω x) (U ω y)}) atTop (𝓝 0) := by
  let E : ℕ → Set Ω := fun n => {ω | ∃ x y : α,
    dist x y ≤ 1 / ((n : ℝ) + 1) ∧ t < dist (U ω x) (U ω y)}
  apply tendsto_measure_zero_of_ae_eventually_not_mem P E
  · intro n
    have heq : E n = (U ⁻¹' {f : C(α, ℝ) | ∀ x y,
        dist x y ≤ 1 / ((n : ℝ) + 1) → dist (f x) (f y) ≤ t})ᶜ := by
      ext ω
      simp only [E, mem_ofPred_eq, mem_compl_iff, mem_preimage, not_forall, not_le, exists_prop]
    rw [heq]
    exact (((isClosed_continuousMap_modulus _ t).measurableSet.preimage hU).compl).nullMeasurableSet
  · apply Eventually.of_forall
    intro ω
    have hu : UniformContinuous (U ω) := CompactSpace.uniformContinuous_of_continuous (U ω).continuous
    obtain ⟨δ, hδ, huδ⟩ := Metric.uniformContinuous_iff.mp hu t ht
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < δ :=
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)).eventually (Iio_mem_nhds hδ)
    filter_upwards [hsmall] with n hn
    rintro ⟨x, y, hxy, hdist⟩
    exact (not_lt_of_ge (huδ (lt_of_le_of_lt hxy hn)).le) hdist

end MatedCRT
