import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CellMeasurable

/-! # Joint measurability of rescaled vertex functions -/

namespace MatedCRT

open Set MeasureTheory

/-- Evaluating a countable family of measurable functions at a measurable
index produces a measurable function. -/
theorem measurable_countable_evaluation {α β ι : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (V : α → ι) (hV : Measurable V) (u : ι → α → β)
    (hu : ∀ i, Measurable (u i)) : Measurable (fun x => u (V x) x) := by
  intro A hA
  have heq : (fun x => u (V x) x) ⁻¹' A =
      ⋃ i, (V ⁻¹' {i}) ∩ (u i ⁻¹' A) := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    constructor
    · intro hx
      exact ⟨V x, rfl, hx⟩
    · rintro ⟨i, hi, hx⟩
      simpa [hi] using hx
  rw [heq]
  exact MeasurableSet.iUnion fun i => (hV (measurableSet_singleton i)).inter (hu i hA)

/-- Rescaling measurable vertex functions along the space-filling curve
admits a jointly measurable version, simultaneously for all spatial points. -/
theorem MatedCRTEnv.IsValid.exists_measurable_rescale
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) (m : ℝ) (u : Ω → ℤ → ℝ)
    (hu : ∀ k, Measurable fun ω => u ω k) :
    ∃ f : Ω × ℂ → ℝ, Measurable f ∧
      ∀ᵐ ω ∂S.P, ∀ x, f (ω, x) = rescale m ε (S.η ω) (u ω) x := by
  obtain ⟨V, hV, hVe⟩ := hS.exists_measurable_vertexOf hε
  refine ⟨fun p => m⁻¹ * u p.1 (V p), ?_, ?_⟩
  · exact measurable_const.mul (measurable_countable_evaluation V hV
      (fun k p => u p.1 k) (fun k => (hu k).comp measurable_fst))
  · filter_upwards [hVe] with ω hω
    intro x
    simp only [rescale, hω x]

end MatedCRT
