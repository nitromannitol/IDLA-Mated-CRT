import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentMeasurability
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CellDomainMeasurable

/-! # Environment-measurable vertex sets -/

namespace MatedCRT

open Set MeasureTheory Topology

/-- The vertex set of cells meeting an open or closed set has a version
measurable with respect to the field and curve. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_cellVertices
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) :
    ∃ V : Ω → Set ℤ, Measurable[S.envSigma] V ∧
      ∀ᵐ ω ∂S.P, V ω = cellVertices ε (S.η ω) D := by
  obtain ⟨η, hηm, hη⟩ := hS.exists_envSigma_measurable_curve
  let V : Ω → Set ℤ := fun ω => cellVertices ε (η ω) D
  have hV : Measurable[S.envSigma] V := by
    let : MeasurableSpace Ω := S.envSigma
    apply measurable_set_iff.mpr
    intro k
    have hk : MeasurableSet {p : C(ℝ, ℂ) | k ∈ cellVertices ε p D} := by
      rcases hD with hD | hD
      · exact (isOpen_curve_cell_meets ε k D hD).measurableSet
      · exact (isClosed_curve_cell_meets ε k D hD).measurableSet
    exact measurableSet_setOfPred.mp (hk.preimage hηm)
  refine ⟨V, hV, ?_⟩
  filter_upwards [hη] with ω hω
  simp [V, hω]

/-- The interior vertex set has an environment-measurable version. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_interiorCellVertices
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) :
    ∃ V : Ω → Set ℤ, Measurable[S.envSigma] V ∧
      ∀ᵐ ω ∂S.P, V ω = interiorCellVertices ε (S.η ω) D := by
  obtain ⟨V, hV, hVa⟩ := hS.exists_envSigma_measurable_cellVertices ε D hD
  obtain ⟨W, hW, hWa⟩ := hS.exists_envSigma_measurable_cellVertices ε (frontier D)
    (Or.inr isClosed_frontier)
  have hdiff : Measurable[S.envSigma] (fun ω => V ω \ W ω) := by
    let : MeasurableSpace Ω := S.envSigma
    apply measurable_set_iff.mpr
    intro k
    exact ((measurable_set_mem k).comp hV).and (((measurable_set_mem k).comp hW).not)
  refine ⟨fun ω => V ω \ W ω, hdiff, ?_⟩
  filter_upwards [hVa, hWa] with ω hv hw
  simp only [interiorCellVertices, hv, hw]

end MatedCRT
