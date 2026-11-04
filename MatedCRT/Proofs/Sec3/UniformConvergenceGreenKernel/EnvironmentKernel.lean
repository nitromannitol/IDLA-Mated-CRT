import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentGreen
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentVertex

/-! # Environment-measurable Green kernels with a spatial pole -/

namespace MatedCRT

open Set MeasureTheory Topology

/-- The Green kernel with pole at the cell containing a fixed point has an
 environment-measurable version, simultaneously at all vertices. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_greenKernel_vertexOf
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) (y : ℂ) :
    ∃ g : Ω → ℤ → ℝ, (∀ b, Measurable[S.envSigma] fun ω => g ω b) ∧
      ∀ᵐ ω ∂S.P, ∀ b, g ω b = greenKernel (S.mult ε ω)
        (interiorCellVertices ε (S.η ω) D) (vertexOf ε (S.η ω) y) b := by
  obtain ⟨a, ha, hae⟩ := hS.exists_envSigma_measurable_vertexOf hε y
  obtain ⟨g, hg, hge⟩ := hS.exists_envSigma_measurable_greenKernel ε D hD a ha
  refine ⟨g, hg, ?_⟩
  filter_upwards [hae, hge] with ω hω hgω b
  rw [hgω b, hω]

end MatedCRT
