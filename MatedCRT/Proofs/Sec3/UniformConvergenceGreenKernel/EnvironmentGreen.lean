import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentCells
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.RandomGraphMeasurable

/-! # Environment-measurable Green kernels -/

namespace MatedCRT

open Set MeasureTheory Topology

/-- The multiplicity of each edge is a measurable function of the
boundary-length path. -/
theorem measurable_bmEdgeCount_path (ε : ℝ) (j k : ℤ) :
    Measurable (fun p : C(ℝ, ℝ × ℝ) =>
      bmEdgeCount ε (fun t => (p t).1) (fun t => (p t).2) j k) := by
  classical
  have hL : MeasurableSet {p : C(ℝ, ℝ × ℝ) |
      bmAdjacent ε (fun t => (p t).1) (min j k) (max j k)} :=
    (isClosed_bmAdjacent ε (min j k) (max j k) Prod.fst continuous_fst).measurableSet
  have hR : MeasurableSet {p : C(ℝ, ℝ × ℝ) |
      bmAdjacent ε (fun t => (p t).2) (min j k) (max j k)} :=
    (isClosed_bmAdjacent ε (min j k) (max j k) Prod.snd continuous_snd).measurableSet
  unfold bmEdgeCount
  by_cases hjk : j = k
  · simp [hjk]
  · simp only [hjk, ↓reduceIte]
    apply Measurable.ite (hL.union hR)
    · by_cases hdist : 1 < max j k - min j k
      · simp only [hdist, true_and]
        exact Measurable.ite (hL.inter hR) measurable_const measurable_const
      · simp [hdist]
    · exact measurable_const

/-- Given an environment-measurable starting vertex, the Green kernel has
an environment-measurable version, simultaneously at all target vertices. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_greenKernel
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D)
    (A : Ω → ℤ) (hA : Measurable[S.envSigma] A) :
    ∃ g : Ω → ℤ → ℝ, (∀ b, Measurable[S.envSigma] fun ω => g ω b) ∧
      ∀ᵐ ω ∂S.P, ∀ b, g ω b = greenKernel (S.mult ε ω)
        (interiorCellVertices ε (S.η ω) D) (A ω) b := by
  obtain ⟨B, hBm, hB⟩ := hS.exists_envSigma_measurable_bm
  obtain ⟨V, hVm, hV⟩ := hS.exists_envSigma_measurable_interiorCellVertices ε D hD
  let M : Ω → ℤ → ℤ → ℕ := fun ω j k =>
    bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k
  have hMm : ∀ j k, Measurable[S.envSigma] fun ω => M ω j k :=
    fun j k => (measurable_bmEdgeCount_path ε j k).comp hBm
  let g : Ω → ℤ → ℝ := fun ω b => greenKernel (M ω) (V ω) (A ω) b
  have hgm : ∀ b, Measurable[S.envSigma] fun ω => g ω b := by
    let : MeasurableSpace Ω := S.envSigma
    intro b
    exact measurable_countable_evaluation A hA
      (fun a ω => greenKernel (M ω) (V ω) a b)
      (fun a => GreenEnvironment.measurable_greenKernel M hMm V hVm a b)
  refine ⟨g, hgm, ?_⟩
  filter_upwards [hB, hV] with ω hb hv b
  have hM : M ω = S.mult ε ω := by
    funext j k
    simp only [M, MatedCRTEnv.mult, hb]
  simp only [g, hM, hv]

end MatedCRT
