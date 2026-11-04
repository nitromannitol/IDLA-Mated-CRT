import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentGreen
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RescaleMeasurable

/-! Environment-measurable normalized exit times. -/

namespace MatedCRT

open Set MeasureTheory Topology

/-- The normalized exit time has an environment-measurable version,
simultaneously for all starting vertices. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_normExitTime
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) :
    ∃ u : Ω → ℤ → ℝ, (∀ a, Measurable[S.envSigma] fun ω => u ω a) ∧
      ∀ᵐ ω ∂S.P, ∀ a, u ω a = normExitTime (S.mult ε ω)
        (interiorCellVertices ε (S.η ω) D) a := by
  classical
  obtain ⟨B, hBm, hB⟩ := hS.exists_envSigma_measurable_bm
  obtain ⟨V, hVm, hV⟩ := hS.exists_envSigma_measurable_interiorCellVertices ε D hD
  let M : Ω → ℤ → ℤ → ℕ := fun ω j k =>
    bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k
  have hMm : ∀ j k, Measurable[S.envSigma] fun ω => M ω j k :=
    fun j k => (measurable_bmEdgeCount_path ε j k).comp hBm
  let u : Ω → ℤ → ℝ := fun ω a => normExitTime (M ω) (V ω) a
  have hum : ∀ a, Measurable[S.envSigma] fun ω => u ω a := by
    let : MeasurableSpace Ω := S.envSigma
    intro a
    have heq : (fun ω => u ω a) = fun ω => ∑' b : ℤ,
        if b ∈ V ω then greenKernel (M ω) (V ω) a b else 0 := by
      funext ω
      simp only [u, normExitTime, tsum_subtype]
      rfl
    rw [heq]
    apply Measurable.tsum
    intro b
    exact Measurable.ite (measurableSet_setOfPred.mpr ((measurable_set_mem b).comp hVm))
      (GreenEnvironment.measurable_greenKernel M hMm V hVm a b) measurable_const
  refine ⟨u, hum, ?_⟩
  filter_upwards [hB, hV] with ω hb hv a
  have hM : M ω = S.mult ε ω := by
    funext j k
    simp only [M, MatedCRTEnv.mult, hb]
  simp only [u, hM, hv]

/-- Exit times along environment-measurable selections from a countable
family of meshes have simultaneous environment-measurable versions. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_selected_normExitTime
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℕ → ℝ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D)
    (I : Ω → ℕ → ℕ) (hI : ∀ n, Measurable[S.envSigma] fun ω => I ω n) :
    ∃ u : Ω → ℕ → ℤ → ℝ,
      (∀ n a, Measurable[S.envSigma] fun ω => u ω n a) ∧
      ∀ᵐ ω ∂S.P, ∀ n a, u ω n a = normExitTime (S.mult (ε (I ω n)) ω)
        (interiorCellVertices (ε (I ω n)) (S.η ω) D) a := by
  classical
  choose u hum hue using fun j => hS.exists_envSigma_measurable_normExitTime (ε j) D hD
  refine ⟨fun ω n a => u (I ω n) ω a, ?_, ?_⟩
  · let : MeasurableSpace Ω := S.envSigma
    intro n a
    exact measurable_countable_evaluation (fun ω => I ω n) (hI n)
      (fun j ω => u j ω a) (fun j => hum j a)
  · filter_upwards [ae_all_iff.mpr hue] with ω hω
    intro n a
    exact hω (I ω n) a

end MatedCRT
