import MatedCRT.Defs.Setting

/-! # Null measurability of the environment sigma algebra -/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

/-- For a valid environment, the environment sigma algebra is contained in the completed ambient sigma algebra. -/
theorem MatedCRTEnv.IsValid.envSigma_le_nullMeasurableSpace {Ω : Type} [mΩ : MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    S.envSigma ≤ (NullMeasurableSpace.instMeasurableSpace : MeasurableSpace (NullMeasurableSpace Ω S.P)) := by
  have hnull : mΩ ≤ (NullMeasurableSpace.instMeasurableSpace : MeasurableSpace (NullMeasurableSpace Ω S.P)) :=
    fun A hA => MeasurableSet.nullMeasurableSet (μ := S.P) hA
  refine sup_le ?_ (iSup_le fun t => ?_)
  · simp only [MatedCRTEnv.fieldSigma, fieldSigmaAlgebra]
    refine iSup₂_le fun φ hφ => ?_
    have hm : Measurable fun ω => fieldPairing 0 (S.hC ω) φ := by
      simpa [fieldPairing] using hS.isQuantumCone.measurable_pairing φ hφ
    exact hm.comap_le.trans hnull
  · obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, hae⟩ := hS.matingOfTrees
    have hη' : Measurable fun ω => η' ω t :=
      (continuous_eval_const t).measurable.comp hC.measurable_curves.2.1
    have hae' : (fun ω => η' ω t) =ᵐ[S.P] fun ω => S.η ω t :=
      hae.mono fun ω h => congrFun h.1 t
    have hnm : NullMeasurable (fun ω => S.η ω t) S.P := (hη'.aemeasurable.congr hae').nullMeasurable
    exact Measurable.comap_le hnm

/-- Environment-measurable events are null measurable. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_of_envSigma {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) {A : Set Ω}
    (hA : MeasurableSet[S.envSigma] A) : NullMeasurableSet A S.P :=
  hS.envSigma_le_nullMeasurableSpace A hA

/-- Environment-measurable real functions are almost everywhere measurable. -/
theorem MatedCRTEnv.IsValid.aemeasurable_of_envSigma {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) {s : Ω → ℝ}
    (hs : Measurable[S.envSigma] s) : AEMeasurable s S.P := by
  have hnm : NullMeasurable s S.P := hs.mono hS.envSigma_le_nullMeasurableSpace le_rfl
  exact hnm.aemeasurable

end MatedCRT
