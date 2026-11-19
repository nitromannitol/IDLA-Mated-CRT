import MatedCRT.FirstPass.Derived.ConeDistributionAreaIndep
import MatedCRT.FirstPass.SLERef.Reference

/-! # Measurable versions of the quantum cone field of a valid environment

The pairings `ω ↦ S.hC ω` of the quantum cone field of an environment are not assumed measurable as a map into
the space of distributions. For a valid environment the mating-of-trees coupling (`MatedCRTEnv.IsValid.matingOfTrees`)
represents them almost surely by the cone field of a whole-plane GFF and a pair of Brownian motions, whose
distribution-valued version is measurable (`exists_coneField_area_indepFun_igCurve_of_coupling`). This gives a
measurable version `H` with `S.hC ω φ = H ω φ` for every test function `φ`, almost surely.

Applied to the reference environments of `HasReferenceEnvironments`, it yields, for every `γ ∈ (0, 2)`, a valid
environment on the standard Borel space `ℝ` together with a measurable version of its field.
-/

noncomputable section

open MeasureTheory

namespace MatedCRT

/-- **Measurable version of the field.** A valid environment has a measurable distribution-valued version `H` of
the pairings of its quantum cone field: almost surely, `S.hC ω φ = H ω φ` for every test function `φ`. -/
theorem MatedCRTEnv.IsValid.exists_measurable_fieldVersion {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ H : Ω → LQGMetric.DistC, Measurable H ∧
      ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hcoup, hae⟩ := hS.matingOfTrees
  obtain ⟨H, hHm, hpair, -⟩ :=
    exists_coneField_area_indepFun_igCurve_of_coupling hγ hγ2 hS.isQuantumCone hS.isLQGMeasure hcoup
      (hae.mono fun _ h => h.2)
  exact ⟨H, hHm, hpair⟩

/-- **Reference environment with a measurable field version.** If the model `𝒮` has valid reference environments,
then for every `γ ∈ (0, 2)` there are a valid environment `S₀` on `ℝ` and a measurable version `H₀` of the pairings
of its quantum cone field. -/
theorem exists_referenceEnv_measurable_fieldVersion {𝒮 : SpaceFillingSLEModel}
    (h10 : HasReferenceEnvironments 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ S₀ : MatedCRTEnv ℝ, S₀.IsValid 𝒮 γ ∧
      ∃ H₀ : ℝ → LQGMetric.DistC, Measurable H₀ ∧
        ∀ᵐ r ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC r φ = H₀ r φ := by
  obtain ⟨S₀, hS₀⟩ := h10 γ hγ hγ2
  exact ⟨S₀, hS₀, hS₀.exists_measurable_fieldVersion hγ hγ2⟩

end MatedCRT
