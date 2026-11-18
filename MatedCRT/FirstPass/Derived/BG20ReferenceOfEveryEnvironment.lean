import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfBG20Reference
import MatedCRT.FirstPass.Derived.InterpolatedLawWiring
import MatedCRT.Proofs.Sec1.EnvironmentScaling.DistributionCode
import MatedCRT.Proofs.Sec6.IterativeBound.FieldSigma

/-!
# Berestycki–Gwynne Theorem 1.2 on one reference environment from its form in every environment

`randomWalkToLBMStmt_of_bg20` binds Berestycki–Gwynne (2020), Theorem 1.2, in every valid environment on `ℝ`
of the model `𝒮` (`hBG`); `randomWalkToLBMStmt_of_bg20_reference` binds it on one valid environment, on any
carrier, of any model with the same normalized space-filling SLE law `ν` (`hBGref`). Here `hBGref` is derived
from `hBG`, the normalized law `HasNormalizedSLELaw 𝒮 ν` and the reference environments
`HasReferenceEnvironments 𝒮`: take `𝒮₀ = 𝒮`, a valid environment `S₀` on `ℝ`, the measurable version of its
field (`exists_fieldMeasurable_coneDistribution`) and of its curve (`MatedCRTEnv.IsValid.exists_curveVersion`).
Both counted forms bind `h1` and `h10`, so `hBGref` is no stronger an input than `hBG`.

* `bg20Reference_of_bg20`: `hBGref` from `h1 h10 hBG`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal

namespace MatedCRT

/-- **Berestycki–Gwynne Theorem 1.2 on one reference environment, from its form in every valid environment.**
If the selected-cell walk laws converge to the Liouville Brownian law field, uniformly on compact sets in
probability, in every valid environment on `ℝ` of `𝒮` (the binder `hBG` of `randomWalkToLBMStmt_of_bg20`), and
`𝒮` has the normalized law `ν` and valid environments on `ℝ`, then the binder `hBGref` of
`randomWalkToLBMStmt_of_bg20_reference` holds: one valid environment of a model with law `ν`, with measurable
versions of its field and curve, along which the convergence holds. -/
theorem bg20Reference_of_bg20 {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h10 : HasReferenceEnvironments 𝒮)
    (hBG : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ S₀ : MatedCRTEnv ℝ, S₀.IsValid 𝒮 γ →
      ∀ H₀ : ℝ → LQGMetric.DistC, Measurable H₀ → (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) →
      ∀ η₀ : ℝ → C(ℝ, ℂ), Measurable η₀ → (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) →
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ H₀ : Ω₀ → LQGMetric.DistC, Measurable H₀ ∧ (∀ᵐ ω ∂S₀.P, ∀ φ : LQGMetric.TestC, S₀.hC ω φ = H₀ ω φ) ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ≥0∞, 0 < δ → Tendsto (fun ε => S₀.P {ω | ∃ z ∈ K,
        δ ≤ FirstPass.Derived.pathLevyProkhorovEDist (FirstPass.Derived.selCellLaw S₀ η₀ ε ω z)
          (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H₀ ω)) z)}) (𝓝[>] 0) (𝓝 0) := by
  intro γ hγ0 hγ2
  obtain ⟨S₀, hS₀⟩ := h10 γ hγ0 hγ2
  obtain ⟨H₀, hH₀m, hrep⟩ := MatedCRT.Sec1.exists_fieldMeasurable_coneDistribution hS₀
  have hH₀ : Measurable H₀ := hH₀m.mono (S₀.fieldSigma_le hS₀) le_rfl
  obtain ⟨η₀, hη₀m, hη₀⟩ := hS₀.exists_curveVersion
  exact ⟨𝒮, h1, ℝ, inferInstance, S₀, hS₀, H₀, hH₀, hrep, η₀, hη₀m, hη₀,
    hBG γ hγ0 hγ2 S₀ hS₀ H₀ hH₀ hrep η₀ hη₀m hη₀⟩

end MatedCRT
