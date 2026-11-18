import MatedCRT.FirstPass.Derived.UniformStartGoodFinExit
import LatticeProb.MeasureTheory.AeEventuallyMeasureBound

/-!
# Uniform-start bound without the reverse Fatou hypothesis

`exists_eps_uniformStart_bound_of_gamma` takes the reverse Fatou statement for the probability measure `S.P` as a
hypothesis.  This file supplies it from the general statement
`LatticeProb.exists_eps_measure_compl_le_of_ae_eventually` of the probability library, so the only hypothesis left is the
almost-sure eventual uniform-start statement `hpkg` at tolerance `κ / 2` along every positive sequence tending to `0`.
-/

open MeasureTheory Filter Topology

namespace MatedCRT

namespace UniformStartGood

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Uniform-start bound from the covering statement alone.** For `0 < γ < 2` and a valid environment, if almost
surely the uniform-start event at tolerance `κ / 2` holds eventually along every positive sequence tending to `0`,
then for every `θ > 0` the uniform-start event at tolerance `κ` has complement of probability at most `θ` for all
small `ε`. -/
theorem exists_eps_uniformStart_bound_derived {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {R ρ : ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hpkg : ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
      ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ω ∈ goodG S (e n) R ρ (κ / 2))
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → S.P (goodG S ε R ρ κ)ᶜ ≤ ENNReal.ofReal θ := by
  have hP : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  refine exists_eps_uniformStart_bound_of_gamma hγ hγ2 hS ?_ hκ hpkg hθ
  intro M hM h θ' hθ'
  obtain ⟨ε₀, h0, hε⟩ := LatticeProb.exists_eps_measure_compl_le_of_ae_eventually S.P M hM h hθ'
  exact ⟨ε₀, h0, hε⟩

end UniformStartGood

end MatedCRT
