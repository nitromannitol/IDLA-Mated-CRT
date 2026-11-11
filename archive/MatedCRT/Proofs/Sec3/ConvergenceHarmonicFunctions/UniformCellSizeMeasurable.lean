import MatedCRT.Steps.Sec3.UniformCellSize
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSCellSizeMeasurable

/-! # Uniform cell-size exponent and environment-measurable versions -/

namespace MatedCRT

open MeasureTheory Set Metric _root_.HarmonicBalls
open scoped ENNReal

/-- A representation-uniform cell-size exponent passes to the measurable
versions of the cell-size events. Agreement with the original event remains
almost everywhere, separately at each mesh. -/
theorem uniform_envSigma_cellSize_of_step (𝒮 : SpaceFillingSLEModel)
    (hcell : UniformCellSizeUpperStep 𝒮) {γ ρ a : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (ha : 0 < a) (ha' : a < 2 / (2 + γ) ^ 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (Ω : Type) [MeasurableSpace Ω]
      (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ A : ℝ → Set Ω, (∀ ε, MeasurableSet[S.envSigma] (A ε)) ∧
        (∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          S.P (A ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ κ)) ∧
        ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
          (ω ∈ A ε ↔ ∀ i : ℤ, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
            diam (cell ε (S.η ω) i) ≤ ε ^ a) := by
  obtain ⟨κ, hκ, hbound⟩ := hcell γ hγ hγ2 ρ hρ hρ1 a ha ha'
  refine ⟨κ, hκ, ?_⟩
  intro Ω _ S hS
  classical
  choose A hAm hAe using fun ε : ℝ =>
    hS.exists_envSigma_measurable_cellSize ε ρ (max 0 (ε ^ a)) (le_max_left _ _)
  have hmatch : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (ω ∈ A ε ↔ ∀ i : ℤ, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ ε ^ a) := by
    intro ε hε
    simpa only [max_eq_right (Real.rpow_nonneg hε.le _)] using hAe ε
  obtain ⟨C, ε₀, hC, hε₀, hprob⟩ := hbound Ω S hS
  refine ⟨A, hAm, ⟨C, ε₀, hC, hε₀, ?_⟩, hmatch⟩
  intro ε hε hsmall
  have heq : S.P (A ε)ᶜ = S.P {ω | ¬ ∀ i : ℤ,
      (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ ε ^ a} := by
    apply measure_congr
    filter_upwards [hmatch ε hε] with ω hω
    exact propext (not_congr hω)
  rw [heq]
  exact hprob ε hε hsmall

end MatedCRT

#print axioms MatedCRT.uniform_envSigma_cellSize_of_step
