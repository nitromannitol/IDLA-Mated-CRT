import MatedCRT.Steps.Sec4.ConvergenceDivisible
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ConvergenceEventMeasurable

/-! # Reduction of the convergence-event measurability step -/

namespace MatedCRT

open MeasureTheory HarmonicBalls

/-- Pointwise measurability of the continuum obstacle solution and the
adjacent-cells property imply the convergence-event measurability step. -/
theorem convergenceDivisibleEventMeasurable_of_pointwise
    (𝒮 : SpaceFillingSLEModel) (hcell : AdjacentCellsMeetAeStep 𝒮)
    (hpoint : ∀ (γ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ (r t : ℝ), 0 < r → 0 < t → ∀ z : ℂ,
        AEMeasurable (fun ω => leastSupersolution (S.μ ω) r 0 t z) S.P) :
    ConvergenceDivisibleEventMeasurableStep 𝒮 := by
  intro γ hγ hγ' ρ hρ _ Ω _ S hS Λ hΛ t δ ε ht _ hε
  have hlf : ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite := by
    filter_upwards [ae_locallyFinite_mult_of_adjacentCells hS hγ hγ' hcell] with ω hω
    exact hω ε hε
  apply hS.nullMeasurableSet_convergenceError_of_pointwise hγ hγ' hρ ht hε Λ hΛ hlf
  · intro q hq n z
    exact hpoint γ hγ hγ' Ω S hS ((n : ℝ) + 1) q (by positivity) hq z
  · exact hpoint γ hγ hγ' Ω S hS ρ t hρ ht

end MatedCRT
