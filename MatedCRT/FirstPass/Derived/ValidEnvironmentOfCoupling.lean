import MatedCRT.FirstPass.Derived.CouplingMatchingArea
import MatedCRT.Defs.Setting

/-! # Valid environments from a matching mating-of-trees coupling -/

set_option autoImplicit false

open MeasureTheory Set HarmonicBalls
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace MatedCRT

/-- A matching mating-of-trees coupling supplies the area parametrization of
an environment. The SLE predicate and the all-start clock are asserted for the
same environment and probability measure. -/
theorem MatedCRTEnv.isValid_of_matching_coupling
    {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {𝒮 : SpaceFillingSLEModel}
    (S : MatedCRTEnv Ω) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)}
    (D : IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ S.bm)
    (hcone : IsQuantumCone γ S.P S.hC S.hcirc)
    (hμ : IsLQGMeasure S.P γ S.hcirc S.μ)
    (hSLE : 𝒮.IsSLE S.P S.fieldSigma (16 / γ ^ 2) S.η)
    (hclock : ∀ᵐ ω ∂S.P, ∀ z : ℂ,
      IsLQGClock planarBrownianMotion γ (S.hcirc ω) z (S.clock ω) ∧
      ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (S.clock ω b))
    (hmatch : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω ∧ ∀ φ : LQGMetric.TestC,
      S.hC ω ⇑φ = coneField (X ω)
        (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) :
    S.IsValid 𝒮 γ := by
  have hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC,
      S.hC ω ⇑φ = coneField (X ω)
        (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ := by
    filter_upwards [hmatch] with ω hω
    exact hω.2
  have harea : ∀ᵐ ω ∂S.P, IsAreaParametrized (S.μ ω) (S.η ω) := by
    filter_upwards [ae_isAreaParametrized_of_coupling_matching_area D hγ hcone hμ hrep,
      hmatch] with ω hω hm
    rw [← hm.1]
    exact hω
  exact ⟨D.isProbabilityMeasure, hcone, hμ, hSLE, harea, hclock,
    ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η, η₀, D, hmatch⟩⟩

end MatedCRT
