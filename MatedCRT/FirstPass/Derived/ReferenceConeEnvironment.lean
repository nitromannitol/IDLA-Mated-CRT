import MatedCRT.FirstPass.Derived.CouplingReferenceConeMatchingArea
import MatedCRT.FirstPass.Derived.ValidEnvironmentOfCoupling

/-! # Reference cone environments from a mating-of-trees coupling -/

noncomputable section

open MeasureTheory Set HarmonicBalls MarkovProcess LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace MatedCRT.Sec1

/-- The reference cone, its area measure and the coupled curve form an
    environment whose validity requires the SLE and all-start clock properties
    for that same environment. -/
theorem exists_reference_cone_environment_of_coupling
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (𝒮 : SpaceFillingSLEModel)
    (clock : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ) :
    ∃ S : MatedCRTEnv Ω,
      S.P = P ∧ S.bm = bm ∧ S.η = (fun ω => ⇑(η ω)) ∧ S.clock = clock ∧
      IsQuantumCone γ S.P S.hC S.hcirc ∧ IsLQGMeasure S.P γ S.hcirc S.μ ∧
      (∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω ∧ ∀ φ : TestC,
        S.hC ω ⇑φ = coneField (X ω)
          (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) ∧
      (𝒮.IsSLE S.P S.fieldSigma (16 / γ ^ 2) S.η →
        (∀ᵐ ω ∂S.P, ∀ z : ℂ,
          IsLQGClock planarBrownianMotion γ (S.hcirc ω) z (S.clock ω) ∧
          ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (S.clock ω b)) →
        S.IsValid 𝒮 γ) := by
  obtain ⟨R, W, F, hC, c, hRm, hR, hWm, hFm, hW, hF, hWB, hXW, hlaw,
    hG, hind, hpair, hhC, hc, hcont, hmeas, hcone, hobs, μ, hμmap, hμpull,
    hμcone, hmatching⟩ := exists_reference_cone_observables_with_matching_area D hγ.1 hγ.2
  let Y : Ω → DistC := MatedCRTHarmonic.GMCFacts.replField X
    (fun ω => MatedCRTHarmonic.GMCFacts.twoSided (W ω)
      ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩)
  let S : MatedCRTEnv Ω := {
    P := P
    hC := fun ω => MatedCRT.FirstPass.Derived.coneRefPairing γ (hC (Y ω)) (c (Y ω)) (F ω)
    hcirc := fun ω => MatedCRT.FirstPass.Derived.coneRefCircle γ (c (Y ω)) (F ω)
    μ := fun ω => MatedCRT.FirstPass.Derived.coneRefMeasure γ (c (Y ω)) (F ω) (μ (Y ω))
    η := fun ω => η ω
    clock := clock
    bm := bm }
  have hmatch : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω ∧ ∀ φ : TestC,
      S.hC ω ⇑φ = coneField (X ω)
        (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ := by
    filter_upwards [hmatching] with ω hω
    exact ⟨rfl, hω.1⟩
  refine ⟨S, rfl, rfl, rfl, rfl, hcone, hμcone, hmatch, ?_⟩
  intro hSLE hclock
  exact S.isValid_of_matching_coupling hγ D hcone hμcone hSLE hclock hmatch

end MatedCRT.Sec1
