import MatedCRT.FirstPass.Derived.ReferenceConeEnvironmentIndep
import MatedCRT.FirstPass.Derived.CanonicalSLECoupling

/-! # Canonical reference cone environment -/

noncomputable section

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace MatedCRT.Sec1

/-- A matching coupling whose Lebesgue curve has the specified code law
provides a reference cone environment for the canonical SLE model, with
validity conditional on the common-event all-start clock property. -/
theorem exists_canonical_reference_cone_environment_of_coupling
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {ν : ℝ → Measure SLEPathCode}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hlaw : P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (clock : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ) :
    ∃ S : MatedCRTEnv Ω,
      S.P = P ∧ S.bm = bm ∧ S.η = (fun ω => ⇑(η ω)) ∧ S.clock = clock ∧
      IsQuantumCone γ S.P S.hC S.hcirc ∧ IsLQGMeasure S.P γ S.hcirc S.μ ∧
      (∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω ∧ ∀ φ : TestC,
        S.hC ω ⇑φ = coneField (X ω)
          (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) ∧
      Indep S.fieldSigma (MeasurableSpace.comap ηL inferInstance) S.P ∧
      (ProbeMi.canonicalSLEModel ν).IsSLE S.P S.fieldSigma (16 / γ ^ 2) S.η ∧
      ((∀ᵐ ω ∂S.P, ∀ z : ℂ,
          IsLQGClock planarBrownianMotion γ (S.hcirc ω) z (S.clock ω) ∧
          ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (S.clock ω b)) →
        S.IsValid (ProbeMi.canonicalSLEModel ν) γ) := by
  obtain ⟨S, hP, hbm, hη, hclock, hcone, hμ, hmatch, hind, hvalid⟩ :=
    exists_reference_cone_environment_indep_of_coupling D hγ
      (ProbeMi.canonicalSLEModel ν) clock
  have hD : IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm := by
    rw [hP]
    exact D
  have hηae : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω := by
    filter_upwards [hmatch] with ω hω
    exact hω.1
  have hrep : ∀ᵐ ω ∂S.P, ∀ φ : TestC, S.hC ω ⇑φ =
      coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ := by
    filter_upwards [hmatch] with ω hω
    exact hω.2
  have hlaw' : S.P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2) := by
    rw [hP]
    exact hlaw
  have hSLE := MatedCRT.FirstPass.Derived.canonicalSLEModel_isSLE_of_coupling
    hγ.1 hγ.2 hD hcone hηae hrep hlaw'
  exact ⟨S, hP, hbm, hη, hclock, hcone, hμ, hmatch, hind, hSLE, hvalid hSLE⟩

end MatedCRT.Sec1
