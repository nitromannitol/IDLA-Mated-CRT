import MatedCRT.FirstPass.Derived.ReferenceConeEnvironment
import MatedCRT.FirstPass.Derived.ConeFieldSigmaCurveIndep

/-! # Reference cone environment and Lebesgue curve independence -/

noncomputable section

open MeasureTheory ProbabilityTheory Set HarmonicBalls MarkovProcess LQGMetric
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace MatedCRT.Sec1

/-- The reference cone environment from the coupling has a field sigma algebra
independent of the coupling's Lebesgue-parametrized curve. -/
theorem exists_reference_cone_environment_indep_of_coupling
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
      Indep S.fieldSigma (MeasurableSpace.comap ηL inferInstance) S.P ∧
      (𝒮.IsSLE S.P S.fieldSigma (16 / γ ^ 2) S.η →
        (∀ᵐ ω ∂S.P, ∀ z : ℂ,
          IsLQGClock planarBrownianMotion γ (S.hcirc ω) z (S.clock ω) ∧
          ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (S.clock ω b)) →
        S.IsValid 𝒮 γ) := by
  obtain ⟨S, hP, hbm, hη, hclock, hcone, hμ, hmatch, hvalid⟩ :=
    exists_reference_cone_environment_of_coupling D hγ 𝒮 clock
  have hD : IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm := by
    rw [hP]
    exact D
  have hrep : ∀ᵐ ω ∂S.P, ∀ φ : TestC, S.hC ω ⇑φ =
      coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ := by
    filter_upwards [hmatch] with ω hω
    exact hω.2
  exact ⟨S, hP, hbm, hη, hclock, hcone, hμ, hmatch,
    indep_fieldSigma_igCurve_of_coupling hγ.1 hγ.2 hD hrep, hvalid⟩

end MatedCRT.Sec1
