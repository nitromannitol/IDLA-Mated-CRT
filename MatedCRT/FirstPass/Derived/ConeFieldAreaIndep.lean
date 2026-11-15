import MatedCRT.FirstPass.Derived.ConeDistributionAreaIndep

/-! # Independence of the concrete cone field and its area -/

noncomputable section

open MeasureTheory ProbabilityTheory
open HarmonicBalls
open scoped NNReal

namespace MatedCRT

/-- In a mating-of-trees coupling, the concrete cone field and a matching LQG
area are jointly independent of the Lebesgue-parametrized curve. -/
theorem indepFun_coneField_lqgMeasure_igCurve_of_coupling
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {μ : Ω → Measure ℂ}
    (hcone : IsQuantumCone γ S.P S.hC S.hcirc)
    (hμ : IsLQGMeasure S.P γ S.hcirc μ)
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)}
    {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ =
      MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) :
    IndepFun (fun ω => (MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)), μ ω)) ηL S.P := by
  obtain ⟨H, _, hind, hH⟩ :=
    FirstPass.Derived.exists_coneField_version_indepFun_igCurve h hγ hγ2
  have hHeq : H =ᵐ[S.P] (fun ω => MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) := by
    filter_upwards [hH] with ω hω
    exact hω.symm
  have hfield : IndepFun (fun ω => MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) ηL S.P :=
    hind.congr hHeq (Filter.EventuallyEq.rfl)
  exact indepFun_distribution_lqgMeasure_of_isQuantumCone hcone hμ hrep hfield

end MatedCRT
