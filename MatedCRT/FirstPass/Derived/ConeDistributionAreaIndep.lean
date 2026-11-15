import MatedCRT.FirstPass.Derived.ConeDistributionAreaCode
import MatedCRT.FirstPass.Derived.ConeCurveIndep

/-! # Independence of a cone distribution and its area measure -/

noncomputable section

open MeasureTheory ProbabilityTheory
open HarmonicBalls
open scoped NNReal

namespace MatedCRT

/-- The distribution and its LQG area are jointly independent of every random
variable independent of the distribution, when their pairings agree. -/
theorem indepFun_distribution_lqgMeasure_of_isQuantumCone
    {Ω : Type} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {S : MatedCRTEnv Ω} {γ : ℝ} {μ : Ω → Measure ℂ}
    {H : Ω → LQGMetric.DistC} {Y : Ω → E}
    (hcone : IsQuantumCone γ S.P S.hC S.hcirc)
    (hμ : IsLQGMeasure S.P γ S.hcirc μ)
    (hpair : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hind : IndepFun H Y S.P) :
    IndepFun (fun ω => (H ω, μ ω)) Y S.P := by
  obtain ⟨M, hM, hrec⟩ := exists_measurable_distribution_coneArea γ
  have hm : Measurable (fun h : LQGMetric.DistC => (h, M h)) :=
    measurable_id.prodMk hM
  refine (hind.comp hm measurable_id).congr ?_ (Filter.EventuallyEq.rfl)
  filter_upwards [hrec hcone hμ hpair] with ω hω
  exact Prod.ext rfl hω

/-- In a mating-of-trees coupling, a matching cone distribution and its LQG
area are independent of the space-filling curve. -/
theorem exists_coneField_area_indepFun_igCurve_of_coupling
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
    ∃ H : Ω → LQGMetric.DistC, Measurable H ∧
      (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) ∧
      IndepFun (fun ω => (H ω, μ ω)) ηL S.P := by
  obtain ⟨H, hHm, hind, hH⟩ :=
    FirstPass.Derived.exists_coneField_version_indepFun_igCurve h hγ hγ2
  have hpair : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ := by
    filter_upwards [hrep, hH] with ω h1 h2 φ
    rw [h1 φ, h2]
  exact ⟨H, hHm, hpair, indepFun_distribution_lqgMeasure_of_isQuantumCone hcone hμ hpair hind⟩

end MatedCRT
