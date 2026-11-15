import MatedCRT.FirstPass.Derived.ConeSelectedArea
import MatedCRT.FirstPass.Derived.ConeCurveIndep
import MatedCRT.FirstPass.Derived.CouplingAreaParametrization

/-! # Matching the area of a mating-of-trees cell model -/

noncomputable section

open MeasureTheory Set
open HarmonicBalls
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

namespace MatedCRT

/-- A coupling cell model has the same area as a matching cone LQG measure. -/
theorem ae_cellModel_area_eq_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hcone : IsQuantumCone γ P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    (hrep : ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC, hC ω φ =
      coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) :
    ∀ᵐ ω ∂P, (cellModelOfCoupling D hγ).area ω = μ ω := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨H, hHm, _, hH⟩ :=
    FirstPass.Derived.exists_coneField_version_indepFun_igCurve D hγ.1 hγ.2
  have hmatch : ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC, hC ω φ = H ω φ := by
    filter_upwards [hrep, hH] with ω hr hv φ
    rw [hr φ, hv]
  filter_upwards [ae_cone_selectedArea_eq (P := P) hcone hμ hHm hmatch, hH] with ω ha hv
  change CellScaling.lqgArea γ (coneField (X ω)
    (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) = μ ω
  rw [hv]
  exact ha

/-- The matching LQG area parametrizes the coupling's curve. -/
theorem ae_isAreaParametrized_of_coupling_matching_area
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hcone : IsQuantumCone γ P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    (hrep : ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC, hC ω φ =
      coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ) :
    ∀ᵐ ω ∂P, IsAreaParametrized (μ ω) (η ω) := by
  filter_upwards [ae_cellModel_area_eq_of_coupling D hγ hcone hμ hrep,
    ae_isAreaParametrized_of_coupling D hγ] with ω heq hp
  change IsAreaParametrized ((cellModelOfCoupling D hγ).area ω) (η ω) at hp
  rwa [heq] at hp

end MatedCRT
