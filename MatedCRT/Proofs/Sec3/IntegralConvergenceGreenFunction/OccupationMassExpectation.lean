import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WholePlaneClockExpectation
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationEnergyIsometry

/-! # Expected mass of the regularized path occupation chaos -/

namespace MatedCRT

open MeasureTheory Set HarmonicBalls MarkovProcess
open scoped NNReal ENNReal

/-- Restricting the occupation measure to a measurable set carrying the path
does not change its total mass. -/
theorem pathOccupationMeasure_comap_real_univ
    {E : Type*} [MeasurableSpace E] {D : Set E} (hD : MeasurableSet D)
    {b : ℝ → E} (hb : Measurable b) (T : ℝ≥0)
    (hsupp : pathOccupationMeasure b T Dᶜ = 0) :
    ((pathOccupationMeasure b T).comap (Subtype.val : D → E)).real univ = T := by
  change (((pathOccupationMeasure b T).comap (Subtype.val : D → E)) univ).toReal = T
  rw [(MeasurableEmbedding.subtype_coe hD).comap_apply, image_univ, Subtype.range_coe,
    measure_of_measure_compl_eq_zero hsupp, pathOccupationMeasure_univ hb]
  simp

/-- Before leaving a region whose averaging circles lie in the unit disk,
the expected total mass of the circle-average clock chaos equals elapsed
Brownian time. -/
theorem IsWholePlaneGFF.occupation_clockDensity_expectation
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {D : Set ℂ} (hD : MeasurableSet D)
    (r : ℝ) (hr : 0 < r) (hinside : ∀ z ∈ D, ‖z‖ + r ≤ 1)
    (b : ContinuousPath ℂ) (T : ℝ≥0)
    (hT : (T : ℝ≥0∞) ≤ b.exitTime D) (γ : ℝ) :
    let σ := (pathOccupationMeasure (fun t => b t.toNNReal) T).comap
      (Subtype.val : D → ℂ)
    let ν : Ω → Measure D := fun ω => σ.withDensity (fun z => ENNReal.ofReal
      (r ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω r z)))
    Integrable (fun ω => (ν ω).real univ) P ∧
      (∫ ω, (ν ω).real univ ∂P) = T := by
  dsimp only
  have hsupp := continuousPath_occupation_compl_eq_zero_before_exit b D hD T (by
    simpa using hT)
  have hm := MatedCRT.IsWholePlaneGFF.clockDensity_integral_real_apply h r hr hinside
    ((pathOccupationMeasure (fun t => b t.toNNReal) T).comap
      (Subtype.val : D → ℂ)) γ univ MeasurableSet.univ
  refine ⟨hm.1, hm.2.trans ?_⟩
  exact pathOccupationMeasure_comap_real_univ hD (by fun_prop) T hsupp

end MatedCRT

