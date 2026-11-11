import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WholePlaneClockExpectation
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationEnergyIsometry
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.L1Expectation

/-! # Expected mass of the regularized path occupation chaos -/

namespace MatedCRT

open MeasureTheory Set HarmonicBalls MarkovProcess Filter Topology
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

/-- Any integrable L¹ limit of the regularized occupation masses has mean
equal to the elapsed path time. The path is fixed, so this is the conditional
expectation needed before integrating over Brownian paths. -/
theorem IsWholePlaneGFF.occupation_mass_limit_expectation
    {Ω : Type} {ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {D : Set ℂ} (hD : MeasurableSet D)
    (l : Filter ι) [NeBot l] (r : ι → ℝ)
    (hr : ∀ᶠ i in l, 0 < r i ∧ ∀ z ∈ D, ‖z‖ + r i ≤ 1)
    (b : ContinuousPath ℂ) (T : ℝ≥0) (hT : (T : ℝ≥0∞) ≤ b.exitTime D)
    (γ : ℝ) (Y : Ω → ℝ) (hY : Integrable Y P)
    (hconv : Tendsto (fun i => ∫ ω, |(((pathOccupationMeasure
      (fun t => b t.toNNReal) T).comap (Subtype.val : D → ℂ)).withDensity
      (fun z => ENNReal.ofReal (r i ^ (γ ^ 2 / 2) *
        Real.exp (γ * hcirc ω (r i) z)))).real univ - Y ω| ∂P) l (𝓝 0)) :
    (∫ ω, Y ω ∂P) = T := by
  apply integral_eq_of_L1_limit P l _ Y T hY
  · filter_upwards [hr] with i hi
    exact (IsWholePlaneGFF.occupation_clockDensity_expectation h hD (r i) hi.1 hi.2 b T hT γ).1
  · filter_upwards [hr] with i hi
    exact (IsWholePlaneGFF.occupation_clockDensity_expectation h hD (r i) hi.1 hi.2 b T hT γ).2
  · exact hconv

end MatedCRT

