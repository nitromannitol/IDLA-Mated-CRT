import MatedCRT.FirstPass.Derived.ShiftedSelectedWalkUnitMesh
import MatedCRT.FirstPass.Derived.UniformSelectedWalkEvent

/-! # Uniform selected-walk events under unit-mesh scaling -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace MatedCRT

/-- Unit-mesh scaling transports an existential event over all marked starts. -/
theorem exists_shiftedSelectedWalkLaw_unitMesh_rescale
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) {R : ℂ} (hR : R ≠ 0) (θ : ℝ)
    (w w' : C(ℝ, ℝ × ℝ))
    (hw : ∀ t, w' t = (c * (w (b * t)).1, c * (w (b * t)).2))
    (η η' : ℝ → ℂ) (hη : ∀ t, η' t = R⁻¹ * η (b * t))
    (m : ℝ≥0) (K : Set ℂ) (B : Set (ℂ × Measure C(ℝ≥0, ℂ))) :
    (∃ x ∈ K, (x, shiftedSelectedWalkLaw 1 m θ x η' w') ∈ B) ↔
    (∃ y, R⁻¹ * y ∈ K ∧
      (R⁻¹ * y, (shiftedSelectedWalkLaw b m (b * θ) y η w).map
        (fun p : C(ℝ≥0, ℂ) => ContinuousMap.const ℝ≥0 R⁻¹ * p)) ∈ B) := by
  constructor
  · rintro ⟨x, hx, hB⟩
    refine ⟨R * x, ?_, ?_⟩
    · simpa only [← mul_assoc, inv_mul_cancel₀ hR, one_mul] using hx
    · rw [shiftedSelectedWalkLaw_unitMesh_rescale hb hc hR θ w w' hw η η' hη m x] at hB
      simpa only [← mul_assoc, inv_mul_cancel₀ hR, one_mul] using hB
  · rintro ⟨y, hy, hB⟩
    refine ⟨R⁻¹ * y, hy, ?_⟩
    rw [shiftedSelectedWalkLaw_unitMesh_rescale hb hc hR θ w w' hw η η' hη m]
    simpa only [← mul_assoc, mul_inv_cancel₀ hR, one_mul] using hB

/-- A random-scale physical event is null measurable when its unit-mesh
representation has measurable data and an almost surely proper surjective curve. -/
theorem nullMeasurableSet_exists_shiftedSelectedWalkLaw_unitMesh_rescale
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (b c : Ω → ℝ) (R : Ω → ℂ) (θ : Ω → ℝ)
    (w w' : Ω → C(ℝ, ℝ × ℝ)) (η η' : Ω → C(ℝ, ℂ)) (m : ℝ≥0)
    (hθ : Measurable θ) (hw' : Measurable w') (hη' : Measurable η')
    (hcurve : ∀ᵐ ω ∂P, Tendsto (η' ω) (cocompact ℝ) (cocompact ℂ) ∧
      Function.Surjective (η' ω))
    (hscale : ∀ᵐ ω ∂P, 0 < b ω ∧ 0 < c ω ∧ R ω ≠ 0 ∧
      (∀ t, w' ω t = (c ω * (w ω (b ω * t)).1, c ω * (w ω (b ω * t)).2)) ∧
      (∀ t, η' ω t = (R ω)⁻¹ * η ω (b ω * t)))
    (K : Set ℂ) (hK : MeasurableSet K)
    (B : Set (ℂ × Measure C(ℝ≥0, ℂ))) (hB : MeasurableSet B) :
    NullMeasurableSet {ω | ∃ y, (R ω)⁻¹ * y ∈ K ∧
      ((R ω)⁻¹ * y, (shiftedSelectedWalkLaw (b ω) m (b ω * θ ω) y
        (η ω) (w ω)).map
          (fun p : C(ℝ≥0, ℂ) => ContinuousMap.const ℝ≥0 (R ω)⁻¹ * p)) ∈ B} P := by
  have h := nullMeasurableSet_exists_shiftedSelectedWalkLaw P zero_lt_one m
    η' w' θ hη' hw' hθ hcurve K hK B hB
  apply h.congr
  filter_upwards [hscale] with ω hω
  exact propext (exists_shiftedSelectedWalkLaw_unitMesh_rescale hω.1 hω.2.1 hω.2.2.1
    (θ ω) (w ω) (w' ω) hω.2.2.2.1 (η ω) (η' ω) hω.2.2.2.2 m K B)

end MatedCRT
