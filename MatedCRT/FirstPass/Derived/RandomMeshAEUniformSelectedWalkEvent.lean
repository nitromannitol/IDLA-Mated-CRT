import MatedCRT.FirstPass.Derived.RandomMeshUniformSelectedWalkEvent

/-! # Uniform selected-walk events at an almost surely positive mesh -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology
open scoped NNReal

/-- An existential selected-walk event is null measurable for an almost
surely positive, almost everywhere measurable random mesh. -/
theorem nullMeasurableSet_exists_ae_randomMesh_shiftedSelectedWalkLaw
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (ε : Ω → ℝ) (m : ℝ≥0)
    (η : Ω → C(ℝ, ℂ)) (w : Ω → C(ℝ, ℝ × ℝ)) (τ : Ω → ℝ)
    (hε : AEMeasurable ε P) (hεpos : ∀ᵐ ω ∂P, 0 < ε ω)
    (hη : Measurable η) (hw : Measurable w) (hτ : Measurable τ)
    (hcurve : ∀ᵐ ω ∂P, Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧
      Function.Surjective (η ω))
    (K : Set ℂ) (hK : MeasurableSet K)
    (B : Set (ℂ × Measure C(ℝ≥0, ℂ))) (hB : MeasurableSet B) :
    NullMeasurableSet {ω | ∃ x ∈ K,
      (x, shiftedSelectedWalkLaw (ε ω) m (τ ω) x (η ω) (w ω)) ∈ B} P := by
  let e : Ω → ℝ := hε.mk ε
  have he : Measurable e := hε.measurable_mk
  let e' : Ω → ℝ := fun ω => if 0 < e ω then e ω else 1
  have he'm : Measurable e' :=
    Measurable.ite (measurableSet_lt measurable_const he) he measurable_const
  have he'pos (ω : Ω) : 0 < e' ω := by
    dsimp only [e']
    split_ifs with h
    · exact h
    · exact zero_lt_one
  let ep : Ω → {r : ℝ // 0 < r} := fun ω => ⟨e' ω, he'pos ω⟩
  have hep : Measurable ep := he'm.subtype_mk
  have heq : ∀ᵐ ω ∂P, e' ω = ε ω := by
    filter_upwards [hε.ae_eq_mk, hεpos] with ω hω hp
    have h : e ω = ε ω := hω.symm
    simp only [e', h, hp, ↓reduceIte]
  have h := nullMeasurableSet_exists_randomMesh_shiftedSelectedWalkLaw
    P ep m η w τ hep hη hw hτ hcurve K hK B hB
  apply h.congr
  filter_upwards [heq] with ω hω
  simp only [ep, hω]

end MatedCRT
