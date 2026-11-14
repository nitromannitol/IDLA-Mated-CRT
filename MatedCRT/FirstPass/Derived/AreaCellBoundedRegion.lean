import MatedCRT.FirstPass.Derived.AreaCellFiniteNeighbors
import MatedCRT.FirstPass.Derived.AreaCellRepresentativeGeometry

/-! # Finite regions for bounded sets of cell representatives -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMS3

/-- A bounded set of representatives and an arbitrary initial cell lie in a finite
region retaining every conductance neighbor of each representative in the set. -/
theorem areaCellConfig_exists_finite_region_of_bounded_representatives
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) (hlf : IsLocallyFiniteMult m)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε η) {U : Set ReflectedGMS.Plane}
    (hU : Bornology.IsBounded U) (start : (areaCellConfig h hε m).cells) :
    ∃ R : Set (areaCellConfig h hε m).cells, R.Finite ∧ start ∈ R ∧
      (∀ v, areaCellRepresentative h hε m v ∈ U → v ∈ R) ∧
      ∀ v, areaCellRepresentative h hε m v ∈ U →
        ∀ w, w ∉ R → (areaCellConfig h hε m).c v w = 0 := by
  let A := {v : (areaCellConfig h hε m).cells | areaCellRepresentative h hε m v ∈ U}
  have hA : A.Finite := finite_areaCellRepresentative_preimage h hε m H hH hU
  obtain ⟨R, hR, hAR, hretain⟩ :=
    areaCellConfig_exists_finite_conductance_region h hε m hlf A hA
  refine ⟨R ∪ {start}, hR.union (Set.finite_singleton start), Or.inr rfl, ?_, ?_⟩
  · intro v hv
    exact Or.inl (hAR hv)
  · intro v hv w hw
    exact hretain v hv w (fun hwR => hw (Or.inl hwR))

end MatedCRT
