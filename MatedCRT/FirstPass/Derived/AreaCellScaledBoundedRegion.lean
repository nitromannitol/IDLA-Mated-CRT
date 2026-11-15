import MatedCRT.FirstPass.Derived.AreaCellBoundedRegion

/-! # Finite regions for scaled cell representatives -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMS3
open scoped Pointwise

/-- A bounded set of nonzero-scaled representatives and an initial cell lie in
 a finite region retaining every conductance neighbor of each such cell. -/
theorem areaCellConfig_exists_finite_region_of_bounded_scaled_representatives
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) (hlf : IsLocallyFiniteMult m)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε η) {U : Set ReflectedGMS.Plane}
    (hU : Bornology.IsBounded U) {a : ℝ} (ha : a ≠ 0)
    (start : (areaCellConfig h hε m).cells) :
    ∃ R : Set (areaCellConfig h hε m).cells, R.Finite ∧ start ∈ R ∧
      (∀ v, a • areaCellRepresentative h hε m v ∈ U → v ∈ R) ∧
      ∀ v, a • areaCellRepresentative h hε m v ∈ U →
        ∀ w, w ∉ R → (areaCellConfig h hε m).c v w = 0 := by
  obtain ⟨R, hR, hstart, hmem, hretain⟩ :=
    areaCellConfig_exists_finite_region_of_bounded_representatives h hε m hlf H hH
      (hU.smul₀ a⁻¹) start
  have hinv : ∀ v, a • areaCellRepresentative h hε m v ∈ U →
      areaCellRepresentative h hε m v ∈ a⁻¹ • U := by
    intro v hv
    simpa only [inv_smul_smul₀ ha] using Set.smul_mem_smul_set (a := a⁻¹) hv
  exact ⟨R, hR, hstart, fun v hv => hmem v (hinv v hv),
    fun v hv => hretain v (hinv v hv)⟩

end MatedCRT
