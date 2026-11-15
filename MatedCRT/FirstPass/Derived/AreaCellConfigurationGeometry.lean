import MatedCRT.FirstPass.Derived.AreaCellConfigurationLocal

/-! # Geometry of area-cell configurations -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic

/-- Each cell of a matching cellular embedding is connected in Euclidean coordinates. -/
theorem areaCellConfig_isConnected {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε η) :
    ∀ K ∈ (areaCellConfig h hε m).cells, IsConnected (K : Set ReflectedGMS.Plane) := by
  rintro K ⟨k, rfl⟩
  rw [coe_euclideanCell, ← hH]
  exact (H.isConnected_cell k).image _ Complex.orthonormalBasisOneI.repr.continuous.continuousOn

/-- Each cell of a matching cellular embedding has nonempty Euclidean interior. -/
theorem areaCellConfig_interior_nonempty {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε η) :
    ∀ K ∈ (areaCellConfig h hε m).cells, (interior (K : Set ReflectedGMS.Plane)).Nonempty := by
  rintro K ⟨k, rfl⟩
  rw [coe_euclideanCell, ← hH]
  change (interior (Complex.orthonormalBasisOneI.repr.toHomeomorph '' H.cell k)).Nonempty
  rw [← Complex.orthonormalBasisOneI.repr.toHomeomorph.image_interior]
  exact (H.interior_cell_nonempty k).image _

/-- The cells of a matching cellular embedding cover the Euclidean plane. -/
theorem areaCellConfig_iUnion_eq_univ {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε η) :
    (⋃ K ∈ (areaCellConfig h hε m).cells, (K : Set ReflectedGMS.Plane)) = univ := by
  apply eq_univ_iff_forall.mpr
  intro z
  have hz : Complex.orthonormalBasisOneI.repr.symm z ∈ ⋃ k, H.cell k := by
    rw [H.iUnion_cell]
    exact mem_univ _
  obtain ⟨k, hk⟩ := mem_iUnion.mp hz
  refine mem_iUnion.mpr ⟨euclideanCell ε η h.1 hε k, mem_iUnion.mpr ⟨⟨k, rfl⟩, ?_⟩⟩
  rw [coe_euclideanCell, ← hH]
  exact ⟨Complex.orthonormalBasisOneI.repr.symm z, hk,
    Complex.orthonormalBasisOneI.repr.apply_symm_apply z⟩

end MatedCRT
