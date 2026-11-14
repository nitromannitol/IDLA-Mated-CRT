import MatedCRT.FirstPass.Derived.AreaCellRepresentativeGeometry

/-! # Local finiteness of curve-cell configurations -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMS3

/-- A bounded Euclidean set meets only finitely many curve cells in a
locally finite embedding. -/
theorem finite_areaCellConfig_cells_meeting {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε η) {U : Set ReflectedGMS.Plane} (hU : Bornology.IsBounded U) :
    {K : (areaCellConfig h hε m).cells | ((K.1 : Set ReflectedGMS.Plane) ∩ U).Nonempty}.Finite := by
  let f := Complex.orthonormalBasisOneI.repr
  have hbound : Bornology.IsBounded (f ⁻¹' U) :=
    f.isometry.antilipschitzWith.isBounded_preimage hU
  have hfin : {k : ℤ | (((euclideanCellEquiv h hε k).1 : Set ReflectedGMS.Plane) ∩ U).Nonempty}.Finite := by
    apply (finite_verticesMeeting H hbound).subset
    intro k hk
    obtain ⟨z, hz, hzU⟩ := hk
    change z ∈ f '' cell ε η k at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, by rw [hH]; exact hw, hzU⟩
  apply (hfin.image (euclideanCellEquiv h hε)).subset
  intro K hK
  refine ⟨(euclideanCellEquiv h hε).symm K, ?_, (euclideanCellEquiv h hε).apply_symm_apply K⟩
  change (((euclideanCellEquiv h hε ((euclideanCellEquiv h hε).symm K)).1 :
    Set ReflectedGMS.Plane) ∩ U).Nonempty
  rw [(euclideanCellEquiv h hε).apply_symm_apply]
  exact hK

end MatedCRT
