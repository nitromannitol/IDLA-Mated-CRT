import MatedCRT.FirstPass.Derived.AreaCellRepresentative
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Cells

/-! # Curve-cell representatives in cellular embeddings -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMS3

/-- The representative of an integer-labelled curve cell belongs to the
corresponding cell of an embedding of the curve cells. -/
theorem areaCellRepresentative_mem_embedding {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε η) (k : ℤ) :
    Complex.orthonormalBasisOneI.repr.symm
      (areaCellRepresentative h hε m (euclideanCellEquiv h hε k)) ∈ H.cell k := by
  rw [areaCellRepresentative_equiv, LinearIsometryEquiv.symm_apply_apply, hH]
  exact vertexPoint_mem_cell hε.le η k

/-- Only finitely many curve-cell representatives lie in a bounded set. -/
theorem finite_areaCellRepresentative_preimage {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε η) {U : Set ReflectedGMS.Plane} (hU : Bornology.IsBounded U) :
    {K : (areaCellConfig h hε m).cells | areaCellRepresentative h hε m K ∈ U}.Finite := by
  let f := Complex.orthonormalBasisOneI.repr
  have hbound : Bornology.IsBounded (f ⁻¹' U) :=
    f.isometry.antilipschitzWith.isBounded_preimage hU
  have hfin : {k : ℤ | areaCellRepresentative h hε m (euclideanCellEquiv h hε k) ∈ U}.Finite := by
    apply (finite_verticesMeeting H hbound).subset
    intro k hk
    refine ⟨f.symm (areaCellRepresentative h hε m (euclideanCellEquiv h hε k)),
      areaCellRepresentative_mem_embedding h hε m H hH k, ?_⟩
    change f (f.symm (areaCellRepresentative h hε m (euclideanCellEquiv h hε k))) ∈ U
    rw [f.apply_symm_apply]
    exact hk
  apply (hfin.image (euclideanCellEquiv h hε)).subset
  intro K hK
  refine ⟨(euclideanCellEquiv h hε).symm K, ?_, (euclideanCellEquiv h hε).apply_symm_apply K⟩
  change areaCellRepresentative h hε m
    (euclideanCellEquiv h hε ((euclideanCellEquiv h hε).symm K)) ∈ U
  rw [(euclideanCellEquiv h hε).apply_symm_apply]
  exact hK

end MatedCRT
end
