import MatedCRT.FirstPass.Derived.AreaCellRepresentativeGeometry
import MatedCRT.FirstPass.Derived.SrwCellularExteriorVisit

/-! # Exterior visits for area-parametrized curve cells -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain

/-- An integer random walk, relabelled by area-parametrized curve cells, almost
surely visits a cell whose scaled endpoint representative is outside a bounded set. -/
theorem ae_visit_exterior_areaCellRepresentative
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    {s : ℝ} (hs : s ≠ 0) {U : Set ReflectedGMS.Plane}
    (hU : Bornology.IsBounded U) (x : ℤ)
    (Q : Measure (ℕ → (areaCellConfig h hε m).cells))
    (hQ : Q = (srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
      (fun ξ n => euclideanCellEquiv h hε (ξ n))) :
    ∀ᵐ ξ ∂Q, ∃ n : ℕ, s • areaCellRepresentative h hε m (ξ n) ∉ U := by
  let : Countable (areaCellConfig h hε m).cells :=
    Countable.of_equiv ℤ (euclideanCellEquiv h hε)
  have hexit := ae_visit_exterior_of_srwLaw_map_cellular
    (α := (areaCellConfig h hε m).cells) hlf hε.le H hconn
    (euclideanCellEquiv h hε)
    (fun K => Complex.orthonormalBasisOneI.repr.symm (areaCellRepresentative h hε m K))
    (areaCellRepresentative_mem_embedding h hε m H hH)
    Complex.orthonormalBasisOneI.repr hs hU x Q hQ
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hexit

end MatedCRT
end
