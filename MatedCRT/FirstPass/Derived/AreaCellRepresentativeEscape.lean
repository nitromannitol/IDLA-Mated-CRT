import MatedCRT.FirstPass.Derived.AreaCellRepresentativeGeometry
import Mathlib.Topology.DiscreteSubset

/-! # Escape of curve-cell representatives -/

set_option autoImplicit false

namespace MatedCRT

open Filter MeasureTheory ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMS3

/-- Representatives escape every compact set along the cofinite filter on cells. -/
theorem tendsto_areaCellRepresentative_cocompact {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε η) :
    Tendsto (areaCellRepresentative h hε m) cofinite (cocompact ReflectedGMS.Plane) := by
  apply tendsto_cofinite_cocompact_iff.mpr
  intro K hK
  exact finite_areaCellRepresentative_preimage h hε m H hH hK.isBounded

/-- Integer-labelled representatives escape every compact set as the label
leaves every finite set. -/
theorem tendsto_areaCellRepresentative_equiv_cocompact {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (hH : H.cell = cell ε η) :
    Tendsto (fun k : ℤ => areaCellRepresentative h hε m (euclideanCellEquiv h hε k))
      cofinite (cocompact ReflectedGMS.Plane) :=
  (tendsto_areaCellRepresentative_cocompact h hε m H hH).comp
    (euclideanCellEquiv h hε).injective.tendsto_cofinite

end MatedCRT
