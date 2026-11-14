import MatedCRT.FirstPass.Derived.AreaCellRepresentative
import MatedCRT.FirstPass.Derived.CellUniquePointDense

/-! # Injective representatives near the endpoints of curve cells -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- Curve cells admit injective representatives arbitrarily close to their endpoint
representatives. The choice is made for a fixed curve and need not be measurable
as the curve varies. -/
theorem exists_areaCell_injective_representative_near_endpoint
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ p : (areaCellConfig h hε m).cells → ReflectedGMS.Plane,
      Function.Injective p ∧
      (∀ K, p K ∈ (K.1 : Set ReflectedGMS.Plane)) ∧
      ∀ K, dist (areaCellRepresentative h hε m K) (p K) < r := by
  classical
  have hex (k : ℤ) : ∃ z : ℂ, dist (vertexPoint ε η k) z < r ∧
      z ∈ cell ε η k ∧ ∀ j ≠ k, z ∉ cell ε η j :=
    exists_dist_lt_mem_cell_notMem_cell_of_ne h hε
      (vertexPoint_mem_cell hε.le η k) hr
  let q : ℤ → ℂ := fun k => Classical.choose (hex k)
  have hq (k : ℤ) : dist (vertexPoint ε η k) (q k) < r ∧
      q k ∈ cell ε η k ∧ ∀ j ≠ k, q k ∉ cell ε η j :=
    Classical.choose_spec (hex k)
  have hqi : Function.Injective q := by
    intro j k hjk
    by_contra hne
    exact (hq j).2.2 k (Ne.symm hne) (hjk ▸ (hq k).2.1)
  let e := euclideanCellEquiv h hε
  let p : (areaCellConfig h hε m).cells → ReflectedGMS.Plane :=
    fun K => Complex.orthonormalBasisOneI.repr (q (e.symm K))
  refine ⟨p, ?_, ?_, ?_⟩
  · exact Complex.orthonormalBasisOneI.repr.injective.comp (hqi.comp e.symm.injective)
  · intro K
    obtain ⟨k, rfl⟩ := e.surjective K
    change Complex.orthonormalBasisOneI.repr (q (e.symm (e k))) ∈
      (euclideanCell ε η h.1 hε k : Set ReflectedGMS.Plane)
    rw [e.symm_apply_apply, coe_euclideanCell]
    exact ⟨q k, (hq k).2.1, rfl⟩
  · intro K
    obtain ⟨k, rfl⟩ := e.surjective K
    rw [areaCellRepresentative_equiv]
    change dist (Complex.orthonormalBasisOneI.repr (vertexPoint ε η k))
      (Complex.orthonormalBasisOneI.repr (q (e.symm (e k)))) < r
    rw [e.symm_apply_apply, Complex.orthonormalBasisOneI.repr.dist_map]
    exact (hq k).1

end MatedCRT
end
