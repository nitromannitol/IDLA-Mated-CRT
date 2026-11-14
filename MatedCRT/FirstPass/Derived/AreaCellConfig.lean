import MatedCRT.FirstPass.Derived.AreaCellInjective
import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116Statement

/-! # Cell configurations from area-parametrized curves -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS

/-- The curve cell expressed as a nonempty compact Euclidean set. -/
def euclideanCell (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η) (hε : 0 < ε)
    (k : ℤ) : Cell where
  carrier := Complex.orthonormalBasisOneI.repr '' cell ε η k
  isCompact' := (isCompact_Icc.image hη).image Complex.orthonormalBasisOneI.repr.continuous
  nonempty' := by
    apply Set.Nonempty.image
    refine ⟨η (ε * k), ε * k, ⟨?_, le_rfl⟩, rfl⟩
    exact mul_le_mul_of_nonneg_left (by linarith) hε.le

@[simp] theorem coe_euclideanCell (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (hε : 0 < ε) (k : ℤ) :
    (euclideanCell ε η hη hε k : Set ReflectedGMS.Plane) =
      Complex.orthonormalBasisOneI.repr '' cell ε η k := rfl

/-- Area parametrization gives distinct compact Euclidean cells. -/
theorem euclideanCell_injective {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) :
    Function.Injective (euclideanCell ε η h.1 hε) := by
  intro j k hjk
  apply cell_injective_of_areaParametrized h hε
  apply Set.image_injective.mpr Complex.orthonormalBasisOneI.repr.injective
  exact congrArg (fun K : Cell => (K : Set ReflectedGMS.Plane)) hjk

/-- The integer labels identify precisely the compact cells of the curve. -/
noncomputable def euclideanCellEquiv {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) :
    ℤ ≃ Set.range (euclideanCell ε η h.1 hε) :=
  Equiv.ofInjective _ (euclideanCell_injective h hε)

/-- The curve cells with the conductances of an integer-indexed multigraph. -/
noncomputable def areaCellConfig {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) :
    CellConfig := by
  classical
  refine ⟨Set.range (euclideanCell ε η h.1 hε), ?_⟩
  intro A B
  exact if ha : A ∈ Set.range (euclideanCell ε η h.1 hε) then
    if hb : B ∈ Set.range (euclideanCell ε η h.1 hε) then
      (m ((euclideanCellEquiv h hε).symm ⟨A, ha⟩)
        ((euclideanCellEquiv h hε).symm ⟨B, hb⟩) : ℝ)
    else 0
    else 0

/-- Conductance preserves the full edge multiplicity, including parallel edges. -/
theorem areaCellConfig_conductance {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (a b : ℤ) :
    (areaCellConfig h hε m).c (euclideanCellEquiv h hε a)
      (euclideanCellEquiv h hε b) = (m a b : ℝ) := by
  classical
  simp [areaCellConfig, euclideanCellEquiv]

end MatedCRT
