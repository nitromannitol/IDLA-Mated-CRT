import MatedCRT.FirstPass.Derived.AreaCellConfig

/-! # Conductance rows of area-cell configurations -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- Total conductance of a curve cell, indexed by the integer vertices. -/
theorem areaCellConfig_pi_eq_tsum {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (a : ℤ) :
    (areaCellConfig h hε m).pi (euclideanCellEquiv h hε a) =
      ∑' b : ℤ, (m a b : ℝ) := by
  unfold CellConfig.pi
  calc
    _ = ∑' b : ℤ, (areaCellConfig h hε m).c
        (euclideanCellEquiv h hε a) (euclideanCellEquiv h hε b) :=
      ((euclideanCellEquiv h hε).tsum_eq _).symm
    _ = _ := tsum_congr (areaCellConfig_conductance h hε m a)

/-- Reciprocal conductance of a curve cell, indexed by integer vertices. -/
theorem areaCellConfig_piStar_eq_tsum {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (a : ℤ) :
    (areaCellConfig h hε m).piStar (euclideanCellEquiv h hε a) =
      ∑' b : ℤ, (m a b : ℝ)⁻¹ := by
  unfold CellConfig.piStar
  calc
    _ = ∑' b : ℤ, ((areaCellConfig h hε m).c
        (euclideanCellEquiv h hε a) (euclideanCellEquiv h hε b))⁻¹ :=
      ((euclideanCellEquiv h hε).tsum_eq _).symm
    _ = _ := tsum_congr fun b => congrArg Inv.inv (areaCellConfig_conductance h hε m a b)

end MatedCRT
