import MatedCRT.FirstPass.Derived.AreaCellBallTargets
import MatedCRT.FirstPass.Derived.SrwHitLawSeparation

/-! # Hitting times of area-parametrized curve cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS.GMS
open MatedCRTHarmonic.Markov

/-- The first hit of a cell target equals the first hit of its integer labels. -/
theorem areaCell_hitTime_eq_vHitTime {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (I : Set (areaCellConfig h hε m).cells) (x : ℕ → ℤ) :
    hitTime I (fun n => euclideanCellEquiv h hε (x n)) =
      vHitTime ((euclideanCellEquiv h hε) ⁻¹' I) x := by
  rw [← hitTime_eq_vHitTime]
  rfl

/-- First hitting a Euclidean set of cells agrees with hitting its integer labels. -/
theorem areaCell_hitTime_meeting_eq {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (U : Set ReflectedGMS.Plane) (x : ℕ → ℤ) :
    hitTime {K : (areaCellConfig h hε m).cells |
      ((K.1 : Set ReflectedGMS.Plane) ∩ U).Nonempty}
        (fun n => euclideanCellEquiv h hε (x n)) =
      vHitTime (cellVertices ε η (Complex.orthonormalBasisOneI.repr ⁻¹' U)) x := by
  calc
    _ = vHitTime ((euclideanCellEquiv h hε) ⁻¹' {K : (areaCellConfig h hε m).cells |
        ((K.1 : Set ReflectedGMS.Plane) ∩ U).Nonempty}) x :=
      areaCell_hitTime_eq_vHitTime h hε m _ x
    _ = _ := congrArg (fun J : Set ℤ => vHitTime J x)
      (euclideanCellEquiv_preimage_meeting h hε m U)

/-- First hitting cells meeting a transported frontier agrees with integer hitting. -/
theorem areaCell_hitTime_frontier_eq {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (D : Set ℂ) (x : ℕ → ℤ) :
    hitTime {K : (areaCellConfig h hε m).cells |
      ((K.1 : Set ReflectedGMS.Plane) ∩
        frontier (Complex.orthonormalBasisOneI.repr '' D)).Nonempty}
        (fun n => euclideanCellEquiv h hε (x n)) =
      vHitTime (cellVertices ε η (frontier D)) x := by
  calc
    _ = vHitTime ((euclideanCellEquiv h hε) ⁻¹' {K : (areaCellConfig h hε m).cells |
        ((K.1 : Set ReflectedGMS.Plane) ∩
          frontier (Complex.orthonormalBasisOneI.repr '' D)).Nonempty}) x :=
      areaCell_hitTime_eq_vHitTime h hε m _ x
    _ = _ := congrArg (fun J : Set ℤ => vHitTime J x)
      (euclideanCellEquiv_preimage_meeting_frontier h hε m D)

/-- First hitting cells meeting a closed ball agrees with integer hitting. -/
theorem areaCell_hitTime_closedBall_eq {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (z : ℂ) (r : ℝ) (x : ℕ → ℤ) :
    hitTime {K : (areaCellConfig h hε m).cells |
      ((K.1 : Set ReflectedGMS.Plane) ∩
        closedBall (Complex.orthonormalBasisOneI.repr z) r).Nonempty}
        (fun n => euclideanCellEquiv h hε (x n)) =
      vHitTime (cellVertices ε η (closedBall z r)) x := by
  calc
    _ = vHitTime ((euclideanCellEquiv h hε) ⁻¹' {K : (areaCellConfig h hε m).cells |
        ((K.1 : Set ReflectedGMS.Plane) ∩
          closedBall (Complex.orthonormalBasisOneI.repr z) r).Nonempty}) x :=
      areaCell_hitTime_eq_vHitTime h hε m _ x
    _ = _ := congrArg (fun J : Set ℤ => vHitTime J x)
      (euclideanCellEquiv_preimage_meeting_closedBall h hε m z r)

end MatedCRT
