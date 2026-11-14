import MatedCRT.FirstPass.Derived.AreaCellHitTime

/-! # Euclidean ball frontier targets for area-parametrized cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS.GMS
open MatedCRTHarmonic.Markov

/-- Integer labels of cells meeting a Euclidean ball frontier. -/
theorem euclideanCellEquiv_preimage_meeting_ball_frontier
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) (z : ℂ) (r : ℝ) :
    (euclideanCellEquiv h hε) ⁻¹'
      {K : (areaCellConfig h hε m).cells |
        ((K.1 : Set ReflectedGMS.Plane) ∩
          frontier (ball (Complex.orthonormalBasisOneI.repr z) r)).Nonempty} =
      cellVertices ε η (frontier (ball z r)) := by
  have hball : Complex.orthonormalBasisOneI.repr '' ball z r =
      ball (Complex.orthonormalBasisOneI.repr z) r :=
    Complex.orthonormalBasisOneI.repr.toIsometryEquiv.image_ball z r
  simpa only [hball] using
    euclideanCellEquiv_preimage_meeting_frontier h hε m (ball z r)

/-- Hitting cells meeting a Euclidean ball frontier agrees with hitting their
integer labels. -/
theorem areaCell_hitTime_ball_frontier_eq
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) (z : ℂ) (r : ℝ) (x : ℕ → ℤ) :
    hitTime {K : (areaCellConfig h hε m).cells |
      ((K.1 : Set ReflectedGMS.Plane) ∩
        frontier (ball (Complex.orthonormalBasisOneI.repr z) r)).Nonempty}
        (fun n => euclideanCellEquiv h hε (x n)) =
      vHitTime (cellVertices ε η (frontier (ball z r))) x := by
  have hball : Complex.orthonormalBasisOneI.repr '' ball z r =
      ball (Complex.orthonormalBasisOneI.repr z) r :=
    Complex.orthonormalBasisOneI.repr.toIsometryEquiv.image_ball z r
  simpa only [hball] using
    areaCell_hitTime_frontier_eq h hε m (ball z r) x

end MatedCRT
