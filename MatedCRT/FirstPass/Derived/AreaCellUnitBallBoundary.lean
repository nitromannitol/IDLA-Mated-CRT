import MatedCRT.FirstPass.Derived.AreaCellConcentricBoundary

/-! # Concentric area-cell boundaries under a unit-ball diameter bound -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS.GMS

/-- A diameter bound on all cells meeting the unit ball controls cells meeting
an inner concentric frontier. -/
theorem areaCellConfig_subset_outer_ball_of_unit_ball_diam
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) (ρ R d : ℝ)
    (hρ : ρ < 1)
    (hd : ∀ k, (cell ε η k ∩ ball 0 1).Nonempty → diam (cell ε η k) ≤ d)
    (hgap : d < R - ρ)
    (K : (areaCellConfig h hε m).cells)
    (hK : ((K.1 : Set ReflectedGMS.Plane) ∩
      frontier (ball (Complex.orthonormalBasisOneI.repr 0) ρ)).Nonempty) :
    (K.1 : Set ReflectedGMS.Plane) ⊆ ball (Complex.orthonormalBasisOneI.repr 0) R := by
  have hd' : ∀ k ∈ cellVertices ε η (frontier (ball 0 ρ)),
      diam (cell ε η k) ≤ d := by
    intro k hk
    obtain ⟨z, hzcell, hzfrontier⟩ := hk
    apply hd k
    refine ⟨z, hzcell, ?_⟩
    have hz : dist z (0 : ℂ) = ρ := Metric.mem_sphere.mp
      (Metric.frontier_ball_subset_sphere hzfrontier)
    exact Metric.mem_ball.mpr (hz ▸ hρ)
  apply areaCellConfig_subset_outer_ball_of_meeting_frontier h hε m 0 ρ R d hd' hgap K
  have hball : Complex.orthonormalBasisOneI.repr '' ball (0 : ℂ) ρ =
      ball (Complex.orthonormalBasisOneI.repr 0) ρ :=
    Complex.orthonormalBasisOneI.repr.toIsometryEquiv.image_ball 0 ρ
  simpa only [hball] using hK

end MatedCRT
