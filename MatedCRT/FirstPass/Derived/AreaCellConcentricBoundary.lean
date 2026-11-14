import MatedCRT.FirstPass.Derived.AreaCellInnerBoundary

/-! # Concentric ball boundary containment for area-parametrized cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS.GMS

/-- A cell meeting the inner ball frontier lies in the outer ball when its
integer-labelled diameter is smaller than the difference of the radii. -/
theorem areaCellConfig_subset_outer_ball_of_meeting_frontier
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ) (z : ℂ) (ρ R d : ℝ)
    (hd : ∀ k ∈ cellVertices ε η (frontier (ball z ρ)),
      diam (cell ε η k) ≤ d) (hgap : d < R - ρ)
    (K : (areaCellConfig h hε m).cells)
    (hK : ((K.1 : Set ReflectedGMS.Plane) ∩
      frontier (Complex.orthonormalBasisOneI.repr '' ball z ρ)).Nonempty) :
    (K.1 : Set ReflectedGMS.Plane) ⊆
      ball (Complex.orthonormalBasisOneI.repr z) R := by
  let s : ℝ := (d + (R - ρ)) / 2
  have hds : d < s := by dsimp [s]; linarith
  have hs : s + ρ ≤ R := by dsimp [s]; linarith
  apply areaCellConfig_subset_of_meeting_frontier h hε m (ball z ρ)
    (ball (Complex.orthonormalBasisOneI.repr z) R) hd hds ?_ K hK
  intro w hw
  have hball : Complex.orthonormalBasisOneI.repr '' ball z ρ =
      ball (Complex.orthonormalBasisOneI.repr z) ρ :=
    Complex.orthonormalBasisOneI.repr.toIsometryEquiv.image_ball z ρ
  rw [hball] at hw
  have hw' : dist w (Complex.orthonormalBasisOneI.repr z) = ρ :=
    Metric.mem_sphere.mp (Metric.frontier_ball_subset_sphere hw)
  exact ball_subset_ball' (by rw [hw']; exact hs)

end MatedCRT
