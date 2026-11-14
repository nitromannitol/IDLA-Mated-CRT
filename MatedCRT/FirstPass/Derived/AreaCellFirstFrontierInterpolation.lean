import MatedCRT.FirstPass.Derived.AreaCellFirstFrontierContainment
import LatticeProb.Walk.CellConfigInnerBoundary

/-! # Interpolation through the first frontier cell -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain

/-- On one full-measure event, each shifted walk starting in an inner ball
reaches its first frontier cell while its interpolation stays in the outer ball,
provided its cells, adjacency, clock, and representatives satisfy the stated conditions. -/
theorem ae_exists_first_frontier_hit_interpolation_mem_outer_ball_areaCell
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (hc : (areaCellConfig h hε m).IsCellConfiguration)
    (hpos : ∀ C, 0 < (areaCellConfig h hε m).holding C) (x : ℤ) :
    ∀ᵐ ξ ∂(srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
        (fun ξ n => euclideanCellEquiv h hε (ξ n)),
      ∀ (ρ R d : ℝ) (K : ℕ), ρ < 1 → ρ ≤ R →
        (∀ k, (cell ε η k ∩ ball 0 1).Nonempty → diam (cell ε η k) ≤ d) →
        d < R - ρ →
        (((ξ K).1 : Set ReflectedGMS.Plane) ∩
          ball (Complex.orthonormalBasisOneI.repr 0) ρ).Nonempty →
        ∃ n : ℕ,
          (((ξ (K + n)).1 : Set ReflectedGMS.Plane) ∩
            frontier (ball (Complex.orthonormalBasisOneI.repr 0) ρ)).Nonempty ∧
          (∀ j < n, ¬ (((ξ (K + j)).1 : Set ReflectedGMS.Plane) ∩
            frontier (ball (Complex.orthonormalBasisOneI.repr 0) ρ)).Nonempty) ∧
          ((ξ (K + n)).1 : Set ReflectedGMS.Plane) ⊆
            ball (Complex.orthonormalBasisOneI.repr 0) R ∧
          ∀ (p : (areaCellConfig h hε m).cells → ReflectedGMS.Plane),
            (∀ C, p C ∈ (C.1 : Set ReflectedGMS.Plane)) →
            (∀ j, (areaCellConfig h hε m).Adj (ξ (K + j)) (ξ (K + (j + 1)))) →
            (areaCellConfig h hε m).JumpTimesUnbounded (fun j => ξ (K + j)) →
            ∀ s : ℝ, 0 ≤ s → s ≤ (areaCellConfig h hε m).jumpTime (fun j => ξ (K + j)) n →
              (areaCellConfig h hε m).interpolatedPath p (fun j => ξ (K + j)) s ∈
                ball (Complex.orthonormalBasisOneI.repr 0) R := by
  filter_upwards [ae_exists_first_frontier_hit_subset_outer_ball_areaCell
    h hε m hlf H hH hconn x] with ξ hξ
  intro ρ R d K hρ hρR hd hgap hstart
  obtain ⟨n, hn, hbefore, hlast⟩ := hξ ρ R d K hρ hd hgap hstart
  refine ⟨n, hn, hbefore, hlast, ?_⟩
  intro p hp hadj hunb s hs hst
  exact LatticeProb.CellConfigBoundary.interpolatedPath_mem_through_inner_boundary
    (areaCellConfig h hε m) hc isOpen_ball (ball_subset_ball hρR)
    (convex_ball _ _) p hp (fun j => ξ (K + j)) (by simpa using hstart)
    hadj hpos hunb hs hst hbefore hlast

end MatedCRT
end
