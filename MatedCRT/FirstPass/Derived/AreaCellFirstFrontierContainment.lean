import MatedCRT.FirstPass.Derived.AreaCellShiftedFrontierHit
import MatedCRT.FirstPass.Derived.AreaCellUnitBallBoundary

/-! # First frontier hit of an area-cell walk -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Metric Set ReflectedGMS.GMS
open MatedCRTHarmonic MatedCRTHarmonic.Markov MatedCRTHarmonic.GMSMain

/-- Uniformly over shifts and concentric balls, the first inner-frontier cell
visited by the walk is contained in the outer ball under a diameter bound. -/
theorem ae_exists_first_frontier_hit_subset_outer_ball_areaCell
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (x : ℤ) :
    ∀ᵐ ξ ∂(srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x).map
        (fun ξ n => euclideanCellEquiv h hε (ξ n)),
      ∀ (ρ R d : ℝ) (K : ℕ), ρ < 1 →
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
            ball (Complex.orthonormalBasisOneI.repr 0) R := by
  classical
  filter_upwards [ae_hitTime_frontier_ne_top_all_bounded_open_all_shifts_areaCell
    h hε m hlf H hH hconn x] with ξ hξ
  intro ρ R d K hρ hd hgap hstart
  have hh := hξ (ball (Complex.orthonormalBasisOneI.repr 0) ρ)
    Metric.isBounded_ball isOpen_ball K hstart
  obtain ⟨n, hn⟩ := hitTime_ne_top_iff.mp hh
  let P : ℕ → Prop := fun n =>
    (((ξ (K + n)).1 : Set ReflectedGMS.Plane) ∩
      frontier (ball (Complex.orthonormalBasisOneI.repr 0) ρ)).Nonempty
  have hex : ∃ n, P n := ⟨n, hn⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_, ?_⟩
  · intro j hj
    exact Nat.find_min hex hj
  · exact areaCellConfig_subset_outer_ball_of_unit_ball_diam h hε m ρ R d
      hρ hd hgap (ξ (K + Nat.find hex)) (Nat.find_spec hex)

end MatedCRT
end
