import MatedCRT.FirstPass.Derived.ProperAreaCurveVersion
import LatticeProb.Topology.ProperAreaCurveFrontier
import LatticeProb.Topology.CurveComponentFrontier

/-! # Frontiers of area-parametrized curve segments -/

open MeasureTheory Set

namespace MatedCRT.FirstPass.Derived

/-- In a valid environment, every nondegenerate curve segment and every
component of its interior have frontier of zero area measure, simultaneously. -/
theorem MatedCRTEnv.IsValid.ae_curveSegment_frontier_null
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ a b : ℝ, a < b →
      S.μ ω (frontier (S.η ω '' Icc a b)) = 0 ∧
      ∀ x : ℂ, S.μ ω
        (frontier (connectedComponentIn (interior (S.η ω '' Icc a b)) x)) = 0 := by
  obtain ⟨η, _, hη⟩ := MatedCRTEnv.IsValid.exists_proper_area_curveVersion hS
  filter_upwards [hη] with ω hω
  rcases hω with ⟨heq, hp, hs, hm, _⟩
  intro a b hab
  have hfront : S.μ ω (frontier (η ω '' Icc a b)) = 0 :=
    LatticeProb.measure_frontier_image_Icc_eq_zero_of_proper (η ω) (S.μ ω)
      (η ω).continuous hp hs (fun u v huv => hm u v huv.le) hab
  have hcomp : ∀ x : ℂ, S.μ ω
      (frontier (connectedComponentIn (interior (η ω '' Icc a b)) x)) = 0 := by
    intro x
    exact LatticeProb.measure_frontier_component_interior_eq_zero
      (isCompact_Icc.image (η ω).continuous).isClosed (S.μ ω) hfront x
  rw [heq] at hfront hcomp
  exact ⟨hfront, hcomp⟩

end MatedCRT.FirstPass.Derived
