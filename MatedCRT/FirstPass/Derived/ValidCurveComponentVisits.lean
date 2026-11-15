import MatedCRT.FirstPass.Derived.ValidAreaCurveFrontier
import LatticeProb.Topology.ComponentVisitIdentity

/-! # Visit times of components of valid curve segments -/

open MeasureTheory Set

namespace MatedCRT.FirstPass.Derived

/-- In a valid environment, a component with an interval-image witness is visited
at almost every time exactly during the interior of that interval. The exceptional
set of times may depend on the component and its witness. -/
theorem MatedCRTEnv.IsValid.ae_component_visit_time_identity
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ s t : ℝ, s < t → ∀ x : ℂ, ∀ a b : ℝ, a < b →
      S.η ω '' Icc a b =
        closure (connectedComponentIn (interior (S.η ω '' Icc s t)) x) →
      ∀ᵐ u ∂volume,
        S.η ω u ∈ connectedComponentIn (interior (S.η ω '' Icc s t)) x ↔
          u ∈ Ioo a b := by
  obtain ⟨η, _, hη⟩ := MatedCRTEnv.IsValid.exists_proper_area_curveVersion hS
  filter_upwards [hη, MatedCRTEnv.IsValid.ae_curveSegment_frontier_null hS] with ω hω hfront
  rcases hω with ⟨heq, _, _, hmass, hmap⟩
  intro s t hst x a b hab himage
  have hmass' : S.μ ω (η ω '' Icc a b) = volume (Icc a b) := by
    rw [hmass a b hab.le, Real.volume_Icc]
  have himage' : η ω '' Icc a b =
      closure (connectedComponentIn (interior (η ω '' Icc s t)) x) := by
    simpa only [heq] using himage
  have hfront' : S.μ ω
      (frontier (connectedComponentIn (interior (η ω '' Icc s t)) x)) = 0 := by
    simpa only [heq] using (hfront s t hst).2 x
  have h := LatticeProb.ae_visit_open_eq_interval (η ω) (S.μ ω)
    (connectedComponentIn (interior (η ω '' Icc s t)) x) a b
    (η ω).continuous.measurable hmap.symm isOpen_interior.connectedComponentIn
    hfront' himage' hmass'
  simpa only [heq] using h

end MatedCRT.FirstPass.Derived
