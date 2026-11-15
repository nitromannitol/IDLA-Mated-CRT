import MatedCRT.FirstPass.Derived.ProperAreaCurveVersion
import LatticeProb.Topology.AreaCurveSimultaneousComponentIdentity

/-! # Simultaneous component visit identities for valid curves -/

open MeasureTheory Set

namespace MatedCRT.FirstPass.Derived

/-- For a fixed segment of a valid curve, almost every time satisfies the visit
identity for every component and every nondegenerate interval-image witness.
The exceptional time set may depend on the segment and the environment. -/
theorem MatedCRTEnv.IsValid.ae_simultaneous_component_visit_identity
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {s t : ℝ} (hst : s < t) :
    ∀ᵐ ω ∂S.P, ∀ᵐ u ∂volume,
      ∀ x ∈ interior (S.η ω '' Icc s t), ∀ a b : ℝ, a < b →
        S.η ω '' Icc a b =
          closure (connectedComponentIn (interior (S.η ω '' Icc s t)) x) →
        (S.η ω u ∈ connectedComponentIn (interior (S.η ω '' Icc s t)) x ↔
          u ∈ Ioo a b) := by
  obtain ⟨η, _, hη⟩ := MatedCRTEnv.IsValid.exists_proper_area_curveVersion hS
  filter_upwards [hη] with ω hω
  rcases hω with ⟨heq, hp, hs, hm, hmap⟩
  have h := LatticeProb.ae_component_visit_identity_of_proper_area_curve
    (η ω) (S.μ ω) (η ω).continuous hp hs hmap.symm
    (fun a b hab => hm a b hab.le) hst
  simpa only [heq] using h

end MatedCRT.FirstPass.Derived
