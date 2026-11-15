import MatedCRT.FirstPass.Derived.ValidCurveFixedTime
import MatedCRT.FirstPass.Derived.ValidCurveSimultaneousComponentIdentity

/-! # Visit times of a selected component of a valid curve -/

set_option autoImplicit false

open MeasureTheory Set

namespace MatedCRT

/-- For a fixed segment and deterministic interior time, a selected component
with a bounded interval-image witness has the corresponding visit-time identity
for almost every time. The interval-image hypothesis is explicit. -/
theorem MatedCRTEnv.IsValid.ae_selected_component_visit_identity
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {a u b : ℝ}
    (hau : a < u) (hub : u < b) {η : Ω → C(ℝ, ℂ)}
    (hη : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω) (A B : Ω → ℝ)
    (hcomponent : ∀ᵐ ω ∂S.P,
      a ≤ A ω ∧ A ω < B ω ∧ B ω ≤ b ∧
      (η ω) '' Icc (A ω) (B ω) =
        closure (connectedComponentIn (interior ((η ω) '' Icc a b)) (η ω u))) :
    ∀ᵐ ω ∂S.P, a ≤ A ω ∧ A ω < B ω ∧ B ω ≤ b ∧
      ∀ᵐ r ∂volume, η ω r ∈
        connectedComponentIn (interior ((η ω) '' Icc a b)) (η ω u) ↔
          r ∈ Ioo (A ω) (B ω) := by
  filter_upwards [hη, hcomponent, hS.ae_fixedTime_mem_interior_image u,
    FirstPass.Derived.MatedCRTEnv.IsValid.ae_simultaneous_component_visit_identity hS
      (hau.trans hub)] with ω he hc hi hv
  refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
  have hi' : η ω u ∈ interior ((η ω) '' Icc a b) := by
    simpa only [he] using hi a b hau hub
  filter_upwards [hv] with r hr
  have h := hr (S.η ω u) (by simpa only [he] using hi') (A ω) (B ω)
    hc.2.1 (by simpa only [he] using hc.2.2.2)
  simpa only [he] using h

end MatedCRT
