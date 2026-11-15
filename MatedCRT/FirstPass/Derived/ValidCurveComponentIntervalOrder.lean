import MatedCRT.FirstPass.Derived.ProperAreaCurveVersion
import LatticeProb.Topology.AreaCurveComponentIntervalOrder

/-! # Interval order for components of valid curves -/

open MeasureTheory Set

namespace MatedCRT

/-- In a valid environment, interval-image witnesses for distinct components
of a curve segment are ordered, simultaneously for all segments and witnesses. -/
theorem MatedCRTEnv.IsValid.ae_component_interval_order
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ s t a b c d : ℝ, s < t → a < b → c < d →
      ∀ x y : ℂ,
      connectedComponentIn (interior (S.η ω '' Icc s t)) x ≠
        connectedComponentIn (interior (S.η ω '' Icc s t)) y →
      S.η ω '' Icc a b =
        closure (connectedComponentIn (interior (S.η ω '' Icc s t)) x) →
      S.η ω '' Icc c d =
        closure (connectedComponentIn (interior (S.η ω '' Icc s t)) y) →
      b ≤ c ∨ d ≤ a := by
  obtain ⟨η, _, hae⟩ := hS.exists_curveVersion
  filter_upwards [hae,
    FirstPass.Derived.MatedCRTEnv.IsValid.ae_proper_area_curveVersion hS hae] with ω he hp
  intro s t a b c d hst hab hcd x y hne hU hV
  apply LatticeProb.component_interval_order_of_proper_area_curve
    (η ω) (S.μ ω) (η ω).continuous hp.1 hp.2.1 hp.2.2.2.symm
    (fun a b hab => hp.2.2.1 a b hab.le) hst hab hcd x y
  · simpa only [he] using hne
  · simpa only [he] using hU
  · simpa only [he] using hV

end MatedCRT
