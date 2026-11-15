import MatedCRT.FirstPass.Derived.ProperAreaCurveVersion
import LatticeProb.Topology.AreaCurveRegularClosed

/-! # Regular closed segments of a valid space-filling curve -/

open MeasureTheory Set

namespace MatedCRT

/-- Almost surely, every nondegenerate time segment of the curve in a valid
    environment is the closure of its interior. -/
theorem MatedCRTEnv.IsValid.ae_regularClosed_segmentImages
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ a b : ℝ, a < b →
      closure (interior (S.η ω '' Icc a b)) = S.η ω '' Icc a b := by
  obtain ⟨η, _, hae⟩ := hS.exists_curveVersion
  filter_upwards [hae,
    FirstPass.Derived.MatedCRTEnv.IsValid.ae_proper_area_curveVersion hS hae] with ω he hp
  intro a b hab
  have h := LatticeProb.closure_interior_image_Icc_of_proper_area_curve
    (η ω) (S.μ ω) (η ω).continuous hp.1 hp.2.1 hp.2.2.2.symm
    (fun a b hab => hp.2.2.1 a b hab.le) hab
  simpa only [he] using h

end MatedCRT
