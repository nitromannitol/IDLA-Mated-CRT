import MatedCRT.FirstPass.Derived.ValidComponentEndpointObservations
import LatticeProb.Topology.ComponentVisitEndpoints

/-! # Selected component intervals and their observations -/

set_option autoImplicit false

open MeasureTheory MeasurableSpace Set
open LatticeProb LatticeProb.CorrelatedBM MatedCRTHarmonic.MatedCRT

namespace MatedCRT

/-- A component interval witnessing the closure of the component containing a
fixed interior-time curve point is almost surely nondegenerate. -/
theorem MatedCRTEnv.IsValid.ae_selected_component_interval_strict
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {a u b : ℝ}
    (hau : a < u) (hub : u < b) {η : Ω → C(ℝ, ℂ)}
    (hη : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω) (A B : Ω → ℝ)
    (himage : ∀ᵐ ω ∂S.P, (η ω) '' Icc (A ω) (B ω) =
      closure (connectedComponentIn (interior ((η ω) '' Icc a b)) (η ω u))) :
    ∀ᵐ ω ∂S.P, A ω < B ω := by
  filter_upwards [hη, himage, hS.ae_fixedTime_mem_interior_image u] with ω he hi hu
  have hu' : η ω u ∈ interior ((η ω) '' Icc a b) := by
    simpa only [he] using hu a b hau hub
  exact interval_lt_of_image_eq_closure_open (η ω)
    (connectedComponentIn (interior ((η ω) '' Icc a b)) (η ω u))
    (A ω) (B ω) isOpen_interior.connectedComponentIn
    ⟨η ω u, mem_connectedComponentIn hu'⟩ hi

/-- Two-sided observation of the visit code gives segment-observable endpoint
versions for bounded component interval witnesses. -/
theorem MatedCRTEnv.IsValid.exists_segment_observable_component_endpoints_of_closure
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {a u b : ℝ}
    (hau : a < u) (hub : u < b) (η : Ω → C(ℝ, ℂ))
    (hη : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω) (A B : Ω → ℝ)
    (hpast : AELeSigma (MeasurableSpace.comap
      (fun ω (q : {q : ℚ // (q : ℝ) ∈ Icc a b}) =>
        curveComponentVisitCode (Icc a b) (η ω) (η ω u) q.1) inferInstance)
      ((incrementSigma lrCoord (Iic b) b).comap S.bm) S.P)
    (hfuture : AELeSigma (MeasurableSpace.comap
      (fun ω (q : {q : ℚ // (q : ℝ) ∈ Icc a b}) =>
        curveComponentVisitCode (Icc a b) (η ω) (η ω u) q.1) inferInstance)
      ((incrementSigma lrCoord (Ici a) a).comap S.bm) S.P)
    (hcomponent : ∀ᵐ ω ∂S.P,
      a ≤ A ω ∧ B ω ≤ b ∧
      (η ω) '' Icc (A ω) (B ω) =
        closure (connectedComponentIn (interior ((η ω) '' Icc a b)) (η ω u))) :
    ∃ A' B' : Path2 → ℝ,
      Measurable[incrementSigma lrCoord (Icc a b) a] A' ∧
      Measurable[incrementSigma lrCoord (Icc a b) a] B' ∧
      (∀ᵐ ω ∂S.P, A' (S.bm ω) = A ω ∧ B' (S.bm ω) = B ω) := by
  have himage : ∀ᵐ ω ∂S.P, (η ω) '' Icc (A ω) (B ω) =
      closure (connectedComponentIn (interior ((η ω) '' Icc a b)) (η ω u)) :=
    hcomponent.mono fun _ h => h.2.2
  have hstrict := hS.ae_selected_component_interval_strict hau hub hη A B himage
  apply hS.exists_segment_observable_component_endpoints hau hub η hη A B hpast hfuture
  filter_upwards [hcomponent, hstrict] with ω hc hs
  exact ⟨hc.1, hs, hc.2.1, hc.2.2⟩

end MatedCRT
