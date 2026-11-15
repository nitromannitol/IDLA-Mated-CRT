import MatedCRT.FirstPass.Derived.ValidCurveFixedTime
import LatticeProb.Topology.EmbeddedDiskConnectedInterior
import LatticeProb.Topology.AreaCurveRegularClosed

/-! # Components of disk-shaped curve segments -/

open MeasureTheory Set Metric

namespace MatedCRT

/-- If a fixed segment of a valid curve is disk-shaped, its component at a fixed
interior time has the whole segment as its closure. -/
theorem MatedCRTEnv.IsValid.ae_disk_segment_component_witness
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {a u b : ℝ}
    (hau : a < u) (hub : u < b)
    (hdisk : ∀ᵐ ω ∂S.P, Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (S.η ω '' Icc a b))) :
    ∀ᵐ ω ∂S.P,
      (connectedComponentIn (interior (S.η ω '' Icc a b)) (S.η ω u)).Nonempty ∧
      ∃ c d : ℝ, a ≤ c ∧ c ≤ d ∧ d ≤ b ∧
        closure (connectedComponentIn (interior (S.η ω '' Icc a b)) (S.η ω u)) =
          S.η ω '' Icc c d := by
  obtain ⟨η, _, hae⟩ := hS.exists_curveVersion
  filter_upwards [hS.ae_fixedTime_mem_interior_image u, hdisk, hae,
    FirstPass.Derived.MatedCRTEnv.IsValid.ae_proper_area_curveVersion hS hae] with ω hi hd he hp
  have hu := hi a b hau hub
  obtain ⟨e⟩ := hd
  have hc := LatticeProb.isConnected_interior_of_homeomorph_closedDisk e
  have heq := hc.isPreconnected.connectedComponentIn hu
  have hclosed := LatticeProb.closure_interior_image_Icc_of_proper_area_curve
    (η ω) (S.μ ω) (η ω).continuous hp.1 hp.2.1 hp.2.2.2.symm
    (fun c d hcd => hp.2.2.1 c d hcd.le) (hau.trans hub)
  refine ⟨⟨S.η ω u, ?_⟩, a, b, le_rfl, (hau.trans hub).le, le_rfl, ?_⟩
  · rw [heq]
    exact hu
  · rw [heq]
    simpa only [he] using hclosed

end MatedCRT
