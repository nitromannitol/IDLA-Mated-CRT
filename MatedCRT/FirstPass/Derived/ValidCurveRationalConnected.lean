import MatedCRT.FirstPass.Derived.ProperAreaCurveVersion
import LatticeProb.Topology.AreaCurveRationalConnected

/-! # Connected segment interiors of valid curves -/

open MeasureTheory Set

namespace MatedCRT

/-- Fixed rational-segment connectedness assumptions yield connected interiors
and regular-closed images for all nondegenerate segments on one event. -/
theorem MatedCRTEnv.IsValid.ae_connected_segmentImages_of_rational
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hrat : ∀ p q : ℚ, (p : ℝ) < (q : ℝ) →
      ∀ᵐ ω ∂S.P, IsConnected (interior (S.η ω '' Icc (p : ℝ) (q : ℝ)))) :
    ∀ᵐ ω ∂S.P, ∀ a b : ℝ, a < b →
      IsConnected (interior (S.η ω '' Icc a b)) ∧
        closure (interior (S.η ω '' Icc a b)) = S.η ω '' Icc a b := by
  have hrat' : ∀ᵐ ω ∂S.P, ∀ p q : ℚ, (p : ℝ) < (q : ℝ) →
      IsConnected (interior (S.η ω '' Icc (p : ℝ) (q : ℝ))) := by
    apply ae_all_iff.mpr
    intro p
    apply ae_all_iff.mpr
    intro q
    by_cases hpq : (p : ℝ) < (q : ℝ)
    · filter_upwards [hrat p q hpq] with ω h _
      exact h
    · exact Filter.Eventually.of_forall fun _ h => (hpq h).elim
  obtain ⟨η, _, hae⟩ := hS.exists_curveVersion
  filter_upwards [hae, hrat',
    FirstPass.Derived.MatedCRTEnv.IsValid.ae_proper_area_curveVersion hS hae] with ω he hc hp
  have h := LatticeProb.connected_interior_image_Icc_of_rational_of_proper_area_curve
    (η ω) (S.μ ω) (η ω).continuous hp.1 hp.2.1 hp.2.2.2.symm
    (fun a b hab => hp.2.2.1 a b hab.le) (by simpa only [he] using hc)
  simpa only [he] using h

end MatedCRT
