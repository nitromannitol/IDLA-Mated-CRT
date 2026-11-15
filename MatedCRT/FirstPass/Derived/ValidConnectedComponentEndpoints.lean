import MatedCRT.FirstPass.Derived.ValidCurveFixedAnchorConnected
import MatedCRT.FirstPass.Derived.ValidExistentialComponentEndpoints

/-! # Observable endpoints of connected curve segments -/

set_option autoImplicit false

open MeasureTheory MeasurableSpace Set
open LatticeProb LatticeProb.CorrelatedBM MatedCRTHarmonic.MatedCRT

namespace MatedCRT

/-- Rational-segment connectedness gives constant, and hence observable,
component endpoints for a fixed time inside a segment. -/
theorem MatedCRTEnv.IsValid.exists_segment_component_endpoints_of_rational_connected
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {a u b : ℝ}
    (hau : a < u) (hub : u < b) (η : Ω → C(ℝ, ℂ))
    (hη : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω)
    (hrat : ∀ p q : ℚ, (p : ℝ) < (q : ℝ) →
      ∀ᵐ ω ∂S.P, IsConnected (interior (S.η ω '' Icc (p : ℝ) (q : ℝ)))) :
    ∃ A B : Path2 → ℝ,
      Measurable[incrementSigma lrCoord (Icc a b) a] A ∧
      Measurable[incrementSigma lrCoord (Icc a b) a] B ∧
      ∀ᵐ ω ∂S.P, a ≤ A (S.bm ω) ∧ B (S.bm ω) ≤ b ∧
        (η ω) '' Icc (A (S.bm ω)) (B (S.bm ω)) =
          closure (connectedComponentIn (interior ((η ω) '' Icc a b)) (η ω u)) := by
  refine ⟨fun _ => a, fun _ => b, measurable_const, measurable_const, ?_⟩
  filter_upwards [hS.ae_fixedTime_component_of_rational_connected u hrat, hη] with ω hω he
  refine ⟨le_rfl, le_rfl, ?_⟩
  simpa only [he] using (hω a b hau hub).2.2.symm

end MatedCRT
