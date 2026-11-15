import MatedCRT.FirstPass.Derived.ValidCurveFixedTime
import MatedCRT.FirstPass.Derived.ValidCurveRationalConnected

/-! # Fixed-time components of connected curve segments -/

open MeasureTheory Set

namespace MatedCRT

/-- For a fixed time, rational-segment connectedness makes the selected
component of every strictly enclosing segment equal to its whole interior.
The connectedness hypothesis remains explicit. -/
theorem MatedCRTEnv.IsValid.ae_fixedTime_component_of_rational_connected
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (u : ℝ)
    (hrat : ∀ p q : ℚ, (p : ℝ) < (q : ℝ) →
      ∀ᵐ ω ∂S.P, IsConnected (interior (S.η ω '' Icc (p : ℝ) (q : ℝ)))) :
    ∀ᵐ ω ∂S.P, ∀ a b : ℝ, a < u → u < b →
      S.η ω u ∈ interior (S.η ω '' Icc a b) ∧
      connectedComponentIn (interior (S.η ω '' Icc a b)) (S.η ω u) =
        interior (S.η ω '' Icc a b) ∧
      closure (connectedComponentIn (interior (S.η ω '' Icc a b)) (S.η ω u)) =
        S.η ω '' Icc a b := by
  filter_upwards [hS.ae_fixedTime_mem_interior_image u,
    hS.ae_connected_segmentImages_of_rational hrat] with ω hmem hconn
  intro a b ha hb
  have hi := hmem a b ha hb
  have hc := hconn a b (ha.trans hb)
  have heq := hc.1.isPreconnected.connectedComponentIn hi
  refine ⟨hi, heq, ?_⟩
  rw [heq]
  exact hc.2

end MatedCRT
