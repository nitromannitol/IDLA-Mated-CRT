import MatedCRT.FirstPass.Derived.IntegerWalkPositiveSpeedLateExterior

/-! # Shifted bounded-set exit for the embedded walk -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain
open scoped ENNReal NNReal

/-- On one almost-sure event, every nonnegative time shift of the embedded walk
at any positive speed exits every bounded set in finite time. -/
theorem ae_pathExitTime_shift_ne_top_all_positive_speeds_all_bounded_integerWalk
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (x : ℤ) :
    ∀ᵐ ξ ∂srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x,
      ∀ v : ℝ, 0 < v → ∀ U : Set ℂ, Bornology.IsBounded U →
        ∀ T : ℝ≥0, HarmonicBalls.pathExitTime U
          (fun t : ℝ≥0 => interpolatedWalk ε η v ξ (T + t)) ≠ ∞ := by
  filter_upwards [ae_visit_all_exteriors_late_all_positive_speeds_integerWalk
    h hε m hlf H hH hconn x] with ξ hξ
  intro v hv U hU T
  obtain ⟨t, ht, hout⟩ := hξ v hv U hU T
  have hle : HarmonicBalls.pathExitTime U
      (fun s : ℝ≥0 => interpolatedWalk ε η v ξ (T + s)) ≤
      ((t - T : ℝ≥0) : ℝ≥0∞) := by
    unfold HarmonicBalls.pathExitTime
    refine sInf_le ⟨t - T, rfl, ?_⟩
    dsimp only
    rwa [add_tsub_cancel_of_le ht]
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top hle

end MatedCRT
end
