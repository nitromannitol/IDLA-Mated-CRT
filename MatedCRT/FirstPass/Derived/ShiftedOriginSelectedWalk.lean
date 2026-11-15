import MatedCRT.FirstPass.Derived.ShiftedOriginSelectedVertex
import MatedCRT.FirstPass.Derived.ConeShiftedSelectedWalkLaw

/-! # The walk selected at the origin on a shifted grid -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory
open scoped NNReal

/-- The walk selected at a singleton-fibre origin starts at index zero. -/
theorem shiftedSelectedWalkLaw_origin_eq {η : ℝ → ℂ} (hzero : η 0 = 0)
    (hf : ∀ t, η t = η 0 → t = 0) {ε c : ℝ} (hε : 0 < ε)
    (hc : 0 < c ∧ c < ε) (m : ℝ≥0) (w : C(ℝ, ℝ × ℝ)) :
    shiftedSelectedWalkLaw ε m c 0 η w =
      (srwLaw (bmEdgeCount ε (fun t => (w (t + c)).1) (fun t => (w (t + c)).2)) 0).map
        (interpPathCM (vertexPoint ε (fun t => η (t + c))) m.coe_nonneg) := by
  unfold shiftedSelectedWalkLaw
  rw [vertexOf_shifted_origin_eq_zero hzero hf hε hc]

/-- One full-measure event identifies the selected origin walk for every positive
mesh, interior shift and interpolation rate. -/
theorem MatedCRTEnv.IsValid.ae_shiftedSelectedWalkLaw_origin
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ (ε : ℝ), 0 < ε → ∀ (c : ℝ), 0 < c → c < ε → ∀ m : ℝ≥0,
      shiftedSelectedWalkLaw ε m c 0 (S.η ω) (S.bm ω) =
        (srwLaw (bmEdgeCount ε (fun t => (S.bm ω (t + c)).1)
          (fun t => (S.bm ω (t + c)).2)) 0).map
          (interpPathCM (vertexPoint ε (fun t => S.η ω (t + c))) m.coe_nonneg) := by
  filter_upwards [hS.ae_vertexOf_shifted_origin] with ω h ε hε c hc hcε m
  unfold shiftedSelectedWalkLaw
  rw [h ε hε c hc hcε]

end MatedCRT
