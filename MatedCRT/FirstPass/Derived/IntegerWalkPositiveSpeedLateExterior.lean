import MatedCRT.FirstPass.Derived.IntegerWalkEscapeSubsequence
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellWindow

/-! # Late exterior visits of the embedded walk at positive speeds -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain
open scoped ENNReal NNReal

/-- On one almost-sure event, the integer-indexed interpolated walk visits the exterior of
any bounded set arbitrarily late, simultaneously for every positive speed. -/
theorem ae_visit_all_exteriors_late_all_positive_speeds_integerWalk
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
        ∀ T : ℝ≥0, ∃ t : ℝ≥0, T ≤ t ∧ interpolatedWalk ε η v ξ t ∉ U := by
  filter_upwards [ae_exists_escape_subsequence_vertexPoint h hε m hlf H hH hconn
    (s := 1) one_ne_zero x] with ξ hξ
  obtain ⟨f, hfmono, hf⟩ := hξ
  intro v hv U hU T
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hU
  obtain ⟨k, hk⟩ := exists_nat_gt (max R ((T : ℝ) * v))
  have hkR : R < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) hk
  have hkT : (T : ℝ) * v < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
  have hfk : (k : ℝ) ≤ (f k : ℝ) := by
    exact_mod_cast hfmono.id_le k
  have hnorm : (k : ℝ) ≤ ‖vertexPoint ε η (ξ (f k))‖ := by
    simpa only [one_smul, LinearIsometryEquiv.norm_map] using hf k
  have hout : vertexPoint ε η (ξ (f k)) ∉ U := by
    intro hmem
    have := hR _ hmem
    linarith
  refine ⟨((f k : ℝ) / v).toNNReal, ?_, ?_⟩
  · apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) hv.le)]
    apply (le_div_iff₀ hv).2
    linarith
  · rw [interpolatedWalk_natCast_div hv]
    exact hout

end MatedCRT
end
