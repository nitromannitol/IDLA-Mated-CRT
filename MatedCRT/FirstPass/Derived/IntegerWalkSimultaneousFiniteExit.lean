import MatedCRT.FirstPass.Derived.IntegerWalkEscapeSubsequence
import MatedCRT.FirstPass.Derived.EmbeddedExitTimeInterp

/-! # Simultaneous bounded-set exit for the embedded walk -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.GMSMain
open scoped ENNReal NNReal

/-- Almost every integer-indexed interpolated walk exits every bounded set in finite time. -/
theorem ae_pathExitTime_ne_top_all_bounded_integerWalk
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (hlf : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
    (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε ω hlf) (0 : ℤ))
    (hH : H.cell = cell ε η)
    (hconn : (MatedCRTHarmonic.MatedCRT.graph ε ω hlf).adj.Connected)
    (x : ℤ) :
    ∀ᵐ ξ ∂srwLaw (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x,
      ∀ U : Set ℂ, Bornology.IsBounded U →
        HarmonicBalls.pathExitTime U (interpolatedWalk ε η 1 ξ) ≠ ∞ := by
  filter_upwards [ae_exists_escape_subsequence_vertexPoint h hε m hlf H hH hconn
    (s := 1) one_ne_zero x] with ξ hξ
  obtain ⟨f, -, hf⟩ := hξ
  intro U hU
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hU
  obtain ⟨k, hk⟩ := exists_nat_gt R
  have hnorm : (k : ℝ) ≤ ‖vertexPoint ε η (ξ (f k))‖ := by
    simpa only [one_smul, LinearIsometryEquiv.norm_map] using hf k
  have hout : vertexPoint ε η (ξ (f k)) ∉ U := by
    intro hmem
    have := hR _ hmem
    linarith
  have hle : HarmonicBalls.pathExitTime U (interpolatedWalk ε η 1 ξ) ≤
      ((f k : ℕ) : ℝ≥0∞) := by
    unfold HarmonicBalls.pathExitTime
    exact sInf_le ⟨(f k : ℝ≥0), by simp, by simpa only [interpolatedWalk_natCast] using hout⟩
  exact ne_top_of_le_ne_top (by simp) hle

end MatedCRT
end
