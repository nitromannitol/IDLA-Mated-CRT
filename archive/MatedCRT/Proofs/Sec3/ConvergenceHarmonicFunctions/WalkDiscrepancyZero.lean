import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.WalkDiscrepancyBound

/-! The constant boundary-data case of the same-walk comparison. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped NNReal

/-- If the Hölder constant is zero, the quenched mean discrepancy is zero. -/
theorem srwLaw_sameWalkExitDiscrepancy_integral_eq_zero_of_holder_zero
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (ψ : ℂ → ℝ) {χ : ℝ≥0}
    (hψ : HolderOnWith 0 χ ψ (closedBall z r))
    {ε : ℝ} (hε : 0 < ε) (ω : Ω) (v : ℤ)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) (hm : 0 < S.mε ε)
    (hη : Continuous (S.η ω))
    (hp : Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))
    (hv : v ∈ interiorCellVertices ε (S.η ω) (ball z r)) :
    (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) = 0 := by
  have hzero : ∀ᵐ x ∂srwLaw (S.mult ε ω) v, sameWalkExitDiscrepancy S r z ψ ε ω x = 0 := by
    filter_upwards [srwLaw_ae_sameWalkExitDiscrepancy_le_disk_diameter S hr z ψ hψ hε ω v
      hlf hcons hm hη hp hv] with x hx
    apply le_antisymm
    · simpa using hx
    · exact abs_nonneg _
  calc
    (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) =
        ∫ _x, (0 : ℝ) ∂srwLaw (S.mult ε ω) v := integral_congr_ae hzero
    _ = 0 := integral_zero _ _

end MatedCRT

#print axioms MatedCRT.srwLaw_sameWalkExitDiscrepancy_integral_eq_zero_of_holder_zero
