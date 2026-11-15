import MatedCRT.FirstPass.Derived.AreaCellTwoRootSum
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Second-moment bounds for the two cells at the origin -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS LatticeProb.CellConfigCappedSquare
open scoped ENNReal

/-- The weighted sum over cells containing the origin is bounded by the largest
root-cell ratio times the sum of the two weights. -/
theorem tsum_originAreaRatio_euclideanCell_le_max_mul
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (hf : ∀ t, η t = η 0 → t = 0)
    (w : ℤ → ℝ≥0∞) :
    (∑' k : ℤ, originAreaRatio (euclideanCell ε η h.1 hε k) * w k) ≤
      max (originAreaRatio (euclideanCell ε η h.1 hε 0))
          (originAreaRatio (euclideanCell ε η h.1 hε 1)) * (w 0 + w 1) := by
  rw [tsum_originAreaRatio_euclideanCell_eq_two_terms h hε hf]
  rw [mul_add]
  exact add_le_add (mul_le_mul' (le_max_left _ _) le_rfl)
    (mul_le_mul' (le_max_right _ _) le_rfl)

/-- If a nonnegative random variable is bounded by the two-root weighted sum,
then square moments of an upper bound for the root ratios and of the total
weight imply its finite expectation. No independence is needed. -/
theorem lintegral_lt_top_of_two_root_bounds
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {μ : Ω → Measure ℂ} {η : Ω → ℝ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (w : Ω → ℤ → ℝ≥0∞) (X A D : Ω → ℝ≥0∞)
    (hA : AEMeasurable A P) (hD : AEMeasurable D P)
    (hA2 : ∫⁻ ω, A ω ^ (2 : ℝ) ∂P < ∞)
    (hD2 : ∫⁻ ω, D ω ^ (2 : ℝ) ∂P < ∞)
    (hbound : ∀ᵐ ω ∂P, ∃ h : IsAreaParametrized (μ ω) (η ω),
      (∀ t, η ω t = η ω 0 → t = 0) ∧
      X ω ≤ ∑' k : ℤ, originAreaRatio (euclideanCell ε (η ω) h.1 hε k) * w ω k ∧
      originAreaRatio (euclideanCell ε (η ω) h.1 hε 0) ≤ A ω ∧
      originAreaRatio (euclideanCell ε (η ω) h.1 hε 1) ≤ A ω ∧
      w ω 0 + w ω 1 ≤ D ω) :
    ∫⁻ ω, X ω ∂P < ∞ := by
  have hle : ∀ᵐ ω ∂P, X ω ≤ A ω * D ω := by
    filter_upwards [hbound] with ω ⟨h, hf, hx, h0, h1, hw⟩
    exact hx.trans ((tsum_originAreaRatio_euclideanCell_le_max_mul h hε hf (w ω)).trans
      (mul_le_mul' (max_le h0 h1) hw))
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hA hD
  refine (lintegral_mono_ae hle).trans_lt (lt_of_le_of_lt hholder ?_)
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA2.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hD2.ne)

end MatedCRT
