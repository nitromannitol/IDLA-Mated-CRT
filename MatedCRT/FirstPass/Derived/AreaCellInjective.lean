import MatedCRT.Defs.Setting
import LatticeProb.Analysis.AreaParametrizedCurveCells

/-! # Distinct cells of an area-parametrized curve -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set

/-- Positive-mesh cells of an area-parametrized curve have distinct integer indices. -/
theorem cell_injective_of_areaParametrized {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) :
    Function.Injective (cell ε η) := by
  intro j k heq
  by_contra hjk
  have hmass : 0 < μ (cell ε η j) := by
    rw [cell, h.2.2.2 _ _ (mul_lt_mul_of_pos_left (by linarith) hε)]
    apply ENNReal.ofReal_pos.mpr
    nlinarith
  have hnull : μ (cell ε η j ∩ cell ε η k) = 0 := by
    rcases lt_or_gt_of_ne hjk with hjk' | hkj
    · have hle : (j : ℝ) + 1 ≤ k := by exact_mod_cast Int.add_one_le_iff.mpr hjk'
      exact LatticeProb.measure_image_Icc_inter_image_Icc_eq_zero h.1 h.2.2.2
        (mul_lt_mul_of_pos_left (by linarith) hε)
        (mul_le_mul_of_nonneg_left (by linarith) hε.le)
        (mul_lt_mul_of_pos_left (by linarith) hε)
    · rw [inter_comm]
      have hle : (k : ℝ) + 1 ≤ j := by exact_mod_cast Int.add_one_le_iff.mpr hkj
      exact LatticeProb.measure_image_Icc_inter_image_Icc_eq_zero h.1 h.2.2.2
        (mul_lt_mul_of_pos_left (by linarith) hε)
        (mul_le_mul_of_nonneg_left (by linarith) hε.le)
        (mul_lt_mul_of_pos_left (by linarith) hε)
  rw [← heq, inter_self] at hnull
  exact (ne_of_gt hmass) hnull

end MatedCRT
