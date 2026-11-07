import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationGreen

/-! Ordinary exit time as the Green occupation of the constant function. -/

namespace MatedCRT

open MeasureTheory
open scoped ENNReal

/-- On a finite killed domain, the Green occupation of one is the ordinary
expected exit time, whenever that expectation is finite. -/
theorem sum_greenFn_eq_expectedExitTime_toReal (m : ℤ → ℤ → ℕ)
    (A : Set ℤ) (B : Finset ℤ) (hAB : A ⊆ B) (a : ℤ)
    (hmean : expectedExitTime m A a ≠ ⊤) :
    (∑ b ∈ B, greenFn m A a b) = (expectedExitTime m A a).toReal := by
  have h := sum_greenFn_mul_eq_integral_occupation_of_expectedExitTime_ne_top
    m A B hAB a (fun _ => 1) hmean
  simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  rw [h]
  unfold expectedExitTime
  rw [← MeasureTheory.integral_toReal]
  · apply integral_congr_ae
    filter_upwards [ae_vExitTime_ne_top_of_expectedExitTime_ne_top m A a hmean] with x hx
    rw [← ENat.natCast_toNat hx]
    simp
  · exact ((measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
      (measurable_vExitTime A)).aemeasurable
  · filter_upwards [ae_vExitTime_ne_top_of_expectedExitTime_ne_top m A a hmean] with x hx
    rw [← ENat.natCast_toNat hx]
    simp

end MatedCRT

#print axioms MatedCRT.sum_greenFn_eq_expectedExitTime_toReal
