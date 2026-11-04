import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.QualitativeRadius

/-! Qualitative control of the initial shell radius from the odometer. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set

/-- Convergence in probability of the rescaled initial odometer to zero
implies the same for any positive power of its shell-radius scale. -/
theorem probTendsToOne_initialRadius_of_rescaled_odometer
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (O : ℝ → Ω → ℝ) (K α : ℝ) (hK : 0 ≤ K) (hα : 0 < α)
    (G : ℝ → Set Ω) (hG : ProbTendsToOne P G)
    (hnonneg : ∀ ε ω, ω ∈ G ε → 0 ≤ O ε ω)
    (hsmall : ∀ a : ℝ, 0 < a → ProbTendsToOne P (fun ε => {ω | ε * O ε ω ≤ a})) :
    ∀ a : ℝ, 0 < a → ProbTendsToOne P (fun ε => {ω | (O ε ω * (ε * K)) ^ α ≤ a}) := by
  intro a ha
  let b := a ^ (1 / α) / (K + 1)
  have hb : 0 < b := by dsimp [b]; positivity
  apply (hG.inter (hsmall b hb)).mono_ev
  filter_upwards [self_mem_nhdsWithin] with ε hε ω hω
  have hO := hnonneg ε ω hω.1
  have hbase : O ε ω * (ε * K) ≤ a ^ (1 / α) := by
    have hm := mul_le_mul_of_nonneg_right hω.2 hK
    have hbK : b * K ≤ b * (K + 1) := by nlinarith [hb.le]
    have hcancel : b * (K + 1) = a ^ (1 / α) := by
      dsimp [b]
      exact div_mul_cancel₀ _ (by linarith : K + 1 ≠ 0)
    calc
      O ε ω * (ε * K) = (ε * O ε ω) * K := by ring
      _ ≤ b * K := hm
      _ ≤ b * (K + 1) := hbK
      _ = a ^ (1 / α) := hcancel
  have hpow := Real.rpow_le_rpow (mul_nonneg hO (mul_nonneg hε.le hK)) hbase hα.le
  have heq : (a ^ (1 / α)) ^ α = a := by
    rw [← Real.rpow_mul ha.le, one_div_mul_cancel (ne_of_gt hα), Real.rpow_one]
  change (O ε ω * (ε * K)) ^ α ≤ a
  simpa only [heq] using hpow

end MatedCRT.Sec7
