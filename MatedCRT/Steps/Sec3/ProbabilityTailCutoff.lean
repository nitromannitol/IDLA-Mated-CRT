import MatedCRT.Steps.Sec3.BoundedMomentRates

/-! Extend a polynomial tail from a fixed cutoff to a bounded range. -/

open MeasureTheory Set

namespace MatedCRT

/-- Monotonicity extends a polynomial tail bound known only up to `T` to
all scales up to `R`, at the cost of the fixed factor `(R / T)^ν`. -/
theorem probability_tail_le_of_cutoff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    {ℓ T R ν C : ℝ} (hℓ : 0 < ℓ) (hℓT : ℓ < T) (hTR : T ≤ R)
    (hν : 0 ≤ ν) (hC : 0 ≤ C)
    (htail : ∀ s ∈ Ioc ℓ T, μ.real {ω | s < f ω} ≤ C * ℓ ^ ν * s ^ (-ν)) :
    ∀ s ∈ Ioo ℓ R, μ.real {ω | s < f ω} ≤
      (C * (R / T) ^ ν) * ℓ ^ ν * s ^ (-ν) := by
  intro s hs
  have hT : 0 < T := hℓ.trans hℓT
  have hs0 : 0 < s := hℓ.trans hs.1
  have hR : 0 < R := hT.trans_le hTR
  have htmin : min s T ∈ Ioc ℓ T := ⟨lt_min hs.1 hℓT, min_le_right _ _⟩
  have hmono : μ.real {ω | s < f ω} ≤ μ.real {ω | min s T < f ω} := by
    apply measureReal_mono
    · intro ω hω
      change s < f ω at hω
      change min s T < f ω
      exact lt_of_le_of_lt (min_le_left _ _) hω
    · exact measure_ne_top μ _
  have hm : 0 < min s T := lt_min hs0 hT
  have hratio : s / min s T ≤ R / T := by
    by_cases h : s ≤ T
    · rw [min_eq_left h, div_self hs0.ne']
      exact (one_le_div hT).2 hTR
    · rw [min_eq_right (le_of_not_ge h)]
      exact div_le_div_of_nonneg_right hs.2.le hT.le
  have hp := Real.rpow_le_rpow (div_nonneg hs0.le hm.le) hratio hν
  have heq : (s / min s T) ^ ν * s ^ (-ν) = (min s T) ^ (-ν) := by
    rw [Real.div_rpow hs0.le hm.le, Real.rpow_neg hs0.le,
      Real.rpow_neg hm.le]
    have hsne : s ^ ν ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hs0 ν)
    field_simp
  have hpow : (min s T) ^ (-ν) ≤ (R / T) ^ ν * s ^ (-ν) := by
    rw [← heq]
    exact mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hs0.le _)
  calc
    μ.real {ω | s < f ω} ≤ μ.real {ω | min s T < f ω} := hmono
    _ ≤ C * ℓ ^ ν * (min s T) ^ (-ν) := htail _ htmin
    _ ≤ C * ℓ ^ ν * ((R / T) ^ ν * s ^ (-ν)) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hC (Real.rpow_nonneg hℓ.le _))
    _ = (C * (R / T) ^ ν) * ℓ ^ ν * s ^ (-ν) := by ring

end MatedCRT

#print axioms MatedCRT.probability_tail_le_of_cutoff
