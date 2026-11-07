import MatedCRT.Draft.Section3HarmonicCorrected

/-! # Exponents in the corrected stopping-location comparison -/

namespace MatedCRT

/-- The full range in the replacement proof, lines 377–386, can be obtained
by choosing the cell-size exponent strictly below its upper endpoint. -/
theorem exists_cell_exponent_for_sameWalk_rate {γ bAnn χ q : ℝ}
    (hγ : 0 < γ) (hχ : 0 < χ) (hq : 0 < q)
    (hqmax : q < χ * min (2 / (2 + γ) ^ (2 : ℕ)) bAnn) :
    ∃ a : ℝ, 0 < a ∧ a < 2 / (2 + γ) ^ (2 : ℕ) ∧
      q < min a bAnn * χ := by
  have hu : 0 < 2 / (2 + γ) ^ (2 : ℕ) := by positivity
  have hqa : q / χ < 2 / (2 + γ) ^ (2 : ℕ) := by
    apply (div_lt_iff₀ hχ).2
    have := lt_of_lt_of_le hqmax (mul_le_mul_of_nonneg_left (min_le_left _ _) hχ.le)
    nlinarith
  have hqb : q / χ < bAnn := by
    apply (div_lt_iff₀ hχ).2
    have := lt_of_lt_of_le hqmax (mul_le_mul_of_nonneg_left (min_le_right _ _) hχ.le)
    nlinarith
  refine ⟨(q / χ + 2 / (2 + γ) ^ (2 : ℕ)) / 2, ?_, ?_, ?_⟩
  · positivity
  · linarith
  · have hm : q / χ < min ((q / χ + 2 / (2 + γ) ^ (2 : ℕ)) / 2) bAnn :=
      lt_min (by linarith) hqb
    exact (div_lt_iff₀ hχ).1 hm

end MatedCRT
