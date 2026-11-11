import Mathlib

/-!
# Exponents of the preparation

, "Lemma 2 (simultaneous preparation)", eq (7): given `b_* < β⁻` with `b_* > 0`, choose
`b_* < b < min{β⁻, b_* + 1}` and `2 < p < min{3, 2β⁻/b}`. These choices give `p b < 2 β⁻` (the mass of a good ball of
radius `r^p` is `≥ r^{pb}`, which must dominate `r^{2β⁻}`) and `p/2 > 1` (the radii `r^{p/2}` are `o(r)`).
The statement is pure real arithmetic; it is the input to the exponent facts used by Lemma 2 and Lemma 3.
-/

namespace MatedCRT

/-- **Exponents of Lemma 2**: there are `b, p` with `b_* < b < min{β⁻, b_* + 1}`,
`2 < p < min{3, 2β⁻/b}`, and `p b < 2 β⁻`. -/
theorem exists_lemma2_exponents {bstar βm : ℝ} (hb0 : 0 < bstar) (h : bstar < βm) :
    ∃ b p : ℝ, 0 < b ∧ bstar < b ∧ b < min βm (bstar + 1) ∧ 2 < p ∧ p < min 3 (2 * βm / b) ∧
      p * b < 2 * βm := by
  obtain ⟨b, hb1, hb2⟩ : ∃ b : ℝ, bstar < b ∧ b < min βm (bstar + 1) :=
    exists_between (lt_min h (by linarith))
  have hbβ : b < βm := lt_of_lt_of_le hb2 (min_le_left _ _)
  have hbpos : 0 < b := by linarith
  have hq : 2 < 2 * βm / b := by
    rw [lt_div_iff₀ hbpos]
    linarith
  obtain ⟨p, hp1, hp2⟩ : ∃ p : ℝ, 2 < p ∧ p < min 3 (2 * βm / b) :=
    exists_between (lt_min (by norm_num) hq)
  refine ⟨b, p, hbpos, hb1, hb2, hp1, hp2, ?_⟩
  exact (lt_div_iff₀ hbpos).1 (lt_of_lt_of_le hp2 (min_le_right _ _))

end MatedCRT
