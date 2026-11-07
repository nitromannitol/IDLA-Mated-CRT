import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Mesoscopic cutoff for boundary excursions -/

namespace MatedCRT

/-- The boundary-excursion cutoff in `LEMMA36-REPLACEMENT.md`, equation
`exponents`: the first annulus radius is at least the permitted annulus
scale, is strictly more than one hundred cell diameters, and is comparable
to `ε` raised to the smaller exponent. -/
theorem mesoscopic_cutoff_bounds {ε a b : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let d := ε ^ a
    let ℓ := 100 * d + ε ^ b
    ε ^ b ≤ ℓ ∧ d < ℓ / 100 ∧
      ε ^ min a b ≤ ℓ ∧ ℓ ≤ 101 * ε ^ min a b := by
  dsimp only
  have ha : 0 < ε ^ a := Real.rpow_pos_of_pos hε _
  have hb : 0 < ε ^ b := Real.rpow_pos_of_pos hε _
  have hamin : ε ^ a ≤ ε ^ min a b :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_left _ _)
  have hbmin : ε ^ b ≤ ε ^ min a b :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_right _ _)
  refine ⟨by linarith, by linarith, ?_, by linarith⟩
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    linarith
  · rw [min_eq_right hba]
    linarith

end MatedCRT
