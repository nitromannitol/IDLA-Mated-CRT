import MatedCRT.Defs.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Intersections of polynomially likely environment events. -/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

/-- Two polynomial exceptional-set bounds combine at the smaller exponent. -/
theorem measure_compl_inter_le_polynomial {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (E F : Set Ω) {ε p q C D : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : P Eᶜ ≤ ENNReal.ofReal (C * ε ^ p))
    (hF : P Fᶜ ≤ ENNReal.ofReal (D * ε ^ q)) :
    P (E ∩ F)ᶜ ≤ ENNReal.ofReal ((C + D) * ε ^ min p q) := by
  have hp : ε ^ p ≤ ε ^ min p q :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_left p q)
  have hq : ε ^ q ≤ ε ^ min p q :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (min_le_right p q)
  have hCp : 0 ≤ C * ε ^ p := mul_nonneg hC (Real.rpow_nonneg hε.le _)
  have hDq : 0 ≤ D * ε ^ q := mul_nonneg hD (Real.rpow_nonneg hε.le _)
  calc
    _ = P (Eᶜ ∪ Fᶜ) := by rw [compl_inter]
    _ ≤ P Eᶜ + P Fᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C * ε ^ p) + ENNReal.ofReal (D * ε ^ q) := add_le_add hE hF
    _ = ENNReal.ofReal (C * ε ^ p + D * ε ^ q) := (ENNReal.ofReal_add hCp hDq).symm
    _ ≤ ENNReal.ofReal ((C + D) * ε ^ min p q) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left hp hC, mul_le_mul_of_nonneg_left hq hD]

end MatedCRT

#print axioms MatedCRT.measure_compl_inter_le_polynomial
