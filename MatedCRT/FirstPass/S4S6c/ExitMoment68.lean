import MatedCRT.FirstPass.S4S6c.TestBound68

/-!
# LEMMA68 second moment: the N = 2 exit-time bound as the `hmom` of `stayIn_le_log` (q2, task fp-S4S6c-envscaling-6-7-6-8)

Write-up B5 (notes/fp-gaps/CHATGPT-lemma68-open-parts.md, eqs (B15)-(B17)); printed Lemma 2.18 with `N = 2`
(Draft `ExitTimeUpperBoundStmt`, Draft/Section2.lean:239, BG20 Prop 5.1, EXTERNAL):
`E[τ²] ≤ 2! C² ε⁻² Sup²`, where `Sup` is the supremum over the centre of the log-potential integral over
`thickening (ε^α) D`. Here `τ = vExitTime W` for the window `W = I(D)` (Draft 2.18 uses `I(D)` itself as the window).

This file is pure ENNReal and real bookkeeping. Inputs are the pointwise instance `hexit` of Draft 2.18 at `N = 2`
and the potential bound `hS : Sup ≤ ofReal Sr` (eq (21) of Lemma 1, from `Lemma1Kernel.lean`, with the good-annulus
bound; not discharged here). Output: the `hmom` hypothesis of `TestBound68.stayIn_le_log`, with `C0` chosen so that
`C ≤ C0 (1 + log(1/r))`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT

/-- The square of a supremum bounded by `ofReal Sr` is bounded by `ofReal (Sr ^ 2)`. -/
theorem sq_le_ofReal_sq {S : ℝ≥0∞} {Sr : ℝ} (hSr : 0 ≤ Sr) (hS : S ≤ ENNReal.ofReal Sr) :
    S ^ 2 ≤ ENNReal.ofReal (Sr ^ 2) := by
  rw [ENNReal.ofReal_pow hSr]
  gcongr

/-- `ε ^ (-2) = (ε⁻¹) ^ 2` for the real power in the Draft exponent `ε ^ (-(N : ℝ))` at `N = 2`. -/
theorem rpow_neg_two_eq_inv_sq {ε : ℝ} (hε : 0 < ε) :
    ε ^ (-((2 : ℕ) : ℝ)) = ε⁻¹ ^ 2 := by
  rw [Nat.cast_ofNat, Real.rpow_neg hε.le, Real.rpow_two, inv_pow]

/-- **Second moment from the Draft exit-time bound** (write-up B5, eq (B17) with `C2 := 2 C² C1²` absorbed into `Sr`).
The `N = 2` instance of Draft Lemma 2.18 at the vertex `a` and window `W`, with the potential supremum `S` bounded by
`ofReal Sr`, gives the `hmom` bound of `TestBound68.stayIn_le_log`. -/
theorem hmom_of_exitTime_two {m : ℤ → ℤ → ℕ} {W : Set ℤ} {a : ℤ} {ε C C0 Sr r : ℝ} {S : ℝ≥0∞}
    (hε : 0 < ε) (hC : 0 ≤ C) (hSr : 0 ≤ Sr)
    (hCC : C ≤ C0 * (1 + Real.log (1 / r)))
    (hexit : exitTimeMoment m W a 2 ≤
      ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * C ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) * S ^ (2 : ℕ))
    (hS : S ≤ ENNReal.ofReal Sr) :
    ∫⁻ x, (ENat.toENNReal (vExitTime W x)) ^ 2 ∂(srwLaw m a) ≤
      ENNReal.ofReal (2 * (C0 * (1 + Real.log (1 / r))) ^ 2 * ε⁻¹ ^ 2 * Sr ^ 2) := by
  have hfac : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  have hA : 0 ≤ 2 * C ^ 2 * ε⁻¹ ^ 2 := by positivity
  have hK : ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * C ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) =
      ENNReal.ofReal (2 * C ^ 2 * ε⁻¹ ^ 2) := by
    rw [hfac, rpow_neg_two_eq_inv_sq hε]
  have hS2 : S ^ 2 ≤ ENNReal.ofReal (Sr ^ 2) := sq_le_ofReal_sq hSr hS
  have hCsq : C ^ 2 ≤ (C0 * (1 + Real.log (1 / r))) ^ 2 := by gcongr
  calc ∫⁻ x, (ENat.toENNReal (vExitTime W x)) ^ 2 ∂(srwLaw m a)
      = exitTimeMoment m W a 2 := rfl
    _ ≤ ENNReal.ofReal (2 * C ^ 2 * ε⁻¹ ^ 2) * S ^ 2 := by
        rw [hK] at hexit
        exact hexit
    _ ≤ ENNReal.ofReal (2 * C ^ 2 * ε⁻¹ ^ 2) * ENNReal.ofReal (Sr ^ 2) := by gcongr
    _ = ENNReal.ofReal (2 * C ^ 2 * ε⁻¹ ^ 2 * Sr ^ 2) := by
        rw [ENNReal.ofReal_mul hA]
    _ ≤ ENNReal.ofReal (2 * (C0 * (1 + Real.log (1 / r))) ^ 2 * ε⁻¹ ^ 2 * Sr ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        gcongr

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.hmom_of_exitTime_two
