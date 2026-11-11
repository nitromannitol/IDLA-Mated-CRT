import Mathlib

/-!
# Convergence in probability from `L¹` and `L²` convergence

Markov's inequality for `|Y_n|` and for `Y_n²` turns `∫|Y_n| → 0` and `∫Y_n² → 0` into `Y_n → 0` in probability.
These are the transfer steps of the H1 assembly (`tendstoInMeasure` of the pairing and of the lateral integral).
-/

open MeasureTheory Filter Topology Set

namespace MatedCRT.LQGMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Convergence in probability to `0` from `∫|Y_n| → 0`. -/
lemma tendstoInMeasure_zero_of_integral_abs {Y : ℕ → Ω → ℝ} (hYi : ∀ n, Integrable (Y n) P)
    (h : Tendsto (fun n => ∫ ω, |Y n ω| ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P Y atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hbd : ∀ n, (P {x | ε ≤ dist (Y n x) 0}).toReal ≤ (∫ ω, |Y n ω| ∂P) / ε := by
    intro n
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => |Y n ω|)
      (Eventually.of_forall fun ω => abs_nonneg _) (hYi n).abs ε
    have hset : {x | ε ≤ dist (Y n x) 0} = {x | ε ≤ |Y n x|} := by
      ext x; simp
    rw [hset, le_div_iff₀ hε, mul_comm]
    exact hm
  have hT : Tendsto (fun n => (P {x | ε ≤ dist (Y n x) 0}).toReal) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => ENNReal.toReal_nonneg) hbd ?_
    simpa using h.div_const ε
  have hT' : Tendsto (fun n => P {x | ε ≤ dist (Y n x) 0}) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top P _) ENNReal.zero_ne_top).1
      (by rw [ENNReal.toReal_zero]; exact hT)
  exact hT'

/-- Convergence in probability to `0` from `∫Y_n² → 0`. -/
lemma tendstoInMeasure_zero_of_integral_sq {Y : ℕ → Ω → ℝ} (hYi : ∀ n, Integrable (fun ω => Y n ω ^ 2) P)
    (h : Tendsto (fun n => ∫ ω, Y n ω ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P Y atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hbd : ∀ n, (P {x | ε ≤ dist (Y n x) 0}).toReal ≤ (∫ ω, Y n ω ^ 2 ∂P) / ε ^ 2 := by
    intro n
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => Y n ω ^ 2)
      (Eventually.of_forall fun ω => sq_nonneg _) (hYi n) (ε ^ 2)
    have hset : {x | ε ≤ dist (Y n x) 0} ⊆ {x | ε ^ 2 ≤ Y n x ^ 2} := by
      intro x hx
      have hx' : ε ≤ |Y n x| := by simpa [Real.dist_eq] using hx
      show ε ^ 2 ≤ Y n x ^ 2
      rw [← sq_abs (Y n x)]
      exact pow_le_pow_left₀ hε.le hx' 2
    have hle : (P {x | ε ≤ dist (Y n x) 0}).toReal ≤ (P {x | ε ^ 2 ≤ Y n x ^ 2}).toReal :=
      ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hset)
    have hpos : 0 < ε ^ 2 := pow_pos hε 2
    rw [le_div_iff₀ hpos]
    calc (P {x | ε ≤ dist (Y n x) 0}).toReal * ε ^ 2 ≤ (P {x | ε ^ 2 ≤ Y n x ^ 2}).toReal * ε ^ 2 :=
          mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      _ = ε ^ 2 * (P {x | ε ^ 2 ≤ Y n x ^ 2}).toReal := mul_comm _ _
      _ ≤ ∫ ω, Y n ω ^ 2 ∂P := hm
  have hT : Tendsto (fun n => (P {x | ε ≤ dist (Y n x) 0}).toReal) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => ENNReal.toReal_nonneg) hbd ?_
    simpa using h.div_const (ε ^ 2)
  have hT' : Tendsto (fun n => P {x | ε ≤ dist (Y n x) 0}) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top P _) ENNReal.zero_ne_top).1 (by simpa using hT)
  exact hT'

end MatedCRT.LQGMeasure
