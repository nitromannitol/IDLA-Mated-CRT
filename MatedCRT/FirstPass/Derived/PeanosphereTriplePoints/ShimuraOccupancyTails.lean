import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraOccupancyPaths
import LatticeProb.Prob.BrownianLevyReflection
import LatticeProb.Prob.CorrelatedBMRationalDescent
import LatticeProb.Analysis.CorrelatedBMHolder
import LatticeProb.Gauss.TailMills

/-!
# Tails of the drops over a cell

For a real Brownian motion `B` and `a ≥ 0`, the probability that `B s - B 0` exceeds `a` at some time
`s ≤ T` is at most `2 exp (-a² / (2 T))` (`measure_exists_gt_le_two_mul_exp`): Lévy's reflection
inequality bounds it by twice the probability that `B T - B 0 ≥ a`, and Chernoff's bound for the
centred Gaussian law of `B T - B 0` bounds that by `exp (-a² / (2 T))`.

For the `γ`-correlated pair, reading either coordinate backwards from `k/n` gives a Brownian
motion, so the drop `x < Y (k/n) - Y s` over the cell `[(k - 1)/n, k/n]` has probability at most
`2 exp (-n x² / 2)` (`measure_drop_le`). With `x = √((j - 1)/n)` and `1 + 6 log n < j` the two
coordinates together have probability at most `4 / n ^ 3` (`measure_tails_le`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MatedCRT.PeanosphereTriplePoints

open MatedCRTHarmonic.MatedCRT (Path2 IsCorrelatedBM2 lrCoord)
open LatticeProb.CorrelatedBM (reversedCoordinate reversedCoordinate_isBrownianReal
  measurable_lrCoord_path)

/-- The running maximum of a Brownian motion has a sub-Gaussian tail. -/
theorem measure_exists_gt_le_two_mul_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {T : ℝ≥0} (hT : 0 < T) {a : ℝ} (ha : 0 ≤ a) :
    P {ω | ∃ s ≤ T, a < B s ω - B 0 ω} ≤ ENNReal.ofReal (2 * Real.exp (-(a ^ 2 / (2 * T)))) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have h1 := LatticeProb.measure_exists_lt_le_two_mul hB hm T a
  have hint : Integrable (fun ω => Real.exp ((a / T) * (B T ω - B 0 ω))) P :=
    LatticeProb.brownian_integrable_exp_mul_sub hB.toIsPreBrownianReal (a / T) 0 T
  have hch := measure_ge_le_exp_mul_mgf (μ := P) (X := fun ω => B T ω - B 0 ω) a
    (div_nonneg ha hTr.le) hint
  have hmgf : mgf (fun ω => B T ω - B 0 ω) P (a / T) = Real.exp (T * (a / T) ^ 2 / 2) := by
    have := LatticeProb.brownian_integral_exp_mul_sub hB.toIsPreBrownianReal (a / T) (zero_le T)
    simpa [mgf] using this
  have hexp : Real.exp (-(a / T) * a) * Real.exp (T * (a / T) ^ 2 / 2) =
      Real.exp (-(a ^ 2 / (2 * T))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hmgf, hexp] at hch
  have h2 : P {ω | a ≤ B T ω - B 0 ω} ≤ ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * T)))) := by
    calc P {ω | a ≤ B T ω - B 0 ω} = ENNReal.ofReal (P.real {ω | a ≤ B T ω - B 0 ω}) :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hch
  calc P {ω | ∃ s ≤ T, a < B s ω - B 0 ω} ≤ 2 * P {ω | a ≤ B T ω - B 0 ω} := h1
    _ ≤ 2 * ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * T)))) := by gcongr
    _ = ENNReal.ofReal (2 * Real.exp (-(a ^ 2 / (2 * T)))) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        simp

/-- The drop of a correlated coordinate over a cell, read backwards from the right end of the cell,
has a sub-Gaussian tail. -/
theorem measure_drop_le {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2)
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    μ {p : Path2 | ∃ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n),
        x < lrCoord i ((k : ℝ) / n) p - lrCoord i s p} ≤
      ENNReal.ofReal (2 * Real.exp (-((n : ℝ) * x ^ 2 / 2))) := by
  have := hμ.isProbabilityMeasure
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hT : (0 : ℝ≥0) < (n : ℝ≥0)⁻¹ := inv_pos.2 (by exact_mod_cast hn)
  have hTc : (((n : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) = 1 / n := by simp
  have hB := (reversedCoordinate_isBrownianReal hμ i ((k : ℝ) / n)).neg
  have hm : ∀ t : ℝ≥0, Measurable ((-reversedCoordinate i ((k : ℝ) / n)) t) := fun t =>
    ((measurable_lrCoord_path i (((k : ℝ) / n) - t)).sub
      (measurable_lrCoord_path i ((k : ℝ) / n))).neg
  have hmain := measure_exists_gt_le_two_mul_exp hB hm hT hx
  refine le_trans (measure_mono ?_) (hmain.trans (le_of_eq ?_))
  · rintro p ⟨s, hs, hlt⟩
    obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (t : ℝ) = (k : ℝ) / n - s :=
      ⟨Real.toNNReal ((k : ℝ) / n - s), Real.coe_toNNReal _ (by linarith [hs.2])⟩
    refine ⟨t, ?_, ?_⟩
    · rw [← NNReal.coe_le_coe, hTc, ht]
      have : ((k : ℝ) - 1) / n = (k : ℝ) / n - 1 / n := by ring
      linarith [hs.1]
    · have hts : (k : ℝ) / n - (t : ℝ) = s := by rw [ht]; ring
      have e : (-reversedCoordinate i ((k : ℝ) / n)) t p -
          (-reversedCoordinate i ((k : ℝ) / n)) 0 p =
          lrCoord i ((k : ℝ) / n) p - lrCoord i s p := by
        simp only [Pi.neg_apply, reversedCoordinate, NNReal.coe_zero, sub_zero, hts]
        ring
      rw [e]
      exact hlt
  · rw [hTc]
    congr 2
    field_simp

theorem measure_drop_snd_le {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {n : ℕ}
    (hn : 1 ≤ n) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    μ {p : Path2 | ∃ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n),
        x < (p ((k : ℝ) / n)).2 - (p s).2} ≤
      ENNReal.ofReal (2 * Real.exp (-((n : ℝ) * x ^ 2 / 2))) := by
  simpa [lrCoord] using measure_drop_le hμ 1 hn k hx

theorem measure_drop_fst_le {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {n : ℕ}
    (hn : 1 ≤ n) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    μ {p : Path2 | ∃ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n),
        x < (p ((k : ℝ) / n)).1 - (p s).1} ≤
      ENNReal.ofReal (2 * Real.exp (-((n : ℝ) * x ^ 2 / 2))) := by
  simpa [lrCoord] using measure_drop_le hμ 0 hn k hx

/-- For `1 + 6 log n < j` and `d = (j - 1)/n`, both coordinate drops over a cell exceed `√d` with total
probability at most `4 / n ^ 3`. -/
theorem measure_tails_le {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {n : ℕ}
    (hn : 1 ≤ n) (k : ℕ) {j : ℕ} (hj : 1 + 6 * Real.log n < j) :
    μ {p : Path2 | ∃ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n),
        Real.sqrt (((j : ℝ) - 1) / n) < (p ((k : ℝ) / n)).2 - (p s).2} +
      μ {p : Path2 | ∃ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n),
        Real.sqrt (((j : ℝ) - 1) / n) < (p ((k : ℝ) / n)).1 - (p s).1} ≤
      ENNReal.ofReal (4 / (n : ℝ) ^ 3) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hj1 : (0 : ℝ) ≤ (j : ℝ) - 1 := by linarith
  have hd : 0 ≤ ((j : ℝ) - 1) / n := div_nonneg hj1 hnR.le
  have hsq : (Real.sqrt (((j : ℝ) - 1) / n)) ^ 2 = ((j : ℝ) - 1) / n := Real.sq_sqrt hd
  have hexp3 : Real.exp (3 * Real.log n) = (n : ℝ) ^ 3 := by
    rw [show 3 * Real.log n = ((3 : ℕ) : ℝ) * Real.log n by norm_num, Real.exp_nat_mul,
      Real.exp_log hnR]
  have hbound : 2 * Real.exp (-((n : ℝ) * (Real.sqrt (((j : ℝ) - 1) / n)) ^ 2 / 2)) ≤
      2 / (n : ℝ) ^ 3 := by
    rw [hsq]
    have h1 : (n : ℝ) * (((j : ℝ) - 1) / n) / 2 = ((j : ℝ) - 1) / 2 := by
      field_simp
    rw [h1]
    have h2 : Real.exp (-(((j : ℝ) - 1) / 2)) ≤ Real.exp (-(3 * Real.log n)) :=
      Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_neg, hexp3] at h2
    calc 2 * Real.exp (-(((j : ℝ) - 1) / 2)) ≤ 2 * ((n : ℝ) ^ 3)⁻¹ := by linarith
      _ = 2 / (n : ℝ) ^ 3 := by rw [div_eq_mul_inv]
  have h2R := (measure_drop_snd_le hμ hn k (Real.sqrt_nonneg (((j : ℝ) - 1) / n))).trans
    (ENNReal.ofReal_le_ofReal hbound)
  have h2L := (measure_drop_fst_le hμ hn k (Real.sqrt_nonneg (((j : ℝ) - 1) / n))).trans
    (ENNReal.ofReal_le_ofReal hbound)
  calc _ ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 3) + ENNReal.ofReal (2 / (n : ℝ) ^ 3) :=
        add_le_add h2R h2L
    _ = ENNReal.ofReal (4 / (n : ℝ) ^ 3) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end MatedCRT.PeanosphereTriplePoints
