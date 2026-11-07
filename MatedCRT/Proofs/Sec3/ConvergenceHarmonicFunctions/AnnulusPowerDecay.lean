import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.MesoscopicCutoff

/-! # Polynomial decay from dyadic annulus iteration -/

namespace MatedCRT

/-- A strictly subunit survival probability is a positive real power of the
dyadic scale ratio. -/
theorem exists_dyadic_survival_exponent {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ n : ℕ, q ^ n = (((1 / 2 : ℝ) ^ n) : ℝ) ^ ν := by
  let ν := Real.log q / Real.log (1 / 2 : ℝ)
  have hlogq : Real.log q < 0 := Real.log_neg hq hq1
  have hloghalf : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hν : 0 < ν := div_pos_of_neg_of_neg hlogq hloghalf
  have hbase : (1 / 2 : ℝ) ^ ν = q := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have heq : Real.log (1 / 2 : ℝ) * ν = Real.log q := by
      dsimp [ν]
      field_simp
    rw [heq, Real.exp_log hq]
  refine ⟨ν, hν, ?_⟩
  intro n
  calc
    q ^ n = ((1 / 2 : ℝ) ^ ν) ^ n := by rw [hbase]
    _ = ((1 / 2 : ℝ) ^ n) ^ ν := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_comm,
        Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- If the outer excursion radius is at most a constant times the dyadic
radius of stage `n`, the geometric survival estimate is bounded by a
positive power of the cutoff-to-excursion ratio. -/
theorem dyadic_survival_le_power_ratio {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ (n : ℕ) (cutoff distance factor : ℝ),
      0 ≤ cutoff → 0 < distance → 0 ≤ factor →
      distance ≤ factor * cutoff * (2 : ℝ) ^ n →
      q ^ n ≤ (factor * cutoff / distance) ^ ν := by
  obtain ⟨ν, hν, hpow⟩ := exists_dyadic_survival_exponent hq hq1
  refine ⟨ν, hν, ?_⟩
  intro n cutoff distance factor hcut hdist hfactor hscale
  have hhalf : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  have hcancel : (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hratio : (1 / 2 : ℝ) ^ n ≤ factor * cutoff / distance := by
    apply (le_div_iff₀ hdist).2
    calc
      (1 / 2 : ℝ) ^ n * distance ≤
          (1 / 2 : ℝ) ^ n * (factor * cutoff * (2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hscale hhalf
      _ = factor * cutoff := by rw [show (1 / 2 : ℝ) ^ n * (factor * cutoff * (2 : ℝ) ^ n) =
          ((1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n) * (factor * cutoff) by ring, hcancel, one_mul]
  rw [hpow n]
  exact Real.rpow_le_rpow hhalf hratio hν.le

end MatedCRT
