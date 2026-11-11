import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.MesoscopicCutoff

/-! # Polynomial decay from dyadic annulus iteration -/

namespace MatedCRT

open scoped ENNReal

/-- At excursion distances at least four times the cutoff, one can choose
the largest dyadic annulus whose outer boundary lies within half the
excursion distance. -/
theorem exists_dyadic_annulus_stage {cutoff distance : ℝ}
    (hcutoff : 0 < cutoff) (hdistance : 4 * cutoff ≤ distance) :
    ∃ n : ℕ, 4 * cutoff * (2 : ℝ) ^ n ≤ distance ∧
      distance < 4 * cutoff * (2 : ℝ) ^ (n + 1) := by
  have hdenom : 0 < 4 * cutoff := by positivity
  have hratio : 1 ≤ distance / (4 * cutoff) := (one_le_div hdenom).2 hdistance
  obtain ⟨n, hn, hnnext⟩ := exists_nat_pow_near hratio (show (1 : ℝ) < 2 by norm_num)
  refine ⟨n, ?_, ?_⟩
  · have h := (le_div_iff₀ hdenom).1 hn
    nlinarith
  · have h := (div_lt_iff₀ hdenom).1 hnnext
    nlinarith

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

/-- The same estimate for the extended nonnegative probabilities used by
the random-walk crossing iteration. -/
theorem dyadic_crossing_probability_le_power_ratio {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ (n : ℕ) (probability : ℝ≥0∞) (cutoff distance factor : ℝ),
      0 ≤ cutoff → 0 < distance → 0 ≤ factor →
      distance ≤ factor * cutoff * (2 : ℝ) ^ n →
      probability ≤ ENNReal.ofReal q ^ n →
      probability ≤ ENNReal.ofReal ((factor * cutoff / distance) ^ ν) := by
  obtain ⟨ν, hν, hbound⟩ := dyadic_survival_le_power_ratio hq hq1
  refine ⟨ν, hν, ?_⟩
  intro n probability cutoff distance factor hcut hdist hfactor hscale hprob
  calc
    probability ≤ ENNReal.ofReal q ^ n := hprob
    _ = ENNReal.ofReal (q ^ n) := (ENNReal.ofReal_pow hq.le n).symm
    _ ≤ ENNReal.ofReal ((factor * cutoff / distance) ^ ν) :=
      ENNReal.ofReal_le_ofReal (hbound n cutoff distance factor hcut hdist hfactor hscale)

/-- The largest admissible annulus has a polynomial survival bound, with an
exponent chosen independently of the cutoff and excursion distance. -/
theorem exists_annulus_stage_with_power_bound {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ cutoff distance : ℝ, 0 < cutoff → 4 * cutoff ≤ distance →
      ∃ n : ℕ, 4 * cutoff * (2 : ℝ) ^ n ≤ distance ∧
        distance < 4 * cutoff * (2 : ℝ) ^ (n + 1) ∧
        ∀ probability : ℝ≥0∞, probability ≤ ENNReal.ofReal q ^ (n + 1) →
          probability ≤ ENNReal.ofReal ((4 * cutoff / distance) ^ ν) := by
  obtain ⟨ν, hν, hbound⟩ := dyadic_crossing_probability_le_power_ratio hq hq1
  refine ⟨ν, hν, ?_⟩
  intro cutoff distance hcut hdist
  obtain ⟨n, hn, hnnext⟩ := exists_dyadic_annulus_stage hcut hdist
  refine ⟨n, hn, hnnext, ?_⟩
  intro probability hprob
  have hdistpos : 0 < distance := lt_of_lt_of_le (by positivity) hdist
  exact hbound (n + 1) probability cutoff distance 4 hcut.le hdistpos (by norm_num)
    hnnext.le hprob

end MatedCRT
