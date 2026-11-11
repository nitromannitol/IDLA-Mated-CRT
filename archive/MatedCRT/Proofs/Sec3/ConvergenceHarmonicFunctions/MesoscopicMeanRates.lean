import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.MesoscopicMeanScale

/-! Mesh exponents in the Hölder mean-discrepancy regimes. -/

namespace MatedCRT

/-- Below the tail exponent, the cutoff mean bound has mesh exponent
`min a b * χ`. -/
theorem mesoscopic_mean_lt_rate {ε a b χ ν K : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hχ : 0 < χ) (hχν : χ < ν) (hK : 0 ≤ K) :
    let ℓ := 2 * (100 * ε ^ a + ε ^ b)
    ℓ ^ χ + χ * K * (ℓ ^ χ / (ν - χ)) ≤
      ((202 : ℝ) ^ χ * (1 + χ * K / (ν - χ))) * ε ^ (min a b * χ) := by
  dsimp only
  have hp := mesoscopic_mean_cutoff_rpow_le (a := a) (b := b) hε hε1 hχ.le
  have hc : 0 ≤ 1 + χ * K / (ν - χ) := by positivity
  have h := mul_le_mul_of_nonneg_left hp hc
  calc
    _ = (1 + χ * K / (ν - χ)) * (2 * (100 * ε ^ a + ε ^ b)) ^ χ := by ring
    _ ≤ (1 + χ * K / (ν - χ)) * ((202 : ℝ) ^ χ * ε ^ (min a b * χ)) := h
    _ = _ := by ring

/-- Above the tail exponent, the cutoff mean bound has mesh exponent
`min a b * ν`. -/
theorem mesoscopic_mean_gt_rate {ε a b χ ν K r : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : 0 ≤ min a b)
    (hν : 0 < ν) (hνχ : ν < χ) (hK : 0 ≤ K) (hr : 0 < r) :
    let ℓ := 2 * (100 * ε ^ a + ε ^ b)
    ℓ ^ χ + χ * K * (ℓ ^ ν * r ^ (χ - ν) / (χ - ν)) ≤
      ((202 : ℝ) ^ χ + χ * K * (202 : ℝ) ^ ν * r ^ (χ - ν) / (χ - ν)) *
        ε ^ (min a b * ν) := by
  dsimp only
  have hχ : 0 < χ := hν.trans hνχ
  have hpχ := mesoscopic_mean_cutoff_rpow_le (a := a) (b := b) hε hε1 hχ.le
  have hpν := mesoscopic_mean_cutoff_rpow_le (a := a) (b := b) hε hε1 hν.le
  have hcmp : ε ^ (min a b * χ) ≤ ε ^ (min a b * ν) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (mul_le_mul_of_nonneg_left hνχ.le hm)
  have hfirst := hpχ.trans (mul_le_mul_of_nonneg_left hcmp (Real.rpow_nonneg (by norm_num) _))
  have hc : 0 ≤ χ * K * r ^ (χ - ν) / (χ - ν) := by positivity
  have hsecond := mul_le_mul_of_nonneg_left hpν hc
  calc
    _ = (2 * (100 * ε ^ a + ε ^ b)) ^ χ +
      (χ * K * r ^ (χ - ν) / (χ - ν)) * (2 * (100 * ε ^ a + ε ^ b)) ^ ν := by ring
    _ ≤ (202 : ℝ) ^ χ * ε ^ (min a b * ν) +
      (χ * K * r ^ (χ - ν) / (χ - ν)) * ((202 : ℝ) ^ ν * ε ^ (min a b * ν)) :=
        add_le_add hfirst hsecond
    _ = _ := by ring

/-- At the tail exponent, the cutoff mean bound has the same mesh exponent
with an additional logarithmic factor. -/
theorem mesoscopic_mean_eq_rate {ε a b ν K r : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hν : 0 < ν) (hK : 0 ≤ K) (hr : 0 < r)
    (hℓr : 2 * (100 * ε ^ a + ε ^ b) ≤ r) :
    let ℓ := 2 * (100 * ε ^ a + ε ^ b)
    ℓ ^ ν + ν * K * (ℓ ^ ν * Real.log (r / ℓ)) ≤
      ((202 : ℝ) ^ ν * (1 + ν * K * (|Real.log r| + |min a b|))) *
        ε ^ (min a b * ν) * (1 + |Real.log ε|) := by
  dsimp only
  let ℓ : ℝ := 2 * (100 * ε ^ a + ε ^ b)
  let M : ℝ := |Real.log r| + |min a b|
  let L : ℝ := |Real.log ε|
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hL : 0 ≤ L := abs_nonneg _
  have hlog0 : 0 ≤ Real.log (r / ℓ) :=
    Real.log_nonneg ((one_le_div hℓ).2 hℓr)
  have hlog := mesoscopic_mean_cutoff_log_le (a := a) (b := b) hε hε1 hr
  have hlog' : Real.log (r / ℓ) ≤ M * (1 + L) := by
    dsimp [ℓ, M, L] at *
    nlinarith [abs_nonneg (Real.log r), abs_nonneg (min a b), abs_nonneg (Real.log ε),
      mul_nonneg (abs_nonneg (Real.log r)) (abs_nonneg (Real.log ε))]
  have hfac : 1 + ν * K * Real.log (r / ℓ) ≤ (1 + ν * K * M) * (1 + L) := by
    have hmul := mul_le_mul_of_nonneg_left hlog' (mul_nonneg hν.le hK)
    have hn : 0 ≤ ν * K * L := by positivity
    nlinarith
  have hfac0 : 0 ≤ 1 + ν * K * Real.log (r / ℓ) := by positivity
  have hp := mesoscopic_mean_cutoff_rpow_le (a := a) (b := b) hε hε1 hν.le
  have hmul := mul_le_mul hp hfac hfac0 (by positivity : 0 ≤ (202 : ℝ) ^ ν * ε ^ (min a b * ν))
  calc
    _ = ℓ ^ ν * (1 + ν * K * Real.log (r / ℓ)) := by dsimp [ℓ]; ring
    _ ≤ ((202 : ℝ) ^ ν * ε ^ (min a b * ν)) * ((1 + ν * K * M) * (1 + L)) := hmul
    _ = _ := by dsimp [M, L]; ring

end MatedCRT

#print axioms MatedCRT.mesoscopic_mean_lt_rate
#print axioms MatedCRT.mesoscopic_mean_gt_rate
#print axioms MatedCRT.mesoscopic_mean_eq_rate
