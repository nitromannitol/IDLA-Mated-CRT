import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.MesoscopicCutoff

/-! Mesh-scale bounds for the mean-discrepancy cutoff. -/

namespace MatedCRT

/-- Every nonnegative power of the microscopic cutoff is bounded by the
corresponding power of the mesh at the smaller of the two exponents. -/
theorem mesoscopic_mean_cutoff_rpow_le {ε a b t : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    (2 * (100 * ε ^ a + ε ^ b)) ^ t ≤
      (202 : ℝ) ^ t * ε ^ (min a b * t) := by
  have hcut := (mesoscopic_cutoff_bounds (a := a) (b := b) hε hε1).2.2.2
  have hleft : 0 ≤ 2 * (100 * ε ^ a + ε ^ b) := by positivity
  have hbound : 2 * (100 * ε ^ a + ε ^ b) ≤ 202 * ε ^ min a b := by linarith
  calc
    _ ≤ (202 * ε ^ min a b) ^ t := Real.rpow_le_rpow hleft hbound ht
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 202) (Real.rpow_nonneg hε.le _),
        Real.rpow_mul hε.le]

/-- The logarithm in the critical moment regime grows at most linearly in
`|log ε|`, with a constant depending on the disk and cutoff exponents. -/
theorem mesoscopic_mean_cutoff_log_le {ε a b r : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hr : 0 < r) :
    Real.log (r / (2 * (100 * ε ^ a + ε ^ b))) ≤
      |Real.log r| + |min a b| * |Real.log ε| := by
  have hmin := (mesoscopic_cutoff_bounds (a := a) (b := b) hε hε1).2.2.1
  have hp : 0 < ε ^ min a b := Real.rpow_pos_of_pos hε _
  have hcut : 0 < 2 * (100 * ε ^ a + ε ^ b) := by positivity
  have hle : ε ^ min a b ≤ 2 * (100 * ε ^ a + ε ^ b) := by linarith
  have hlog := Real.log_le_log hp hle
  rw [Real.log_rpow hε] at hlog
  rw [Real.log_div (ne_of_gt hr) (ne_of_gt hcut)]
  have h₁ := le_abs_self (Real.log r)
  have h₂ := neg_le_abs (min a b * Real.log ε)
  rw [abs_mul] at h₂
  linarith

end MatedCRT

#print axioms MatedCRT.mesoscopic_mean_cutoff_rpow_le
#print axioms MatedCRT.mesoscopic_mean_cutoff_log_le
