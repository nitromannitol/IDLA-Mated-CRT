import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LogHorizon

/-! Polynomial scales give the logarithmic ratio needed for shell halving. -/

namespace MatedCRT.Sec7

/-- Polynomial bounds on the initial maximum and target, together with a
polynomial upper bound on the tested-radius floor, control their log ratio. -/
theorem log_initial_target_ratio_le_of_polynomial_bounds
    (ε a x B p b ω : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ha : 0 < a) (hω : 0 < ω) (haε : a ≤ ε ^ ω)
    (hx : 0 < x) (hB : 0 < B) (hxupper : x ≤ ε ^ (-p))
    (hBlower : ε ^ b ≤ B) (hpb : 0 ≤ p + b) :
    Real.log (x / B) ≤ ((p + b) / ω) * |Real.log a| := by
  have hεlog : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  have halog : Real.log a ≤ ω * Real.log ε := by
    have h := Real.log_le_log ha haε
    rwa [Real.log_rpow hε] at h
  have ha0 : Real.log a ≤ 0 := by nlinarith
  have hxlog : Real.log x ≤ -p * Real.log ε := by
    have h := Real.log_le_log hx hxupper
    rwa [Real.log_rpow hε] at h
  have hBlog : b * Real.log ε ≤ Real.log B := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hε b) hBlower
    rwa [Real.log_rpow hε] at h
  have hmult := mul_le_mul_of_nonneg_left halog hpb
  rw [Real.log_div hx.ne' hB.ne', abs_of_nonpos ha0]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hω).2
  nlinarith

/-- The polynomial estimate supplies the exact logarithmic ratio hypothesis
used to choose the number of shell-halving blocks. -/
theorem log_initial_target_ratio_le_halving_horizon
    (ε a x B p b ω : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ha : 0 < a) (hω : 0 < ω) (haε : a ≤ ε ^ ω)
    (hx : 0 < x) (hB : 0 < B) (hxupper : x ≤ ε ^ (-p))
    (hBlower : ε ^ b ≤ B) (hpb : 0 ≤ p + b) :
    Real.log (x / B) ≤
      ((p + b) / (ω * Real.log 2)) * (1 + |Real.log a|) * Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 ≤ (p + b) / ω := div_nonneg hpb hω.le
  calc
    Real.log (x / B) ≤ ((p + b) / ω) * |Real.log a| :=
      log_initial_target_ratio_le_of_polynomial_bounds ε a x B p b ω hε hε1 ha hω
        haε hx hB hxupper hBlower hpb
    _ ≤ ((p + b) / ω) * (1 + |Real.log a|) :=
      mul_le_mul_of_nonneg_left (by linarith) hc
    _ = ((p + b) / (ω * Real.log 2)) * (1 + |Real.log a|) * Real.log 2 := by
      field_simp

/-- Polynomial initial and target scales admit a cubic-log shell horizon whose
halving blocks reduce the initial maximum below the target. -/
theorem exists_polynomial_scale_halving_horizon
    (ε a x B p b ω s : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ha : 0 < a) (hω : 0 < ω) (haε : a ≤ ε ^ ω)
    (hx : 0 < x) (hB : 0 < B) (hxupper : x ≤ ε ^ (-p))
    (hBlower : ε ^ b ≤ B) (hpb : 0 ≤ p + b) (hs : 0 < s) :
    ∃ M N : ℕ,
      x * (1 / 2 : ℝ) ^ M ≤ B ∧
      2 * (1 + |Real.log a|) ^ 2 < (N : ℝ) * s ∧
      ((M * N : ℕ) : ℝ) ≤
        ((p + b) / (ω * Real.log 2) + 2) * (2 / s + 2) *
          (1 + |Real.log a|) ^ 3 := by
  let C := (p + b) / (ω * Real.log 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg hpb (mul_nonneg hω.le (Real.log_nonneg (by norm_num)))
  obtain ⟨M, N, hM, hN, hbound⟩ := exists_cubic_log_halving_horizon a s C hs hC
  have hratio : Real.log (x / B) ≤ C * (1 + |Real.log a|) * Real.log 2 :=
    log_initial_target_ratio_le_halving_horizon ε a x B p b ω hε hε1 ha hω
      haε hx hB hxupper hBlower hpb
  exact ⟨M, N, halving_blocks_reach_threshold x B (1 + |Real.log a|) C M hx hB
    hratio hM.le, hN, hbound⟩

end MatedCRT.Sec7
