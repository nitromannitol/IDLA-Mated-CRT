import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.DyadicChooseHorizon
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.LogRatio

/-! Polynomial scale bounds for the dyadic shell horizon. -/

namespace MatedCRT.Sec7

/-- Two-sided polynomial bounds control the absolute logarithm of a positive
scale uniformly by the absolute mesh logarithm. -/
theorem abs_log_le_of_two_sided_mesh_powers
    (ε x u v : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hx : 0 < x)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hlower : ε ^ u ≤ x) (hupper : x ≤ ε ^ (-v)) :
    |Real.log x| ≤ (u + v) * |Real.log ε| := by
  have he : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
  have hlo := Real.log_le_log (Real.rpow_pos_of_pos hε u) hlower
  have hhi := Real.log_le_log hx hupper
  rw [Real.log_rpow hε] at hlo hhi
  rw [abs_of_nonpos he]
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg hu (neg_nonneg.mpr he),
    mul_nonneg hv (neg_nonneg.mpr he)]

/-- The lower test-radius scale in a dyadic block has at most logarithmic
growth when the rescaled initial maximum has polynomial mesh bounds. -/
theorem dyadic_test_scale_log_le_of_mesh_powers
    (ε x u v α c : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hx : 0 < x)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hα : 0 ≤ α) (hc : 0 < c)
    (hlower : ε ^ u ≤ x) (hupper : x ≤ ε ^ (-v)) :
    1 + |Real.log ((c / 8) * (x * (1 / 2 : ℝ)) ^ α)| ≤
      (1 + |Real.log (c / 8)| + α * |Real.log (1 / 2 : ℝ)| + α * (u + v)) *
        (1 + |Real.log ε|) := by
  have hlogx := abs_log_le_of_two_sided_mesh_powers ε x u v hε hε1 hx hu hv hlower hupper
  have hlog : |Real.log ((c / 8) * (x * (1 / 2 : ℝ)) ^ α)| ≤
      |Real.log (c / 8)| + α * (|Real.log x| + |Real.log (1 / 2 : ℝ)|) := by
    rw [Real.log_mul (by positivity : c / 8 ≠ 0)
      (Real.rpow_pos_of_pos (by positivity : 0 < x * (1 / 2 : ℝ)) α).ne',
      Real.log_rpow (by positivity : 0 < x * (1 / 2 : ℝ)),
      Real.log_mul hx.ne' (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    have h₁ := abs_add_le (Real.log (c / 8))
      (α * (Real.log x + Real.log (1 / 2 : ℝ)))
    have h₂ := abs_add_le (Real.log x) (Real.log (1 / 2 : ℝ))
    rw [abs_mul, abs_of_nonneg hα] at h₁
    nlinarith [mul_le_mul_of_nonneg_left h₂ hα]
  have hz := abs_nonneg (Real.log ε)
  have hc' := abs_nonneg (Real.log (c / 8))
  have hhalf := abs_nonneg (Real.log (1 / 2 : ℝ))
  nlinarith [mul_le_mul_of_nonneg_left hlogx hα,
    mul_nonneg hα (add_nonneg hu hv), mul_nonneg hα hhalf,
    mul_nonneg hc' hz, mul_nonneg (mul_nonneg hα hhalf) hz,
    mul_nonneg (mul_nonneg hα (add_nonneg hu hv)) hz]

/-- Polynomial initial, target, and rescaled-maximum bounds choose a dyadic
level and a shell horizon bounded by a fixed cubic power of the mesh log. -/
theorem exists_dyadic_horizon_of_polynomial_scales
    (ε S B x p b u v α c s : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hS : 0 < S) (hB : 0 < B) (hx : 0 < x) (hα : 0 < α)
    (hc : 0 < c) (hs : 0 < s) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hpb : 0 ≤ p + b) (hSupper : S ≤ ε ^ (-p)) (hBlower : ε ^ b ≤ B)
    (hxlower : ε ^ u ≤ x) (hxupper : x ≤ ε ^ (-v)) :
    let a := (c / 8) * (x * (1 / 2 : ℝ)) ^ α
    let q := (1 / 2 : ℝ) ^ α
    let A := 1 + |Real.log (c / 8)| + α * |Real.log (1 / 2 : ℝ)| + α * (u + v)
    let C := (p + b) / Real.log 2
    ∃ N n : ℕ,
      S * (1 / 2 : ℝ) ^ N ≤ B ∧
      (N : ℝ) * (2 / s + 2) *
        (1 + |Real.log a| + |Real.log q| * (N : ℝ)) ^ 2 < n ∧
      (n : ℝ) ≤ (C + 2) * (2 / s + 2) *
        (A + |Real.log q| * (C + 2)) ^ 2 * (1 + |Real.log ε|) ^ 3 + 2 := by
  let a : ℝ := (c / 8) * (x * (1 / 2 : ℝ)) ^ α
  let q : ℝ := (1 / 2 : ℝ) ^ α
  let A : ℝ := 1 + |Real.log (c / 8)| + α * |Real.log (1 / 2 : ℝ)| + α * (u + v)
  let C : ℝ := (p + b) / Real.log 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hL : 1 ≤ 1 + |Real.log ε| := by linarith [abs_nonneg (Real.log ε)]
  have hratio : Real.log (S / B) ≤ C * (1 + |Real.log ε|) * Real.log 2 := by
    have hh := log_initial_target_ratio_le_halving_horizon ε ε S B p b 1
      hε hε1 hε (by norm_num) (by simp)
      hS hB hSupper hBlower hpb
    simpa only [one_mul, C] using hh
  have hlog : 1 + |Real.log a| ≤ A * (1 + |Real.log ε|) :=
    dyadic_test_scale_log_le_of_mesh_powers ε x u v α c hε hε1 hx hu hv hα.le hc
      hxlower hxupper
  exact exists_dyadic_level_and_cubic_horizon S B a q s (1 + |Real.log ε|) A C
    hS hB hs hL hA hC hratio hlog

end MatedCRT.Sec7
