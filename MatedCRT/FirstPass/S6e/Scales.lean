import Mathlib

/-!
# FIRST PASS: the dyadic scale and the constant q₀ of LEMMA68 (N1, N2) (task fp-S6e-lemma68-C17, z9)

Source: `notes/fp-gaps/CHATGPT-z9-lemma68-B1B2.md` §7 (N1: `q₀ ≤ 1` from the definition of `q*`) and §8 (N2: the
dyadic scale `Δ(r) = 2^{-n(r)}`, `n(r) = min {n : 2^{-n} ≤ r^p}`, with `r^p/2 < Δ(r) ≤ r^p` and
`s(r) = √Δ(r) ≤ r^{1+ζ}`, `ζ = p/2 - 1`; equations (19)-(20)). The name `Δ(r)` replaces the overloaded `δ` of the
write-up (C1 uses `s = √δ`, D4 the boxed `δ`); the final cutoff of §8.3 is `r_cut`, not defined here.
-/

open Real

namespace MatedCRT

namespace Lemma68Scales

/-! ### N1: the constant `q₀` -/

/-- `q* = min {1/2, (16 C₂)⁻¹}` (write-up, C16; `C₂ > 0`). -/
noncomputable def qStar (C2 : ℝ) : ℝ := min (1 / 2 : ℝ) ((16 * C2)⁻¹)

/-- `q₀ = q*/9` (write-up, §7). -/
noncomputable def q0Of (C2 : ℝ) : ℝ := qStar C2 / 9

lemma qStar_le_half (C2 : ℝ) : qStar C2 ≤ 1 / 2 := min_le_left _ _

/-- (N1) `q₀ ≤ 1` follows from the definition of `q*` alone; no sign condition on `C₂` is needed. -/
lemma q0_le_one (C2 : ℝ) : q0Of C2 ≤ 1 := by
  have := qStar_le_half C2
  unfold q0Of
  linarith

/-- (N1) `0 < q₀` once `C₂ > 0`. -/
lemma q0_pos {C2 : ℝ} (hC2 : 0 < C2) : 0 < q0Of C2 := by
  unfold q0Of qStar
  apply div_pos _ (by norm_num)
  exact lt_min (by norm_num) (inv_pos.2 (by linarith))

/-- (N1) For `0 < r ≤ 1` the radius-dependent constant `q₀ / (1 + log(1/r))²` lies in `[0, q₀]`, so the factor
`1 - q(r)` of C17 is nonnegative. -/
lemma q_le_q0 {C2 r : ℝ} (hC2 : 0 < C2) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    q0Of C2 / (1 + Real.log (1 / r)) ^ 2 ≤ q0Of C2 := by
  have hlog : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr0 hr1)
  have hsq : 1 ≤ (1 + Real.log (1 / r)) ^ 2 := by nlinarith
  exact div_le_self (q0_pos hC2).le hsq

/-! ### N2: the dyadic scale `Δ(r)` -/

/-- `n(r) = min {n : 2^{-n} ≤ r^p}` (write-up (19)); the set is nonempty for `r > 0`. -/
noncomputable def dyadicIndex (p r : ℝ) : ℕ := sInf {n : ℕ | (1 / 2 : ℝ) ^ n ≤ r ^ p}

/-- `Δ(r) = 2^{-n(r)}` (write-up (19)). -/
noncomputable def Delta (p r : ℝ) : ℝ := (1 / 2 : ℝ) ^ dyadicIndex p r

/-- `s(r) = √Δ(r)` (write-up (19)). -/
noncomputable def sScale (p r : ℝ) : ℝ := Real.sqrt (Delta p r)

/-- (N2, (20)) Minimality and the defining property of `n(r)`: `r^p/2 < Δ(r) ≤ r^p` for `0 < r < 1`, `p > 0`. -/
lemma dyadicIndex_spec {p r : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) :
    (1 / 2 : ℝ) ^ dyadicIndex p r ≤ r ^ p ∧ r ^ p < 2 * (1 / 2 : ℝ) ^ dyadicIndex p r := by
  have hrp0 : 0 < r ^ p := Real.rpow_pos_of_pos hr0 p
  have hrp1 : r ^ p < 1 := Real.rpow_lt_one hr0.le hr1 hp
  obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one hrp0 (show (1 / 2 : ℝ) < 1 by norm_num)
  have hne : {n : ℕ | (1 / 2 : ℝ) ^ n ≤ r ^ p}.Nonempty := ⟨n0, hn0.le⟩
  have hmem : (1 / 2 : ℝ) ^ dyadicIndex p r ≤ r ^ p := Nat.sInf_mem hne
  refine ⟨hmem, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, dyadicIndex p r = k + 1 := by
    rcases Nat.eq_zero_or_pos (dyadicIndex p r) with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hmem
      linarith
    · exact ⟨dyadicIndex p r - 1, by omega⟩
  have hk' : r ^ p < (1 / 2 : ℝ) ^ k := by
    by_contra hcon
    have hle : dyadicIndex p r ≤ k := Nat.sInf_le (not_lt.1 hcon)
    omega
  rw [hk, pow_succ]
  linarith

lemma half_rpow_lt_Delta {p r : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) :
    r ^ p / 2 < Delta p r := by
  have := (dyadicIndex_spec hp hr0 hr1).2
  unfold Delta
  linarith

lemma Delta_le_rpow {p r : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) : Delta p r ≤ r ^ p :=
  (dyadicIndex_spec hp hr0 hr1).1

/-- (N2, (20)) `s(r) = √Δ(r) ≤ r^{p/2}`. -/
lemma sScale_le_rpow_half {p r : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) :
    sScale p r ≤ r ^ (p / 2) := by
  unfold sScale
  calc Real.sqrt (Delta p r) ≤ Real.sqrt (r ^ p) := Real.sqrt_le_sqrt (Delta_le_rpow hp hr0 hr1)
    _ = r ^ (p / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr0.le]
      congr 1
      ring

/-- (N2, the form used by C16 and D4) `s(r) ≤ r^{1+ζ}` for `ζ = p/2 - 1`. -/
lemma sScale_le_rpow_one_add {p r : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) :
    sScale p r ≤ r ^ (1 + (p / 2 - 1)) := by
  rw [show (1 : ℝ) + (p / 2 - 1) = p / 2 by ring]
  exact sScale_le_rpow_half hp hr0 hr1

end Lemma68Scales

end MatedCRT
