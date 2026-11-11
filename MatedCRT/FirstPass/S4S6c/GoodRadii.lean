import Mathlib

/-!
# Candidate radii of Lemma 2

The candidate-radius condition asks that a good radius `R_z` lie in `[δ, √δ] ∩ {7^{-n} : n ∈ ℕ}`. The deterministic part is that this
set is nonempty for every dyadic-scale `δ ≤ 1/49`: the powers `7^{-n}` have ratio `7`, which is at most `δ^{-1/2}`
on `(0, 1/49]`. Goodness of the radius is the probabilistic part of Lemma 2 and is not here.
-/

namespace MatedCRT

/-- For `0 < δ ≤ 1/49` there is `n : ℕ` with `δ ≤ 7^{-n} ≤ √δ`. -/
theorem exists_seven_pow_mem_Icc {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 49) :
    ∃ n : ℕ, δ ≤ (1 / 7 : ℝ) ^ n ∧ (1 / 7 : ℝ) ^ n ≤ Real.sqrt δ := by
  classical
  have hs0 : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  have hsq : Real.sqrt δ ≤ 1 / 7 := Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
  have hex : ∃ n : ℕ, (1 / 7 : ℝ) ^ n ≤ Real.sqrt δ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hs0 (by norm_num : (1 / 7 : ℝ) < 1)
    exact ⟨n, hn.le⟩
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, (1 / 7 : ℝ) ^ n ≤ Real.sqrt δ ∧
      ∀ m < n, ¬ (1 / 7 : ℝ) ^ m ≤ Real.sqrt δ :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  rcases n with _ | m
  · exfalso
    rw [pow_zero] at hn
    linarith
  · refine ⟨m + 1, ?_, hn⟩
    have hm : Real.sqrt δ < (1 / 7 : ℝ) ^ m := not_le.1 (hmin m (Nat.lt_succ_self m))
    have hsqδ : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ0.le
    rw [pow_succ]
    nlinarith [mul_nonneg hs0.le (sub_nonneg.2 hsq), mul_lt_mul_of_pos_right hm (by norm_num : (0 : ℝ) < 1 / 7)]

end MatedCRT
