import MatedCRT.Proofs.Sec6.IterativeBound.Budget

/-!
# Lemma 6.10: the ε-dependent error terms (Steps 2-4)

* `eventually_rpow_le`: `ε^s ≤ c` for small `ε` (`s, c > 0`).
* `log_term_bound`: the cost `B log j` of the rounds at radius `r_min = 10 ε^ω` is `O(ε^{ω/2})` for `j ≤ 2/ε`.
* `failure_bound`: the union bound over at most `j ≤ 2/ε` rounds, each failing with probability
  `exp(-(s₃/64) r_min^{1/4} ε^{-ω/2})`, is at most `M ε` (eqn:use-absorb).
-/

namespace MatedCRT

open Filter Topology Set

namespace IterativeBound

theorem eventually_rpow_le {s c : ℝ} (hs : 0 < s) (hc : 0 < c) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ s ≤ c := by
  have h0 : Tendsto (fun ε : ℝ => ε ^ s) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ s)) :=
    ((Real.continuousAt_rpow_const 0 s (Or.inr hs.le)).tendsto).mono_left nhdsWithin_le_nhds
  rw [Real.zero_rpow hs.ne'] at h0
  exact h0.eventually (Iic_mem_nhds hc)

theorem eventually_le_const {c : ℝ} (hc : 0 < c) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ c :=
  nhdsWithin_le_nhds (Iic_mem_nhds hc)

theorem log_term_bound {ε ω₂ c₄ : ℝ} {j : ℕ} (hε : 0 < ε) (hω : 0 < ω₂) (hc₄ : 0 < c₄)
    (hj : (j : ℝ) ≤ 2 / ε) :
    2 * (10 * ε ^ ω₂) ^ (3 / 4 : ℝ) / c₄ * Real.log j ≤ 80 * 2 ^ (ω₂ / 4) / (c₄ * ω₂) * ε ^ (ω₂ / 2) := by
  set t := ω₂ / 4 with ht
  have ht0 : 0 < t := by positivity
  have hlog : Real.log j ≤ (j : ℝ) ^ t / t := Real.log_le_rpow_div (Nat.cast_nonneg j) ht0
  have hjt : (j : ℝ) ^ t ≤ (2 / ε) ^ t := Real.rpow_le_rpow (Nat.cast_nonneg j) hj ht0.le
  have h2e : (2 / ε) ^ t = 2 ^ t * ε ^ (-t) := by
    rw [Real.div_rpow (by norm_num) hε.le, Real.rpow_neg hε.le, div_eq_mul_inv]
  have h10 : (10 * ε ^ ω₂) ^ (3 / 4 : ℝ) ≤ 10 * ε ^ (3 * ω₂ / 4) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hε.le]
    have h : (10 : ℝ) ^ (3 / 4 : ℝ) ≤ 10 := by
      calc (10 : ℝ) ^ (3 / 4 : ℝ) ≤ 10 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 10 := Real.rpow_one 10
    rw [show ω₂ * (3 / 4) = 3 * ω₂ / 4 by ring]
    exact mul_le_mul_of_nonneg_right h (by positivity)
  have hcomb : ε ^ (3 * ω₂ / 4) * ε ^ (-t) = ε ^ (ω₂ / 2) := by
    rw [← Real.rpow_add hε]
    congr 1
    rw [ht]
    ring
  have hlog0 : 0 ≤ Real.log j := Real.log_natCast_nonneg j
  calc 2 * (10 * ε ^ ω₂) ^ (3 / 4 : ℝ) / c₄ * Real.log j
      ≤ 2 * (10 * ε ^ (3 * ω₂ / 4)) / c₄ * ((2 / ε) ^ t / t) := by
        apply mul_le_mul (div_le_div_of_nonneg_right (by linarith) hc₄.le)
          (hlog.trans (div_le_div_of_nonneg_right hjt ht0.le)) hlog0 (by positivity)
    _ = 80 * 2 ^ t / (c₄ * ω₂) * (ε ^ (3 * ω₂ / 4) * ε ^ (-t)) := by
        rw [h2e, ht]
        field_simp
        ring
    _ = 80 * 2 ^ (ω₂ / 4) / (c₄ * ω₂) * ε ^ (ω₂ / 2) := by rw [hcomb]

theorem failure_bound {ε ω₂ c₃ : ℝ} {j : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hω : 0 < ω₂) (hc₃ : 0 < c₃)
    (hj : (j : ℝ) ≤ 2 / ε) :
    (j : ℝ) * Real.exp (-(c₃ * (10 * ε ^ ω₂) ^ (1 / 4 : ℝ) * ε ^ (-(ω₂ / 2)))) ≤
      2 * ((⌈8 / ω₂⌉₊).factorial : ℝ) / c₃ ^ ⌈8 / ω₂⌉₊ * ε := by
  set k := ⌈8 / ω₂⌉₊ with hk
  set y₀ := c₃ * ε ^ (-(ω₂ / 4)) with hy₀
  have hy₀pos : 0 < y₀ := by positivity
  have hy : y₀ ≤ c₃ * (10 * ε ^ ω₂) ^ (1 / 4 : ℝ) * ε ^ (-(ω₂ / 2)) := by
    have h1 : ε ^ (ω₂ / 4) ≤ (10 * ε ^ ω₂) ^ (1 / 4 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hε.le]
      have h10 : (1 : ℝ) ≤ 10 ^ (1 / 4 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
      rw [show ω₂ * (1 / 4) = ω₂ / 4 by ring]
      nlinarith [Real.rpow_pos_of_pos hε (ω₂ / 4)]
    have h2 : ε ^ (-(ω₂ / 4)) = ε ^ (ω₂ / 4) * ε ^ (-(ω₂ / 2)) := by
      rw [← Real.rpow_add hε]
      congr 1
      ring
    rw [hy₀, h2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hc₃.le) (by positivity)
  have he : Real.exp (-(c₃ * (10 * ε ^ ω₂) ^ (1 / 4 : ℝ) * ε ^ (-(ω₂ / 2)))) ≤ k.factorial / y₀ ^ k :=
    (Real.exp_le_exp.2 (neg_le_neg hy)).trans (exp_neg_le_factorial_div hy₀pos k)
  have hk8 : 8 / ω₂ ≤ k := Nat.le_ceil _
  have hyk : (k.factorial : ℝ) / y₀ ^ k = k.factorial / c₃ ^ k * ε ^ (ω₂ / 4 * k) := by
    rw [hy₀, mul_pow, ← Real.rpow_mul_natCast hε.le,
      show -(ω₂ / 4) * (k : ℝ) = -(ω₂ / 4 * k) by ring, Real.rpow_neg hε.le]
    field_simp
  have hεk : ε ^ (ω₂ / 4 * k) ≤ ε ^ 2 := by
    have h2 : (2 : ℝ) ≤ ω₂ / 4 * k := by
      rw [div_le_iff₀ hω] at hk8
      nlinarith
    calc ε ^ (ω₂ / 4 * k) ≤ ε ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hε hε1 h2
      _ = ε ^ 2 := by norm_cast
  have he' : Real.exp (-(c₃ * (10 * ε ^ ω₂) ^ (1 / 4 : ℝ) * ε ^ (-(ω₂ / 2)))) ≤
      k.factorial / c₃ ^ k * ε ^ 2 :=
    he.trans (hyk ▸ mul_le_mul_of_nonneg_left hεk (by positivity))
  calc (j : ℝ) * Real.exp (-(c₃ * (10 * ε ^ ω₂) ^ (1 / 4 : ℝ) * ε ^ (-(ω₂ / 2))))
      ≤ 2 / ε * (k.factorial / c₃ ^ k * ε ^ 2) :=
        mul_le_mul hj he' (Real.exp_pos _).le (by positivity)
    _ = 2 * (k.factorial : ℝ) / c₃ ^ k * ε := by
        field_simp

end IterativeBound

end MatedCRT
