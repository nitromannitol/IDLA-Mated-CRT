import MatedCRT.Proofs.Sec6.IterativeBound.Arith

/-!
# Lemma 6.10: the radius budget (Steps 1-4)

* `closure_cthickening_subset_ball`: `Θ̄ ⋐ B_{ρ₁}` and `ρ₁ + R < ρ₂` give `B⁺_R(Θ̄) ⋐ B_{ρ₂}`.
* `stage3_bound` (Steps 3-4 for few walkers): `(j - 1) ε^κ ≤ δ₀^β` when `j - 1 < δ₀/ε`, `j ≤ ε^{-ω'}` and
  `ω' + β ≤ κ`, uniformly in `δ₀ ∈ (0, 1]`.
* `budget_step` (Steps 1-2): with `x_n = (n ε/s₅)^a`, `r_n = max(x_n, r_min)` and the absorption rate
  `p ≥ c₄ r_n^{1/4}`, a round from `n` to `n₁ < (1 - p) n` walkers lowers `A x^{1/2} + B log n` by `r_n + d`
  (`A = 8/(a c₄)`, `B = 2 r_min^{3/4}/c₄`).
-/

namespace MatedCRT

open Set Metric

namespace IterativeBound

theorem closure_cthickening_subset_ball {X : Set ℂ} {R ρ₁ ρ₂ : ℝ} (hX : closure X ⊆ ball 0 ρ₁) (hR : 0 ≤ R)
    (hρ : ρ₁ + R < ρ₂) : closure (cthickening R X) ⊆ ball 0 ρ₂ := by
  rw [isClosed_cthickening.closure_eq, ← cthickening_closure]
  have hK : IsCompact (closure X) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (isBounded_ball.subset hX)
  rw [hK.cthickening_eq_biUnion_closedBall hR]
  intro y hy
  simp only [mem_iUnion, exists_prop] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  rw [mem_ball]
  calc dist y 0 ≤ dist y x + dist x 0 := dist_triangle y x 0
    _ < ρ₂ := by linarith [mem_closedBall.1 hxy, mem_ball.1 (hX hx)]

theorem stage3_bound {ε δ₀ ω' β κ : ℝ} {j : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ₀ : 0 < δ₀)
    (hω' : 0 < ω') (hβ : 0 < β) (hβ1 : β ≤ 1) (hκ : ω' + β ≤ κ)
    (hj1 : (j : ℝ) - 1 < δ₀ / ε) (hj2 : (j : ℝ) ≤ ε ^ (-ω')) :
    ((j : ℝ) - 1) * ε ^ κ ≤ δ₀ ^ β := by
  have hδβ : 0 < δ₀ ^ β := Real.rpow_pos_of_pos hδ₀ _
  have hεκ : 0 < ε ^ κ := Real.rpow_pos_of_pos hε _
  by_cases hj : (j : ℝ) - 1 ≤ 0
  · nlinarith
  push Not at hj
  by_cases hcase : δ₀ ≤ ε ^ (1 - ω')
  · have h1 : ((j : ℝ) - 1) * ε ^ κ ≤ δ₀ / ε * ε ^ κ := mul_le_mul_of_nonneg_right hj1.le hεκ.le
    have e1 : δ₀ ^ β * δ₀ ^ (1 - β) = δ₀ := by
      rw [← Real.rpow_add hδ₀]
      norm_num
    have e2 : ε ^ (κ - 1) = ε ^ κ / ε := by rw [Real.rpow_sub hε, Real.rpow_one]
    have h2 : δ₀ / ε * ε ^ κ = δ₀ ^ β * (δ₀ ^ (1 - β) * ε ^ (κ - 1)) := by
      calc δ₀ / ε * ε ^ κ = (δ₀ ^ β * δ₀ ^ (1 - β)) * (ε ^ κ / ε) := by rw [e1]; ring
        _ = δ₀ ^ β * (δ₀ ^ (1 - β) * ε ^ (κ - 1)) := by rw [e2]; ring
    have h3 : δ₀ ^ (1 - β) ≤ (ε ^ (1 - ω')) ^ (1 - β) := Real.rpow_le_rpow hδ₀.le hcase (by linarith)
    have h4 : (ε ^ (1 - ω')) ^ (1 - β) * ε ^ (κ - 1) ≤ 1 := by
      rw [← Real.rpow_mul hε.le, ← Real.rpow_add hε]
      exact Real.rpow_le_one hε.le hε1 (by nlinarith [mul_pos hω' hβ])
    calc ((j : ℝ) - 1) * ε ^ κ ≤ δ₀ ^ β * (δ₀ ^ (1 - β) * ε ^ (κ - 1)) := h1.trans h2.le
      _ ≤ δ₀ ^ β * 1 := by
          apply mul_le_mul_of_nonneg_left _ hδβ.le
          exact (mul_le_mul_of_nonneg_right h3 (Real.rpow_pos_of_pos hε _).le).trans h4
      _ = δ₀ ^ β := mul_one _
  · push Not at hcase
    have h1 : ((j : ℝ) - 1) * ε ^ κ ≤ ε ^ (-ω') * ε ^ κ :=
      mul_le_mul_of_nonneg_right (by linarith) hεκ.le
    have h2 : ε ^ (-ω') * ε ^ κ ≤ (ε ^ (1 - ω')) ^ β := by
      rw [← Real.rpow_add hε, ← Real.rpow_mul hε.le]
      exact Real.rpow_le_rpow_of_exponent_ge hε hε1 (by nlinarith [mul_pos hω' hβ])
    have h3 : (ε ^ (1 - ω')) ^ β ≤ δ₀ ^ β :=
      Real.rpow_le_rpow (Real.rpow_pos_of_pos hε _).le hcase.le hβ.le
    linarith

theorem one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem log_natCast_le_log_natCast {n₁ n : ℕ} (h : n₁ ≤ n) : Real.log n₁ ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n₁ with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast h)

/-- **The budget of one round** (Steps 1-2). -/
theorem budget_step {ε s₅ a c₄ rmin d p : ℝ} {n n₁ : ℕ}
    (hε : 0 < ε) (hs₅ : 0 < s₅) (ha : 0 < a) (ha1 : a ≤ 1 / 2) (hc₄ : 0 < c₄) (hc₄1 : c₄ ≤ 1)
    (hrmin : 0 < rmin) (hrmin1 : rmin ≤ 1) (hdr : d ≤ rmin) (hn3 : 3 ≤ n)
    (hx1 : ((n : ℝ) * ε / s₅) ^ a ≤ 1)
    (hp : c₄ * (max (((n : ℝ) * ε / s₅) ^ a) rmin) ^ (1 / 4 : ℝ) ≤ p) (hp1 : p < 1)
    (hn₁ : (n₁ : ℝ) < (1 - p) * n) :
    8 / (a * c₄) * (((n₁ : ℝ) * ε / s₅) ^ a) ^ (1 / 2 : ℝ) + 2 * rmin ^ (3 / 4 : ℝ) / c₄ * Real.log n₁ +
        (max (((n : ℝ) * ε / s₅) ^ a) rmin + d) ≤
      8 / (a * c₄) * (((n : ℝ) * ε / s₅) ^ a) ^ (1 / 2 : ℝ) + 2 * rmin ^ (3 / 4 : ℝ) / c₄ * Real.log n := by
  set x := ((n : ℝ) * ε / s₅) ^ a with hx_def
  set x₁ := ((n₁ : ℝ) * ε / s₅) ^ a with hx₁_def
  set B := 2 * rmin ^ (3 / 4 : ℝ) / c₄ with hB
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx0 : 0 < x := Real.rpow_pos_of_pos (by positivity) _
  have hx₁0 : 0 ≤ x₁ := Real.rpow_nonneg (by positivity) _
  have hmax0 : 0 < max x rmin := lt_max_of_lt_right hrmin
  have hp0 : 0 ≤ p := le_trans (by positivity) hp
  have h1p : 0 ≤ 1 - p := by linarith
  have hn₁n : n₁ ≤ n := by
    have : (n₁ : ℝ) < n := lt_of_lt_of_le hn₁ (by nlinarith)
    exact_mod_cast this.le
  have hx₁le : x₁ ≤ (1 - p) ^ a * x := by
    calc x₁ ≤ ((1 - p) * n * ε / s₅) ^ a :=
          Real.rpow_le_rpow (by positivity)
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hn₁.le hε.le) hs₅.le) ha.le
      _ = (1 - p) ^ a * x := by
          rw [show (1 - p) * n * ε / s₅ = (1 - p) * (n * ε / s₅) by ring, Real.mul_rpow h1p (by positivity)]
  have hx₁x : x₁ ≤ x :=
    Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hn₁n) hε.le) hs₅.le) ha.le
  have hlog := log_natCast_le_log_natCast hn₁n
  have hB0 : 0 ≤ B := by positivity
  have hr34 : rmin ≤ rmin ^ (3 / 4 : ℝ) := by
    calc rmin = rmin ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ rmin ^ (3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hrmin hrmin1 (by norm_num)
  have hBr : B * (c₄ * rmin ^ (1 / 4 : ℝ)) = 2 * rmin := by
    rw [hB]
    have : rmin ^ (3 / 4 : ℝ) * rmin ^ (1 / 4 : ℝ) = rmin := by
      rw [← Real.rpow_add hrmin]
      norm_num
    calc 2 * rmin ^ (3 / 4 : ℝ) / c₄ * (c₄ * rmin ^ (1 / 4 : ℝ))
        = 2 * (rmin ^ (3 / 4 : ℝ) * rmin ^ (1 / 4 : ℝ)) * (c₄ / c₄) := by ring
      _ = 2 * rmin := by rw [this, div_self hc₄.ne', mul_one]
  by_cases hcase : rmin ≤ x
  · rw [max_eq_left hcase] at hp ⊢
    have hst := potential_step hx0 hx1 hx₁0 ha ha1 hc₄ hp hp1 hx₁le
    have := mul_le_mul_of_nonneg_left hlog hB0
    linarith
  · push Not at hcase
    rw [max_eq_right hcase.le] at hp ⊢
    have hsq : 8 / (a * c₄) * x₁ ^ (1 / 2 : ℝ) ≤ 8 / (a * c₄) * x ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx₁0 hx₁x (by norm_num)) (by positivity)
    suffices hB' : B * Real.log n₁ + 2 * rmin ≤ B * Real.log n by linarith
    rcases Nat.eq_zero_or_pos n₁ with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero, mul_zero, zero_add]
      have h3 : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn3)
      have hB2 : 2 * rmin ≤ B := by
        rw [hB, le_div_iff₀ hc₄]
        nlinarith
      nlinarith [one_lt_log_three]
    · have hn₁pos : (0 : ℝ) < n₁ := by exact_mod_cast h0
      have hp1' : 0 < 1 - p := by
        by_contra h
        push Not at h
        nlinarith
      have hl1 : Real.log n₁ ≤ Real.log (1 - p) + Real.log n := by
        rw [← Real.log_mul hp1'.ne' hn0.ne']
        exact Real.log_le_log hn₁pos hn₁.le
      have hl2 : Real.log (1 - p) ≤ -p := by
        have := Real.log_le_sub_one_of_pos hp1'
        linarith
      have hBp : 2 * rmin ≤ B * p := by
        rw [← hBr]
        exact mul_le_mul_of_nonneg_left hp hB0
      nlinarith

end IterativeBound

end MatedCRT
