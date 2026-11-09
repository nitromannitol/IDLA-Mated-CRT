import MatedCRT.FirstPass.S5c.Scaling

/-!
# FIRST PASS, Lemma 5.3: the floor term is monotone in the scale index (B1c, monotone route)

For `0 < s ≤ u`, `leastSupersolution_le_scaled` gives `w_s ≤ (s/u) w_u`, i.e. `w_s/s ≤ w_u/u`. So along the scales
`s_n = t (1/2)^n`, which decrease in `n`, the floor term `w_t + t(-w_{s_n}/s_n)` of Floor.lean is nondecreasing in `n`.
This is the monotonicity that a Dini-type argument needs to make the floor index uniform on compact sets (B1c of
reports/q3.md). Pure algebra on top of Scaling.lean; no new mathematics.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric
open _root_.HarmonicBalls

/-- **Monotone scale quotient**: for `0 < s ≤ u`, `w_s/s ≤ w_u/u` (from the scaling bound of Scaling.lean). -/
theorem div_leastSupersolution_le_of_le {μ : Measure ℂ} {r : ℝ} {z : ℂ} {s u : ℝ} (hs : 0 < s) (hsu : s ≤ u)
    (x : ℂ) (hb : ∀ τ : ℝ, 0 ≤ τ → BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutions μ r z τ)) :
    leastSupersolution μ r z s x / s ≤ leastSupersolution μ r z u x / u := by
  have hu : 0 < u := lt_of_lt_of_le hs hsu
  have h := leastSupersolution_le_scaled (μ := μ) (r := r) (z := z) hs hsu x hb
  rw [div_le_div_iff₀ hs hu]
  have h2 := mul_le_mul_of_nonneg_right h hu.le
  have h3 : s / u * leastSupersolution μ r z u x * u = s * leastSupersolution μ r z u x := by
    field_simp [hu.ne']
  linarith [h2, h3]

/-- **Monotone floor term** (Floor.lean, the expression `w_t + t(-w_{s_n}/s_n)` with `s_n = t (1/2)^n`): nondecreasing in `n`. -/
theorem floorTerm_monotone {μ : Measure ℂ} {ρ t : ℝ} (ht : 0 < t) (x : ℂ)
    (hb : ∀ τ : ℝ, 0 ≤ τ → BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutions μ ρ 0 τ)) :
    Monotone (fun n : ℕ => leastSupersolution μ ρ 0 t x +
      t * (-(leastSupersolution μ ρ 0 (t * (1 / 2) ^ n) x) / (t * (1 / 2) ^ n))) := by
  intro n m hnm
  have hsm : 0 < t * (1 / 2 : ℝ) ^ m := mul_pos ht (by positivity)
  have hle : t * (1 / 2 : ℝ) ^ m ≤ t * (1 / 2 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hnm) ht.le
  have h := div_leastSupersolution_le_of_le (μ := μ) (r := ρ) (z := 0) hsm hle x hb
  have h' : -(leastSupersolution μ ρ 0 (t * (1 / 2) ^ n) x) / (t * (1 / 2) ^ n) ≤
      -(leastSupersolution μ ρ 0 (t * (1 / 2) ^ m) x) / (t * (1 / 2) ^ m) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact h
  dsimp only
  linarith [mul_le_mul_of_nonneg_left h' ht.le]

end MatedCRT.S5c
