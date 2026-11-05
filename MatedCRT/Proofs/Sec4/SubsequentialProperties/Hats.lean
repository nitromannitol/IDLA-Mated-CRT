import MatedCRT.Defs.Notation

/-!
# Tensor hat functions: a countable Lipschitz partition of unity

The boundary data of the discrete Dirichlet problems in Steps 2 and 3 of the proof of Lemma 4.8
(paper/idla_mated_crt-corrected.tex, l.1806-1816) must be deterministic (Lemma 3.5 is stated for deterministic data),
while they approximate the random subsequential limit. The paper uses polynomials with rational coefficients. Here the
data are finite combinations `∑ c_p hat_p` of the countably many tensor hat functions
`hat n j k (x) = h(n Re x - j) h(n Im x - k)`, `h(s) = max(0, 1 - |s|)`, with random coefficients `c_p`; Lemma 3.5 is
applied to each `hat n j k` and the combinations are handled by linearity.

* `hat_nonneg`, `hat_eq_zero_of_far`: `hat n j k ≥ 0` vanishes off the square of side `2/n` around `(j/n, k/n)`;
* `sum_hat_eq_one`: the hats at scale `n` form a partition of unity;
* `abs_sub_sum_hat_le`: `|g(x) - ∑ g(p) hat_p(x)| ≤ δ` if `g` oscillates by at most `δ` at distance `< 2/n`;
* `isHolderContinuousOn_hat`: each hat is Lipschitz, hence Hölder continuous.
-/

namespace MatedCRT

open Metric Finset
open scoped NNReal

/-- The one-dimensional hat `h(s) = max(0, 1 - |s|)`. -/
noncomputable def hat1 (s : ℝ) : ℝ := max 0 (1 - |s|)

theorem hat1_nonneg (s : ℝ) : 0 ≤ hat1 s := le_max_left _ _

theorem hat1_le_one (s : ℝ) : hat1 s ≤ 1 := max_le zero_le_one (by linarith [abs_nonneg s])

theorem hat1_eq_zero {s : ℝ} (hs : 1 ≤ |s|) : hat1 s = 0 := max_eq_left (by linarith)

theorem hat1_le_add (s t : ℝ) : hat1 s ≤ hat1 t + |s - t| := by
  unfold hat1
  refine max_le (add_nonneg (le_max_left _ _) (abs_nonneg _)) ?_
  have h := abs_sub_abs_le_abs_sub t s
  rw [abs_sub_comm t s] at h
  linarith [le_max_right (0 : ℝ) (1 - |t|)]

/-- `h` is `1`-Lipschitz. -/
theorem abs_hat1_sub_le (s t : ℝ) : |hat1 s - hat1 t| ≤ |s - t| := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [hat1_le_add s t]
  · linarith [hat1_le_add t s, abs_sub_comm s t]

/-- On `[0, 1]`, the hats at `0` and `1` sum to `1`. -/
theorem hat1_add_hat1_sub_one {f : ℝ} (h0 : 0 ≤ f) (h1 : f < 1) : hat1 f + hat1 (f - 1) = 1 := by
  unfold hat1
  rw [abs_of_nonneg h0, abs_of_neg (by linarith : f - 1 < 0), max_eq_right (by linarith),
    max_eq_right (by linarith)]
  ring

/-- **Partition of unity in one dimension**: `∑_{j ∈ [-N, N]} h(s - j) = 1` if `|s| + 1 ≤ N`. -/
theorem sum_hat1_eq_one {s : ℝ} {N : ℕ} (hN : |s| + 1 ≤ N) :
    ∑ j ∈ Icc (-(N : ℤ)) N, hat1 (s - j) = 1 := by
  set j₀ : ℤ := ⌊s⌋ with hj₀
  have hfl : (j₀ : ℝ) ≤ s := Int.floor_le s
  have hfl' : s < (j₀ : ℝ) + 1 := Int.lt_floor_add_one s
  have hsN := abs_le.1 (show |s| ≤ (N : ℝ) - 1 by linarith)
  have hmem0 : j₀ ∈ Icc (-(N : ℤ)) N := by
    rw [Finset.mem_Icc]
    constructor
    · have : (-(N : ℝ)) ≤ j₀ := by linarith
      exact_mod_cast this
    · have : (j₀ : ℝ) ≤ N := by linarith
      exact_mod_cast this
  have hmem1 : j₀ + 1 ∈ Icc (-(N : ℤ)) N := by
    rw [Finset.mem_Icc]
    constructor
    · have : (-(N : ℝ)) ≤ (j₀ : ℝ) + 1 := by linarith
      exact_mod_cast this
    · have : (j₀ : ℝ) + 1 ≤ N := by linarith
      exact_mod_cast this
  rw [Finset.sum_eq_add j₀ (j₀ + 1) (by omega) ?_ (fun h => absurd hmem0 h) (fun h => absurd hmem1 h)]
  · push_cast
    have := hat1_add_hat1_sub_one (f := s - j₀) (by linarith) (by linarith)
    rw [show s - ((j₀ : ℝ) + 1) = s - j₀ - 1 by ring]
    exact this
  · intro c _ hc
    apply hat1_eq_zero
    rcases lt_or_gt_of_ne hc.1 with h | h
    · have : (c : ℝ) + 1 ≤ j₀ := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]
      linarith
    · have h2 : j₀ + 1 < c := lt_of_le_of_ne h (Ne.symm hc.2)
      have : (j₀ : ℝ) + 2 ≤ c := by
        have : j₀ + 2 ≤ c := by omega
        exact_mod_cast this
      rw [abs_of_neg (by linarith)]
      linarith

/-- The tensor hat at scale `n` centred at `(j/n, k/n)`. -/
noncomputable def hat (n : ℕ) (j k : ℤ) (x : ℂ) : ℝ :=
  hat1 (n * x.re - j) * hat1 (n * x.im - k)

/-- The centre `(j/n, k/n)` of `hat n j k`. -/
noncomputable def hatPoint (n : ℕ) (j k : ℤ) : ℂ := ⟨j / n, k / n⟩

theorem hat_nonneg (n : ℕ) (j k : ℤ) (x : ℂ) : 0 ≤ hat n j k x :=
  mul_nonneg (hat1_nonneg _) (hat1_nonneg _)

/-- The index square of the hats at scale `n` used on `B_R(0)`. -/
def hatIndex (N : ℕ) : Finset (ℤ × ℤ) := Icc (-(N : ℤ)) N ×ˢ Icc (-(N : ℤ)) N

/-- **Partition of unity**: `∑_{(j, k)} hat n j k (x) = 1` if `|n Re x| + 1 ≤ N` and `|n Im x| + 1 ≤ N`. -/
theorem sum_hat_eq_one {n N : ℕ} {x : ℂ} (hre : |(n : ℝ) * x.re| + 1 ≤ N) (him : |(n : ℝ) * x.im| + 1 ≤ N) :
    ∑ p ∈ hatIndex N, hat n p.1 p.2 x = 1 := by
  unfold hatIndex hat
  rw [Finset.sum_product]
  dsimp only
  rw [← Finset.sum_mul_sum, sum_hat1_eq_one hre, sum_hat1_eq_one him, one_mul]

/-- A hat vanishes at points at distance `≥ 2/n` from its centre. -/
theorem dist_hatPoint_lt_of_hat_ne_zero {n : ℕ} (hn : 0 < n) {j k : ℤ} {x : ℂ} (h : hat n j k x ≠ 0) :
    dist x (hatPoint n j k) < 2 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : |(n : ℝ) * x.re - j| < 1 := by
    by_contra hc
    exact h (by rw [hat, hat1_eq_zero (not_lt.1 hc), zero_mul])
  have h2 : |(n : ℝ) * x.im - k| < 1 := by
    by_contra hc
    exact h (by rw [hat, hat1_eq_zero (not_lt.1 hc), mul_zero])
  have hre : |(x - hatPoint n j k).re| < 1 / n := by
    have : (x - hatPoint n j k).re = ((n : ℝ) * x.re - j) / n := by
      simp only [Complex.sub_re, hatPoint]
      field_simp
    rw [this, abs_div, abs_of_pos hn', div_lt_div_iff_of_pos_right hn']
    exact h1
  have him : |(x - hatPoint n j k).im| < 1 / n := by
    have : (x - hatPoint n j k).im = ((n : ℝ) * x.im - k) / n := by
      simp only [Complex.sub_im, hatPoint]
      field_simp
    rw [this, abs_div, abs_of_pos hn', div_lt_div_iff_of_pos_right hn']
    exact h2
  rw [dist_eq_norm]
  have h2n : 2 / (n : ℝ) = 1 / n + 1 / n := by ring
  rw [h2n]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans_lt (add_lt_add hre him)

/-- **Approximation by hats.** If `|g(x) - g(y)| ≤ δ` whenever `|x - y| < 2/n`, and the partition of unity holds at
`x`, then `|g(x) - ∑_p g(p) hat_p(x)| ≤ δ`. -/
theorem abs_sub_sum_hat_le {n N : ℕ} (hn : 0 < n) {x : ℂ} (hre : |(n : ℝ) * x.re| + 1 ≤ N)
    (him : |(n : ℝ) * x.im| + 1 ≤ N) {g : ℂ → ℝ} {δ : ℝ}
    (hg : ∀ p ∈ hatIndex N, dist x (hatPoint n p.1 p.2) < 2 / n → |g x - g (hatPoint n p.1 p.2)| ≤ δ) :
    |g x - ∑ p ∈ hatIndex N, g (hatPoint n p.1 p.2) * hat n p.1 p.2 x| ≤ δ := by
  have hsum := sum_hat_eq_one hre him
  have hrw : g x - ∑ p ∈ hatIndex N, g (hatPoint n p.1 p.2) * hat n p.1 p.2 x =
      ∑ p ∈ hatIndex N, (g x - g (hatPoint n p.1 p.2)) * hat n p.1 p.2 x := by
    have h : ∑ p ∈ hatIndex N, (g x - g (hatPoint n p.1 p.2)) * hat n p.1 p.2 x =
        g x * ∑ p ∈ hatIndex N, hat n p.1 p.2 x -
          ∑ p ∈ hatIndex N, g (hatPoint n p.1 p.2) * hat n p.1 p.2 x := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [h, hsum, mul_one]
  rw [hrw]
  calc |∑ p ∈ hatIndex N, (g x - g (hatPoint n p.1 p.2)) * hat n p.1 p.2 x|
      ≤ ∑ p ∈ hatIndex N, |(g x - g (hatPoint n p.1 p.2)) * hat n p.1 p.2 x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ hatIndex N, δ * hat n p.1 p.2 x := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [abs_mul, abs_of_nonneg (hat_nonneg _ _ _ _)]
        by_cases h0 : hat n p.1 p.2 x = 0
        · rw [h0, mul_zero, mul_zero]
        · exact mul_le_mul_of_nonneg_right (hg p hp (dist_hatPoint_lt_of_hat_ne_zero hn h0))
            (hat_nonneg _ _ _ _)
    _ = δ := by rw [← Finset.mul_sum, hsum, mul_one]

/-- Each hat is `2n`-Lipschitz. -/
theorem abs_hat_sub_le (n : ℕ) (j k : ℤ) (x y : ℂ) : |hat n j k x - hat n j k y| ≤ 2 * n * dist x y := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hre : |((n : ℝ) * x.re - j) - ((n : ℝ) * y.re - j)| ≤ n * dist x y := by
    rw [show ((n : ℝ) * x.re - j) - ((n : ℝ) * y.re - j) = n * (x - y).re by simp only [Complex.sub_re]; ring,
      abs_mul, abs_of_nonneg hn, dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hn
  have him : |((n : ℝ) * x.im - k) - ((n : ℝ) * y.im - k)| ≤ n * dist x y := by
    rw [show ((n : ℝ) * x.im - k) - ((n : ℝ) * y.im - k) = n * (x - y).im by simp only [Complex.sub_im]; ring,
      abs_mul, abs_of_nonneg hn, dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) hn
  set a := hat1 ((n : ℝ) * x.re - j)
  set a' := hat1 ((n : ℝ) * y.re - j)
  set b := hat1 ((n : ℝ) * x.im - k)
  set b' := hat1 ((n : ℝ) * y.im - k)
  have ha := abs_hat1_sub_le ((n : ℝ) * x.re - j) ((n : ℝ) * y.re - j)
  have hb := abs_hat1_sub_le ((n : ℝ) * x.im - k) ((n : ℝ) * y.im - k)
  have hrw : hat n j k x - hat n j k y = a * (b - b') + b' * (a - a') := by
    simp only [hat, a, a', b, b']; ring
  rw [hrw]
  have ha0 : 0 ≤ a := hat1_nonneg _
  have ha1 : a ≤ 1 := hat1_le_one _
  have hb0 : 0 ≤ b' := hat1_nonneg _
  have hb1 : b' ≤ 1 := hat1_le_one _
  calc |a * (b - b') + b' * (a - a')| ≤ |a * (b - b')| + |b' * (a - a')| := abs_add_le _ _
    _ = a * |b - b'| + b' * |a - a'| := by rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hb0]
    _ ≤ 1 * |b - b'| + 1 * |a - a'| := by
        gcongr
    _ ≤ n * dist x y + n * dist x y := by linarith
    _ = 2 * n * dist x y := by ring

/-- Each hat is Lipschitz. -/
theorem lipschitzWith_hat (n : ℕ) (j k : ℤ) : LipschitzWith ⟨2 * n, by positivity⟩ (hat n j k) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq]
  exact abs_hat_sub_le n j k x y

theorem continuous_hat (n : ℕ) (j k : ℤ) : Continuous (hat n j k) := (lipschitzWith_hat n j k).continuous

/-- Each hat is Hölder continuous (Lipschitz) on every set. -/
theorem isHolderContinuousOn_hat (n : ℕ) (j k : ℤ) (s : Set ℂ) : IsHolderContinuousOn (hat n j k) s :=
  ⟨_, 1, one_pos, le_rfl, (lipschitzWith_hat n j k).holderWith.holderOnWith s⟩

end MatedCRT
