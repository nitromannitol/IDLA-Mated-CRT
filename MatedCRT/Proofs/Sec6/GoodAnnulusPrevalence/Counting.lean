import MatedCRT.Proofs.Sec6.AnnulusHit.Geometry

/-!
# Counting radii and grid points (proof of Lemma 6.4, lines 2387-2400)

For `δ ∈ (0, 1]` let `N = ⌊log₇ ⌊δ⁻¹⌋⌋` (`prevalenceLog`), so that `7^N ≤ δ⁻¹ < 7^{N+1}`. The radii of the proof of
Lemma 6.4 are `r_k = 7^{-(n₀ + 2k)}` with `n₀ = ⌊N/2⌋ + 1` (`prevalenceRadius`). Every `r_k` is at most `δ^{1/2}`,
and `r_k ≥ δ` for `1 ≤ k ≤ K = ⌊(N - n₀)/2⌋` (`prevalenceCount`). Consecutive radii have ratio `1/49`, as Lemma 6.6
needs. Since `4K + 5 ≥ N + 1`, `e^{-αK} ≤ 7^{25} δ^5` for `α = 20 log 7` (`exp_prevalenceCount_le`). The grid points
of `(δ/100) ℤ²` in `B_1` have coordinates in `[-⌊100/δ⌋, ⌊100/δ⌋]`: at most `(201/δ)²` of them.
-/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- `N(δ) = ⌊log₇ ⌊δ⁻¹⌋⌋`. -/
noncomputable def prevalenceLog (δ : ℝ) : ℕ := Nat.log 7 ⌊δ⁻¹⌋₊

/-- The first exponent `n₀ = ⌊N/2⌋ + 1`. -/
noncomputable def prevalenceStart (δ : ℝ) : ℕ := prevalenceLog δ / 2 + 1

/-- The number `K = ⌊(N - n₀)/2⌋` of radii used in Lemma 6.6. -/
noncomputable def prevalenceCount (δ : ℝ) : ℕ := (prevalenceLog δ - prevalenceStart δ) / 2

/-- The radii `r_k = 7^{-(n₀ + 2k)}`. -/
noncomputable def prevalenceRadius (δ : ℝ) (k : ℕ) : ℝ := (7 : ℝ)⁻¹ ^ (prevalenceStart δ + 2 * k)

theorem pow_prevalenceLog_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : (7 : ℝ) ^ prevalenceLog δ ≤ δ⁻¹ := by
  have h1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδ1
  have hfl : ⌊δ⁻¹⌋₊ ≠ 0 := (Nat.floor_pos.2 h1).ne'
  have h : (7 : ℝ) ^ prevalenceLog δ ≤ (⌊δ⁻¹⌋₊ : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 7 hfl
  exact h.trans (Nat.floor_le (by positivity))

theorem lt_pow_prevalenceLog_succ (δ : ℝ) : δ⁻¹ < (7 : ℝ) ^ (prevalenceLog δ + 1) := by
  have h1 : ⌊δ⁻¹⌋₊ < 7 ^ (prevalenceLog δ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : (⌊δ⁻¹⌋₊ : ℝ) + 1 ≤ (7 : ℝ) ^ (prevalenceLog δ + 1) := by
    exact_mod_cast Nat.succ_le_of_lt h1
  linarith [Nat.lt_floor_add_one δ⁻¹]

theorem prevalenceRadius_pos (δ : ℝ) (k : ℕ) : 0 < prevalenceRadius δ k := by
  unfold prevalenceRadius; positivity

theorem prevalenceRadius_eq (δ : ℝ) (k : ℕ) :
    prevalenceRadius δ k = ((7 : ℝ) ^ (prevalenceStart δ + 2 * k))⁻¹ := by
  unfold prevalenceRadius; rw [inv_pow]

theorem prevalenceRadius_succ (δ : ℝ) (k : ℕ) : prevalenceRadius δ (k + 1) = prevalenceRadius δ k / 49 := by
  unfold prevalenceRadius
  rw [show prevalenceStart δ + 2 * (k + 1) = (prevalenceStart δ + 2 * k) + 2 by ring, pow_add]
  norm_num [div_eq_mul_inv]

theorem prevalenceRadius_le_sqrt {δ : ℝ} (hδ : 0 < δ) (k : ℕ) : prevalenceRadius δ k ≤ Real.sqrt δ := by
  have hpos := prevalenceRadius_pos δ k
  have hN := lt_pow_prevalenceLog_succ δ
  have hexp : prevalenceLog δ + 1 ≤ (prevalenceStart δ + 2 * k) * 2 := by
    unfold prevalenceStart; omega
  have hsq : prevalenceRadius δ k ^ 2 ≤ δ := by
    rw [prevalenceRadius_eq, inv_pow, ← pow_mul]
    have h7 : (7 : ℝ) ^ (prevalenceLog δ + 1) ≤ 7 ^ ((prevalenceStart δ + 2 * k) * 2) :=
      pow_le_pow_right₀ (by norm_num) hexp
    have h8 : δ⁻¹ ≤ (7 : ℝ) ^ ((prevalenceStart δ + 2 * k) * 2) := hN.le.trans h7
    calc ((7 : ℝ) ^ ((prevalenceStart δ + 2 * k) * 2))⁻¹ ≤ (δ⁻¹)⁻¹ := inv_anti₀ (by positivity) h8
      _ = δ := inv_inv δ
  rw [← Real.sqrt_sq hpos.le]
  exact Real.sqrt_le_sqrt hsq

theorem le_prevalenceRadius {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ prevalenceCount δ) : δ ≤ prevalenceRadius δ k := by
  have hexp : prevalenceStart δ + 2 * k ≤ prevalenceLog δ := by
    unfold prevalenceCount at hk; omega
  rw [prevalenceRadius_eq]
  have h7 : (7 : ℝ) ^ (prevalenceStart δ + 2 * k) ≤ δ⁻¹ :=
    (pow_le_pow_right₀ (by norm_num) hexp).trans (pow_prevalenceLog_le hδ hδ1)
  calc δ = (δ⁻¹)⁻¹ := (inv_inv δ).symm
    _ ≤ ((7 : ℝ) ^ (prevalenceStart δ + 2 * k))⁻¹ := inv_anti₀ (by positivity) h7

/-- `e^{-αK} ≤ 7^{25} δ^5` for `α = 20 log 7`. -/
theorem exp_prevalenceCount_le {δ : ℝ} (hδ : 0 < δ) :
    Real.exp (-(20 * Real.log 7) * prevalenceCount δ) ≤ 7 ^ 25 * δ ^ 5 := by
  have hK : prevalenceLog δ + 1 ≤ 4 * prevalenceCount δ + 5 := by
    unfold prevalenceCount prevalenceStart; omega
  have hexp : Real.exp (-(20 * Real.log 7) * prevalenceCount δ) = ((7 : ℝ) ^ (20 * prevalenceCount δ))⁻¹ := by
    rw [show -(20 * Real.log 7) * (prevalenceCount δ : ℝ) =
        -(((20 * prevalenceCount δ : ℕ) : ℝ) * Real.log 7) by push_cast; ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h1 : δ⁻¹ ≤ (7 : ℝ) ^ (4 * prevalenceCount δ + 5) :=
    (lt_pow_prevalenceLog_succ δ).le.trans (pow_le_pow_right₀ (by norm_num) hK)
  have h2 : (δ⁻¹) ^ 5 ≤ ((7 : ℝ) ^ (4 * prevalenceCount δ + 5)) ^ 5 := pow_le_pow_left₀ (by positivity) h1 5
  have h3 : ((7 : ℝ) ^ (4 * prevalenceCount δ + 5)) ^ 5 = 7 ^ (20 * prevalenceCount δ) * 7 ^ 25 := by ring
  rw [h3, inv_pow] at h2
  have h4 : (0 : ℝ) < 7 ^ (20 * prevalenceCount δ) := by positivity
  have h5 : 1 ≤ (7 : ℝ) ^ (20 * prevalenceCount δ) * (7 ^ 25 * δ ^ 5) := by
    have h6 := mul_le_mul_of_nonneg_left h2 (pow_pos hδ 5).le
    rw [mul_inv_cancel₀ (pow_pos hδ 5).ne'] at h6
    calc (1 : ℝ) ≤ δ ^ 5 * (7 ^ (20 * prevalenceCount δ) * 7 ^ 25) := h6
      _ = 7 ^ (20 * prevalenceCount δ) * (7 ^ 25 * δ ^ 5) := by ring
  rw [hexp]
  calc ((7 : ℝ) ^ (20 * prevalenceCount δ))⁻¹ = ((7 : ℝ) ^ (20 * prevalenceCount δ))⁻¹ * 1 := (mul_one _).symm
    _ ≤ ((7 : ℝ) ^ (20 * prevalenceCount δ))⁻¹ * (7 ^ (20 * prevalenceCount δ) * (7 ^ 25 * δ ^ 5)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = 7 ^ 25 * δ ^ 5 := inv_mul_cancel_left₀ h4.ne' _

/-- The grid points of `(δ/100) ℤ²` in `B_1` have coordinates in `[-⌊100/δ⌋, ⌊100/δ⌋]`. -/
theorem grid_mem_Icc {δ : ℝ} (hδ : 0 < δ) {m n : ℤ} (hz : ‖((δ / 100 : ℝ) : ℂ) * (m + n * Complex.I)‖ < 1) :
    m ∈ Finset.Icc (-(⌊100 / δ⌋₊ : ℤ)) ⌊100 / δ⌋₊ ∧ n ∈ Finset.Icc (-(⌊100 / δ⌋₊ : ℤ)) ⌊100 / δ⌋₊ := by
  set z : ℂ := ((δ / 100 : ℝ) : ℂ) * (m + n * Complex.I) with hzdef
  have hre : z.re = δ / 100 * m := by rw [hzdef]; simp
  have him : z.im = δ / 100 * n := by rw [hzdef]; simp
  have key : ∀ j : ℤ, |δ / 100 * j| < 1 → j ∈ Finset.Icc (-(⌊100 / δ⌋₊ : ℤ)) ⌊100 / δ⌋₊ := by
    intro j hj
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < δ / 100)] at hj
    have hj' : |(j : ℝ)| < 100 / δ := by rw [lt_div_iff₀ hδ]; linarith
    have hfl := Nat.lt_floor_add_one (100 / δ)
    have h1 : (j : ℝ) < (⌊100 / δ⌋₊ : ℝ) + 1 := by linarith [le_abs_self (j : ℝ)]
    have h2 : -(j : ℝ) < (⌊100 / δ⌋₊ : ℝ) + 1 := by linarith [neg_abs_le (j : ℝ)]
    have h1' : j < (⌊100 / δ⌋₊ : ℤ) + 1 := by exact_mod_cast h1
    have h2' : -j < (⌊100 / δ⌋₊ : ℤ) + 1 := by exact_mod_cast h2
    rw [Finset.mem_Icc]
    constructor <;> omega
  refine ⟨key m ?_, key n ?_⟩
  · rw [← hre]; exact (Complex.abs_re_le_norm z).trans_lt hz
  · rw [← him]; exact (Complex.abs_im_le_norm z).trans_lt hz

/-- The number of grid points with coordinates in `[-M, M]`. -/
theorem card_grid (M : ℕ) :
    ((Finset.Icc (-(M : ℤ)) M) ×ˢ (Finset.Icc (-(M : ℤ)) M)).card = (2 * M + 1) ^ 2 := by
  rw [Finset.card_product, Int.card_Icc]
  have : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
  rw [this, sq]

/-- Outer probability of an event from that of its complement. -/
theorem ofReal_le_measure_of_compl_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : Set Ω} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (h : P Sᶜ ≤ ENNReal.ofReal (1 - p)) : ENNReal.ofReal p ≤ P S := by
  have h1 : (1 : ℝ≥0∞) ≤ P S + P Sᶜ := by
    rw [← measure_univ (μ := P), ← union_compl_self S]
    exact measure_union_le _ _
  have h2 : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
    rw [← ENNReal.ofReal_add hp (by linarith), show p + (1 - p) = 1 by ring, ENNReal.ofReal_one]
  refine ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top (a := ENNReal.ofReal (1 - p)) ?_
  rw [h2]
  exact h1.trans (by gcongr)

end MatedCRT
