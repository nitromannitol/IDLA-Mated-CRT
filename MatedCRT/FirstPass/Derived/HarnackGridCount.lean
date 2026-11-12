import MatedCRT.FirstPass.Derived.HarnackRingGeometry

/-!
# Counting the grid circles of the Harnack inequality

The union bound of Berestycki–Gwynne (2020), Lemma 3.11, runs over the grid circles `∂B_{s'}(z')` with
`z' = h (m + n i) ∈ B_1` and `s' = (√2)^a ∈ [s₀, 1]`.  These indices lie in a box of cardinality at most
`(2/h + 3)² (3/s₀ + 2)`; for `h = ε^{2β}` and `s₀ = ε^β` this is at most `125 ε^{-5β}`.
-/

set_option autoImplicit false

namespace MatedCRT

open Set

/-- The box of indices `(m, n, a)` containing all grid circles with centre of norm at most `1` and radius in `[s₀, 1]`. -/
noncomputable def gridIndexBox (h s₀ : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  Finset.Icc (-⌈1 / h⌉) ⌈1 / h⌉ ×ˢ Finset.Icc (-⌈1 / h⌉) ⌈1 / h⌉ ×ˢ Finset.Icc (-⌈3 / s₀⌉) 0

theorem one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem seven_fifths_le_sqrt_two : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
  rw [show (7 / 5 : ℝ) = Real.sqrt ((7 / 5) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- A radius `(√2)^a ≤ 1` has `a ≤ 0`. -/
theorem nonpos_of_sqrt2Pow_le_one {a : ℤ} (ha : sqrt2Pow a ≤ 1) : a ≤ 0 := by
  by_contra hpos
  push Not at hpos
  exact absurd ha (not_le.2 (one_lt_zpow₀ one_lt_sqrt_two hpos))

/-- A radius `(√2)^a ≥ s₀` with `a ≤ 0` has `-a ≤ ⌈3/s₀⌉`. -/
theorem neg_le_ceil_of_le_sqrt2Pow {s₀ : ℝ} (hs₀ : 0 < s₀) {a : ℤ} (ha0 : a ≤ 0) (ha : s₀ ≤ sqrt2Pow a) :
    -a ≤ ⌈3 / s₀⌉ := by
  obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat ha0
  unfold sqrt2Pow at ha
  rw [zpow_neg, zpow_natCast] at ha
  have hpos : 0 < Real.sqrt 2 ^ n := pow_pos (by linarith [one_lt_sqrt_two]) n
  have h1 : Real.sqrt 2 ^ n ≤ 1 / s₀ := by
    rw [le_div_iff₀ hs₀]
    calc Real.sqrt 2 ^ n * s₀ ≤ Real.sqrt 2 ^ n * (Real.sqrt 2 ^ n)⁻¹ :=
          mul_le_mul_of_nonneg_left ha hpos.le
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  have h2 : 1 + (n : ℝ) * (Real.sqrt 2 - 1) ≤ Real.sqrt 2 ^ n := by
    have := one_add_mul_le_pow (a := Real.sqrt 2 - 1) (by linarith [one_lt_sqrt_two]) n
    simpa using this
  have h3 : (n : ℝ) * (2 / 5) ≤ 1 / s₀ := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [seven_fifths_le_sqrt_two]
  have h4 : (n : ℝ) ≤ 3 / s₀ := by
    have : (1 : ℝ) / s₀ * 3 = 3 / s₀ := by ring
    have h5 : (0 : ℝ) ≤ 1 / s₀ := by positivity
    nlinarith
  have h6 : ((n : ℤ) : ℝ) ≤ (⌈3 / s₀⌉ : ℝ) := by
    rw [Int.cast_natCast]
    exact h4.trans (Int.le_ceil _)
  rw [neg_neg]
  exact_mod_cast h6

/-- The real and imaginary parts of the lattice point `h (m + n i)` are `h m` and `h n`. -/
theorem abs_le_of_norm_latticePt_le {h : ℝ} (hh : 0 < h) {m n : ℤ} {R : ℝ}
    (hR : ‖latticePt h m n‖ ≤ R) : |(m : ℝ)| ≤ R / h ∧ |(n : ℝ)| ≤ R / h := by
  have hre : (latticePt h m n).re = h * m := by simp [latticePt]
  have him : (latticePt h m n).im = h * n := by simp [latticePt]
  have h1 := Complex.abs_re_le_norm (latticePt h m n)
  have h2 := Complex.abs_im_le_norm (latticePt h m n)
  rw [hre, abs_mul, abs_of_pos hh] at h1
  rw [him, abs_mul, abs_of_pos hh] at h2
  exact ⟨by rw [le_div_iff₀ hh]; linarith, by rw [le_div_iff₀ hh]; linarith⟩

/-- Every grid index with centre in the closed unit disc and radius in `[s₀, 1]` lies in the box. -/
theorem mem_gridIndexBox {h s₀ : ℝ} (hh : 0 < h) (hs₀ : 0 < s₀) {m n a : ℤ}
    (hz : ‖latticePt h m n‖ ≤ 1) (hs : s₀ ≤ sqrt2Pow a) (hs1 : sqrt2Pow a ≤ 1) :
    (m, n, a) ∈ gridIndexBox h s₀ := by
  obtain ⟨hm, hn⟩ := abs_le_of_norm_latticePt_le hh hz
  have hce : (1 : ℝ) / h ≤ (⌈1 / h⌉ : ℝ) := Int.le_ceil _
  rw [abs_le] at hm hn
  have ha0 := nonpos_of_sqrt2Pow_le_one hs1
  have ha := neg_le_ceil_of_le_sqrt2Pow hs₀ ha0 hs
  simp only [gridIndexBox, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨by omega, ha0⟩⟩
  · have : (-(⌈1 / h⌉ : ℤ) : ℝ) ≤ m := by linarith [hm.1]
    exact_mod_cast this
  · have : (m : ℝ) ≤ (⌈1 / h⌉ : ℤ) := by linarith [hm.2]
    exact_mod_cast this
  · have : (-(⌈1 / h⌉ : ℤ) : ℝ) ≤ n := by linarith [hn.1]
    exact_mod_cast this
  · have : (n : ℝ) ≤ (⌈1 / h⌉ : ℤ) := by linarith [hn.2]
    exact_mod_cast this

theorem card_Icc_cast_le (a b : ℤ) (hab : a ≤ b + 1) :
    ((Finset.Icc a b).card : ℝ) ≤ (b : ℝ) + 1 - a := by
  have h1 : (((b + 1 - a).toNat : ℕ) : ℤ) = b + 1 - a := Int.toNat_of_nonneg (by omega)
  have h2 : (((Finset.Icc a b).card : ℕ) : ℤ) = b + 1 - a := by rw [Int.card_Icc, h1]
  have h3 := congrArg (Int.cast : ℤ → ℝ) h2
  push_cast at h3
  linarith

/-- The box has at most `(2/h + 3)² (3/s₀ + 2)` elements. -/
theorem card_gridIndexBox_le {h s₀ : ℝ} (hh : 0 < h) (hs₀ : 0 < s₀) :
    ((gridIndexBox h s₀).card : ℝ) ≤ (2 / h + 3) ^ 2 * (3 / s₀ + 2) := by
  have hN : 0 ≤ ⌈1 / h⌉ := Int.ceil_nonneg (by positivity)
  have hA : 0 ≤ ⌈3 / s₀⌉ := Int.ceil_nonneg (by positivity)
  have hc1 : ((Finset.Icc (-⌈1 / h⌉) ⌈1 / h⌉).card : ℝ) ≤ 2 / h + 3 := by
    have := card_Icc_cast_le (-⌈1 / h⌉) ⌈1 / h⌉ (by omega)
    have h2 : (⌈1 / h⌉ : ℝ) < 1 / h + 1 := Int.ceil_lt_add_one _
    push_cast at this
    have : (2 : ℝ) / h = 2 * (1 / h) := by ring
    linarith
  have hc3 : ((Finset.Icc (-⌈3 / s₀⌉) 0).card : ℝ) ≤ 3 / s₀ + 2 := by
    have := card_Icc_cast_le (-⌈3 / s₀⌉) 0 (by omega)
    have h2 : (⌈3 / s₀⌉ : ℝ) < 3 / s₀ + 1 := Int.ceil_lt_add_one _
    push_cast at this
    linarith
  unfold gridIndexBox
  rw [Finset.card_product, Finset.card_product]
  push_cast
  have h0 : (0 : ℝ) ≤ ((Finset.Icc (-⌈1 / h⌉) ⌈1 / h⌉).card : ℝ) := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ ((Finset.Icc (-⌈3 / s₀⌉) 0).card : ℝ) := Nat.cast_nonneg _
  calc ((Finset.Icc (-⌈1 / h⌉) ⌈1 / h⌉).card : ℝ) *
        (((Finset.Icc (-⌈1 / h⌉) ⌈1 / h⌉).card : ℝ) * ((Finset.Icc (-⌈3 / s₀⌉) 0).card : ℝ))
      ≤ (2 / h + 3) * ((2 / h + 3) * (3 / s₀ + 2)) := by gcongr
    _ = (2 / h + 3) ^ 2 * (3 / s₀ + 2) := by ring

/-- For `h = ε^{2β}` and `s₀ = ε^β` the box has at most `125 ε^{-5β}` elements. -/
theorem card_gridIndexBox_rpow_le {β ε : ℝ} (hβ : 0 < β) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ((gridIndexBox (ε ^ (2 * β)) (ε ^ β)).card : ℝ) ≤ 125 * ε ^ (-(5 * β)) := by
  have hh : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε0 _
  have hs : 0 < ε ^ β := Real.rpow_pos_of_pos hε0 _
  have hY1 : 1 ≤ ε ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε1.le (by linarith)
  have hinv : (ε ^ β)⁻¹ = ε ^ (-β) := (Real.rpow_neg hε0.le β).symm
  have hY2 : (ε ^ (-β)) ^ 2 = (ε ^ (2 * β))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le, ← Real.rpow_neg hε0.le]
    congr 1
    push_cast
    ring
  have hY5 : (ε ^ (-β)) ^ 5 = ε ^ (-(5 * β)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le]
    congr 1
    push_cast
    ring
  have h1 : 2 / ε ^ (2 * β) + 3 ≤ 5 * (ε ^ (-β)) ^ 2 := by
    rw [hY2]
    have : 1 ≤ (ε ^ (2 * β))⁻¹ := by
      rw [← hY2]; nlinarith
    rw [div_eq_mul_inv]
    linarith
  have h2 : 3 / ε ^ β + 2 ≤ 5 * ε ^ (-β) := by
    rw [div_eq_mul_inv, hinv]
    linarith
  refine (card_gridIndexBox_le hh hs).trans ?_
  have hp : (0 : ℝ) ≤ 2 / ε ^ (2 * β) + 3 := by positivity
  calc (2 / ε ^ (2 * β) + 3) ^ 2 * (3 / ε ^ β + 2)
      ≤ (5 * (ε ^ (-β)) ^ 2) ^ 2 * (5 * ε ^ (-β)) := by gcongr
    _ = 125 * (ε ^ (-β)) ^ 5 := by ring
    _ = 125 * ε ^ (-(5 * β)) := by rw [hY5]

end MatedCRT
