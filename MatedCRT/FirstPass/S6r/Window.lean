import MatedCRT.FirstPass.S6r.Constants

/-!
# S2 and S3: the dyadic scale, the short window and the three scale relations (fp-S6r)

Written argument: `notes/fp-gaps/CHATGPT-idla-6-8-redesign.md` §4 `S2_goodRadiusShortWindow` (lines 165-214) and
§5 `S3_scaleRelations` (lines 215-245).

* `dyadicD r` is the dyadic scale `d(r) = 2^{-⌊log₂(1/r²)⌋}` with `r² ≤ d(r) < 2r²` (S2.1).
* The short window of test radii is `[d, d^a]`, `a = shortExp ζ = (1+ζ)/2` (S2.2). `winSelect` is the first-good-radius
  choice among the seven-adic candidates `7^{-m}` of the short window (default `d`), the analogue of `firstGoodRadius`
  for the window. The prevalence statement (S2.3: some candidate is good, for all eligible `z`) is NOT proved here; it
  enters later as a named hypothesis on the `good` predicate, from the corrected good-annulus event (S1, z12) and
  GM Lemma 3.1 / printed 6.6.
* S3 (the three relations of §5): `r² ≤ R` (S3.1), `R ≤ 2 r^{1+ζ}` (S3.2), and `c₀R < r` (S3.3, under the deterministic
  cutoff `2 c₀ r^ζ < 1`, i.e. `r < (1/(2c₀))^{1/ζ}`).
-/

open Real Set

namespace MatedCRT
namespace Lemma68Window

/-- The dyadic scale `d(r) = 2^{-⌊log₂(1/r²)⌋}` of redesign S2.1: `r² ≤ d(r) < 2r²` for `0 < r ≤ 1`. -/
noncomputable def dyadicD (r : ℝ) : ℝ := (1 / 2 : ℝ) ^ Nat.log 2 ⌊1 / r ^ 2⌋₊

/-- For `x ≥ 1`: `1/x ≤ (1/2)^⌊log₂ ⌊x⌋⌋ < 2/x`. -/
lemma dyadic_bounds (x : ℝ) (hx : 1 ≤ x) :
    1 / x ≤ (1 / 2 : ℝ) ^ Nat.log 2 ⌊x⌋₊ ∧ (1 / 2 : ℝ) ^ Nat.log 2 ⌊x⌋₊ < 2 * (1 / x) := by
  have hx0 : 0 < x := by linarith
  have hN : ⌊x⌋₊ ≠ 0 := (Nat.floor_pos.mpr hx).ne'
  have h1 : (2 : ℕ) ^ Nat.log 2 ⌊x⌋₊ ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 hN
  have h1' : (2 : ℝ) ^ Nat.log 2 ⌊x⌋₊ ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
  have h1r : (2 : ℝ) ^ Nat.log 2 ⌊x⌋₊ ≤ x := h1'.trans (Nat.floor_le hx0.le)
  have h2 : ⌊x⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊x⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) ⌊x⌋₊
  have h2' : (⌊x⌋₊ : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log 2 ⌊x⌋₊ + 1) := by exact_mod_cast h2
  have h2r : x < (2 : ℝ) ^ (Nat.log 2 ⌊x⌋₊ + 1) := lt_of_lt_of_le (Nat.lt_floor_add_one x) h2'
  have hp : (0 : ℝ) < 2 ^ Nat.log 2 ⌊x⌋₊ := by positivity
  have e : (2 : ℝ) ^ (Nat.log 2 ⌊x⌋₊ + 1) = 2 * 2 ^ Nat.log 2 ⌊x⌋₊ := by ring
  constructor
  · rw [one_div_pow]
    exact one_div_le_one_div_of_le hp h1r
  · rw [one_div_pow, mul_one_div, div_lt_div_iff₀ hp hx0]
    rw [e] at h2r
    linarith

lemma dyadicD_pos (r : ℝ) : 0 < dyadicD r := by
  unfold dyadicD; positivity

lemma dyadicD_le_one (r : ℝ) : dyadicD r ≤ 1 := by
  unfold dyadicD; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma one_le_inv_sq {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : 1 ≤ 1 / r ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- (S2.1) `r² ≤ d(r)`. -/
lemma sq_le_dyadicD {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : r ^ 2 ≤ dyadicD r := by
  have h := (dyadic_bounds (1 / r ^ 2) (one_le_inv_sq hr hr1)).1
  rw [one_div_one_div] at h
  unfold dyadicD
  exact h

/-- (S2.1) `d(r) < 2r²`. -/
lemma dyadicD_lt_two_mul_sq {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : dyadicD r < 2 * r ^ 2 := by
  have h := (dyadic_bounds (1 / r ^ 2) (one_le_inv_sq hr hr1)).2
  rw [one_div_one_div] at h
  unfold dyadicD
  exact h

/-- The short window `[d, d^a]`, `a = shortExp ζ`, of redesign S2.2, as a predicate on `R` for the dyadic scale of `r`. -/
def InWindow (r ζ R : ℝ) : Prop := dyadicD r ≤ R ∧ R ≤ dyadicD r ^ shortExp ζ

/-- The lower seven-adic index `⌈a L / log 7⌉` of the short window, `L = -log d`. -/
noncomputable def winLo (d ζ : ℝ) : ℤ := ⌈shortExp ζ * (-Real.log d) / Real.log 7⌉

/-- The upper seven-adic index `⌊L / log 7⌋` of the short window. -/
noncomputable def winHi (d : ℝ) : ℤ := ⌊-Real.log d / Real.log 7⌋

/-- The seven-adic candidates `R_k = 7^{-(winLo + k)}` of the short window (S2.2). -/
noncomputable def winCand (d ζ : ℝ) (k : ℕ) : ℝ := (7 : ℝ) ^ (-(winLo d ζ + (k : ℤ)))

/-- The number of candidates `K(d) = winHi - winLo + 1` (S2.2). -/
noncomputable def winNum (d ζ : ℝ) : ℕ := (winHi d - winLo d ζ + 1).toNat

/-- Every candidate `k < winNum d ζ` lies in `[d, d^a]`. -/
lemma winCand_mem {d ζ : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) {k : ℕ}
    (hk : k < winNum d ζ) : d ≤ winCand d ζ k ∧ winCand d ζ k ≤ d ^ shortExp ζ := by
  have hlog7 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have hK : (k : ℤ) < winHi d - winLo d ζ + 1 := Int.lt_toNat.mp hk
  have hmHi : winLo d ζ + (k : ℤ) ≤ winHi d := by omega
  have hmLo : winLo d ζ ≤ winLo d ζ + (k : ℤ) := by omega
  have hHi : ((winLo d ζ + (k : ℤ) : ℤ) : ℝ) * Real.log 7 ≤ -Real.log d := by
    have h1 : (winHi d : ℝ) ≤ -Real.log d / Real.log 7 := Int.floor_le _
    have h2 : ((winLo d ζ + (k : ℤ) : ℤ) : ℝ) ≤ (winHi d : ℝ) := by exact_mod_cast hmHi
    have h3 := h2.trans h1
    rwa [le_div_iff₀ hlog7] at h3
  have hLo : shortExp ζ * (-Real.log d) ≤ ((winLo d ζ + (k : ℤ) : ℤ) : ℝ) * Real.log 7 := by
    have h1 : shortExp ζ * (-Real.log d) / Real.log 7 ≤ (winLo d ζ : ℝ) := Int.le_ceil _
    have h2 : (winLo d ζ : ℝ) ≤ ((winLo d ζ + (k : ℤ) : ℤ) : ℝ) := by exact_mod_cast hmLo
    have h3 := h1.trans h2
    rwa [div_le_iff₀ hlog7] at h3
  have hlogd : Real.log d ≤ 0 := Real.log_nonpos hd.le hd1
  unfold winCand
  push_cast at hHi hLo
  constructor
  · rw [← Real.log_le_log_iff hd (zpow_pos (by norm_num) _), Real.log_zpow]
    push_cast
    linarith
  · rw [← Real.log_le_log_iff (zpow_pos (by norm_num) _) (Real.rpow_pos_of_pos hd _),
      Real.log_zpow, Real.log_rpow hd]
    push_cast
    linarith

open Classical in
/-- The first-good-radius choice of the short window (S2.2–S2.3; the window analogue of `firstGoodRadius`): the
first candidate `winCand d ζ k` (`k < winNum d ζ`) whose good event `good k` holds, and the default `d` if none. -/
noncomputable def winSelect (d ζ : ℝ) (good : ℕ → Prop) : ℝ :=
  if h : ∃ k, k < winNum d ζ ∧ good k then winCand d ζ (Nat.find h) else d

open Classical in
/-- The window selection lies in `[d, d^a]`. -/
lemma winSelect_mem {d ζ : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hζ1 : ζ ≤ 1) (good : ℕ → Prop) :
    d ≤ winSelect d ζ good ∧ winSelect d ζ good ≤ d ^ shortExp ζ := by
  unfold winSelect
  split_ifs with h
  · exact winCand_mem hd hd1 (Nat.find_spec h).1
  · have hda : d ≤ d ^ shortExp ζ := by
      have := Real.rpow_le_rpow_of_exponent_ge hd hd1 (shortExp_le_one hζ1)
      rwa [Real.rpow_one] at this
    exact ⟨le_rfl, hda⟩

/-- (S3.1) `r² ≤ R` for every `R` in the short window of `r`. -/
lemma InWindow.sq_le {r ζ R : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (h : InWindow r ζ R) : r ^ 2 ≤ R :=
  (sq_le_dyadicD hr hr1).trans h.1

lemma InWindow.pos {r ζ R : ℝ} (h : InWindow r ζ R) : 0 < R :=
  (dyadicD_pos r).trans_le h.1

/-- `R ≤ 1` for `R` in the short window (since `d ≤ 1` and `a ≥ 0`). -/
lemma InWindow.le_one {r ζ R : ℝ} (hζ0 : 0 ≤ ζ) (h : InWindow r ζ R) : R ≤ 1 :=
  h.2.trans (Real.rpow_le_one (dyadicD_pos r).le (dyadicD_le_one r) (shortExp_nonneg hζ0))

/-- (S3.2) `R ≤ d^a < 2^a r^{1+ζ} ≤ 2 r^{1+ζ}` for `R` in the short window of `r`. -/
lemma InWindow.le_two_mul_rpow {r ζ R : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (h : InWindow r ζ R) : R ≤ 2 * r ^ (1 + ζ) := by
  have ha0 : 0 ≤ shortExp ζ := shortExp_nonneg hζ0
  have h1 : dyadicD r ^ shortExp ζ ≤ (2 * r ^ 2) ^ shortExp ζ :=
    Real.rpow_le_rpow (dyadicD_pos r).le (dyadicD_lt_two_mul_sq hr hr1).le ha0
  have e : ((2 : ℕ) : ℝ) * shortExp ζ = 1 + ζ := by
    unfold shortExp; push_cast; ring
  have h2 : (2 * r ^ 2) ^ shortExp ζ = 2 ^ shortExp ζ * r ^ (1 + ζ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, e]
  have h3 : (2 : ℝ) ^ shortExp ζ ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (shortExp_le_one hζ1)
    simpa using this
  have hpos : 0 ≤ r ^ (1 + ζ) := by positivity
  calc R ≤ dyadicD r ^ shortExp ζ := h.2
    _ ≤ (2 * r ^ 2) ^ shortExp ζ := h1
    _ = 2 ^ shortExp ζ * r ^ (1 + ζ) := h2
    _ ≤ 2 * r ^ (1 + ζ) := mul_le_mul_of_nonneg_right h3 hpos

/-- (S3.3) `c₀ R < r` once `R ≤ 2 r^{1+ζ}` and the deterministic cutoff `2 c₀ r^ζ < 1` holds. -/
lemma c0_mul_lt_of_le_two_mul_rpow {c0 ζ r R : ℝ} (hc0 : 0 < c0) (hr : 0 < r) (hcut : 2 * c0 * r ^ ζ < 1)
    (hR : R ≤ 2 * r ^ (1 + ζ)) : c0 * R < r := by
  have e : r ^ (1 + ζ) = r * r ^ ζ := by rw [Real.rpow_add hr, Real.rpow_one]
  calc c0 * R ≤ c0 * (2 * r ^ (1 + ζ)) := mul_le_mul_of_nonneg_left hR hc0.le
    _ = (2 * c0 * r ^ ζ) * r := by rw [e]; ring
    _ < 1 * r := mul_lt_mul_of_pos_right hcut hr
    _ = r := one_mul r

/-- The deterministic cutoff `r < r_*(c₀, ζ) = (1/(2c₀))^{1/ζ}` gives `2 c₀ r^ζ < 1` (S3.3). -/
lemma cutoff_of_lt {c0 ζ r : ℝ} (hc0 : 0 < c0) (hζ : 0 < ζ) (hr : 0 < r)
    (hlt : r < (1 / (2 * c0)) ^ (1 / ζ)) : 2 * c0 * r ^ ζ < 1 := by
  have h1 : r ^ ζ < ((1 / (2 * c0)) ^ (1 / ζ)) ^ ζ := Real.rpow_lt_rpow hr.le hlt hζ
  rw [one_div ζ, Real.rpow_inv_rpow (by positivity) hζ.ne'] at h1
  have h3 : 2 * c0 * (1 / (2 * c0)) = 1 := by field_simp
  calc 2 * c0 * r ^ ζ < 2 * c0 * (1 / (2 * c0)) := mul_lt_mul_of_pos_left h1 (by positivity)
    _ = 1 := h3

end Lemma68Window
end MatedCRT
