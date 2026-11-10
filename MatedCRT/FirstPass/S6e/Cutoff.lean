import Mathlib
import MatedCRT.FirstPass.S4S6c.AmplCutoff

/-!
# FIRST PASS: the explicit cutoffs of LEMMA68 section D (D1, D3, D4) (task fp-S6e-lemma68-D123, z9)

Source: `notes/fp-gaps/CHATGPT-lemma68-open-parts.md`, section D (lines 887-955), with the parameters of its
section 1 (`ζ = p/2 - 1`, `λ = 2β⁻ - p b`, `c_v = 4^(-b)`, `c_0`), `q0 = q_*/9` (C16), `c = q0/200` (D1),
`s = √δ` and `N = ⌊r/(100 s)⌋` (C1, C3). Pure real analysis: the probability enters only through
`(1 - q(r))^N` (C17), which is `D1_real`. The amplification estimate `exp(-c r^(-ζ)/(1+log(1/r))²) ≤ 1/2` is
`MatedCRT.AmplCutoff.amplification_cutoff` (q2, FirstPass/S4S6c/AmplCutoff.lean).

Hypothesis not stated in the write-up: `q0 ≤ 1` (needed for `1 - q(r) ≥ 0` in (C17)); it is an explicit
argument of `D1_real` and `D1_le_half`.
-/

open Real MeasureTheory

namespace MatedCRT

namespace Lemma68Cutoff

/-- The amplification radius `r_amp = min {1, (c ζ²/(16 log 2))^(2/ζ)}` of (D2), with `c = q0/200`. -/
noncomputable def rAmp (q0 ζ : ℝ) : ℝ :=
  min 1 ((q0 / 200 * ζ ^ 2 / (16 * Real.log 2)) ^ (2 / ζ))

/-- The minimum inside the simultaneous deterministic cutoff of (D3), before the factor `1/2`. -/
noncomputable def r0Min (ρ s₀ p b lam cv c0 q0 ζ : ℝ) : ℝ :=
  min (min (min (min (min (1 / 2) (ρ / 100)) ((1000 : ℝ) ^ (-1 / ζ))) ((s₀ / 80) ^ (2 / p)))
    ((2 ^ (-b) * cv * c0 ^ b) ^ (1 / lam))) (rAmp q0 ζ)

/-- The simultaneous deterministic cutoff of (D3):
`r0 = ½ min {½, ρ/100, 1000^(-1/ζ), (s₀/80)^(2/p), (2^(-b) c_v c_0^b)^(1/λ), r_amp}`. -/
noncomputable def r0 (ρ s₀ p b lam cv c0 q0 ζ : ℝ) : ℝ :=
  1 / 2 * r0Min ρ s₀ p b lam cv c0 q0 ζ

theorem rAmp_pos {q0 ζ : ℝ} (hq0 : 0 < q0) (hζ : 0 < ζ) : 0 < rAmp q0 ζ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX : 0 < q0 / 200 * ζ ^ 2 / (16 * Real.log 2) :=
    div_pos (mul_pos (div_pos hq0 (by norm_num)) (pow_pos hζ 2)) (mul_pos (by norm_num) hl2)
  exact lt_min one_pos (Real.rpow_pos_of_pos hX _)

section R0

variable {ρ s₀ p b lam cv c0 q0 ζ : ℝ}

theorem r0Min_pos (hρ : 0 < ρ) (hs₀ : 0 < s₀) (hcv : 0 < cv) (hc0 : 0 < c0) (hq0 : 0 < q0) (hζ : 0 < ζ) :
    0 < r0Min ρ s₀ p b lam cv c0 q0 ζ := by
  unfold r0Min
  have hA : (0 : ℝ) < 1 / 2 := by norm_num
  have hB : 0 < ρ / 100 := div_pos hρ (by norm_num)
  have hC : (0 : ℝ) < (1000 : ℝ) ^ (-1 / ζ) := Real.rpow_pos_of_pos (by norm_num) _
  have hD : 0 < (s₀ / 80) ^ (2 / p) := Real.rpow_pos_of_pos (div_pos hs₀ (by norm_num)) _
  have hE : 0 < (2 ^ (-b) * cv * c0 ^ b) ^ (1 / lam) :=
    Real.rpow_pos_of_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hcv)
      (Real.rpow_pos_of_pos hc0 _)) _
  exact lt_min (lt_min (lt_min (lt_min (lt_min hA hB) hC) hD) hE) (rAmp_pos hq0 hζ)

theorem r0_le_r0Min (hρ : 0 < ρ) (hs₀ : 0 < s₀) (hcv : 0 < cv) (hc0 : 0 < c0) (hq0 : 0 < q0) (hζ : 0 < ζ) :
    r0 ρ s₀ p b lam cv c0 q0 ζ ≤ r0Min ρ s₀ p b lam cv c0 q0 ζ := by
  have := r0Min_pos (p := p) (b := b) (lam := lam) hρ hs₀ hcv hc0 hq0 hζ
  unfold r0
  linarith

theorem r0Min_le_rho : r0Min ρ s₀ p b lam cv c0 q0 ζ ≤ ρ / 100 := by
  unfold r0Min
  simp [min_le_iff]

theorem r0Min_le_zeta : r0Min ρ s₀ p b lam cv c0 q0 ζ ≤ (1000 : ℝ) ^ (-1 / ζ) := by
  unfold r0Min
  simp [min_le_iff]

theorem r0Min_le_s0 : r0Min ρ s₀ p b lam cv c0 q0 ζ ≤ (s₀ / 80) ^ (2 / p) := by
  unfold r0Min
  simp [min_le_iff]

theorem r0Min_le_B : r0Min ρ s₀ p b lam cv c0 q0 ζ ≤ (2 ^ (-b) * cv * c0 ^ b) ^ (1 / lam) := by
  unfold r0Min
  simp [min_le_iff]

theorem r0Min_le_rAmp : r0Min ρ s₀ p b lam cv c0 q0 ζ ≤ rAmp q0 ζ := by
  unfold r0Min
  exact min_le_right _ _

/-- (D3, for the dd-bound `dd ≤ ρ/100` of the choice of `dd`, q2's item O6) -/
theorem r0_le_rho_div (hρ : 0 < ρ) (hs₀ : 0 < s₀) (hcv : 0 < cv) (hc0 : 0 < c0) (hq0 : 0 < q0)
    (hζ : 0 < ζ) : r0 ρ s₀ p b lam cv c0 q0 ζ ≤ ρ / 100 :=
  (r0_le_r0Min hρ hs₀ hcv hc0 hq0 hζ).trans r0Min_le_rho

/-- (D3) `r0 ≤ r_amp`, the amplification radius of (D2). -/
theorem r0_le_rAmp (hρ : 0 < ρ) (hs₀ : 0 < s₀) (hcv : 0 < cv) (hc0 : 0 < c0) (hq0 : 0 < q0)
    (hζ : 0 < ζ) : r0 ρ s₀ p b lam cv c0 q0 ζ ≤ rAmp q0 ζ :=
  (r0_le_r0Min hρ hs₀ hcv hc0 hq0 hζ).trans r0Min_le_rAmp

/-- (D3, first consequence) `r ≤ r0` gives `r^ζ ≤ 1/1000`, the numerical form of `s ≤ r/1000` for `s ≤ r^(1+ζ)`. -/
theorem rpow_zeta_le_of_le_r0 (hρ : 0 < ρ) (hs₀ : 0 < s₀) (hcv : 0 < cv) (hc0 : 0 < c0) (hq0 : 0 < q0)
    (hζ : 0 < ζ) {r : ℝ} (hr : 0 < r) (h : r ≤ r0 ρ s₀ p b lam cv c0 q0 ζ) : r ^ ζ ≤ 1 / 1000 := by
  have h1 : r ≤ (1000 : ℝ) ^ (-1 / ζ) :=
    h.trans ((r0_le_r0Min hρ hs₀ hcv hc0 hq0 hζ).trans r0Min_le_zeta)
  calc r ^ ζ ≤ ((1000 : ℝ) ^ (-1 / ζ)) ^ ζ := Real.rpow_le_rpow hr.le h1 hζ.le
    _ = 1 / 1000 := by
      have hζ0 : ζ ≠ 0 := hζ.ne'
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1000)]
      have e : -1 / ζ * ζ = -1 := by field_simp
      rw [e, Real.rpow_neg_one]
      norm_num

/-- (D3, second consequence, the inequality (B4)): `r ≤ r0` gives `2^b r^λ ≤ c_v c_0^b`. -/
theorem two_rpow_mul_le_of_le_r0 (hρ : 0 < ρ) (hs₀ : 0 < s₀) (hcv : 0 < cv) (hc0 : 0 < c0) (hq0 : 0 < q0)
    (hζ : 0 < ζ) (hlam : 0 < lam) {r : ℝ} (hr : 0 < r) (h : r ≤ r0 ρ s₀ p b lam cv c0 q0 ζ) :
    (2 : ℝ) ^ b * r ^ lam ≤ cv * c0 ^ b := by
  have hX : 0 < 2 ^ (-b) * cv * c0 ^ b :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hcv) (Real.rpow_pos_of_pos hc0 _)
  have h1 : r ≤ (2 ^ (-b) * cv * c0 ^ b) ^ (1 / lam) :=
    h.trans ((r0_le_r0Min hρ hs₀ hcv hc0 hq0 hζ).trans r0Min_le_B)
  have h2 : r ^ lam ≤ 2 ^ (-b) * cv * c0 ^ b := by
    calc r ^ lam ≤ ((2 ^ (-b) * cv * c0 ^ b) ^ (1 / lam)) ^ lam := Real.rpow_le_rpow hr.le h1 hlam.le
      _ = 2 ^ (-b) * cv * c0 ^ b := by
        rw [← Real.rpow_mul hX.le, one_div_mul_cancel hlam.ne', Real.rpow_one]
  have h3 : (2 : ℝ) ^ (-b) = ((2 : ℝ) ^ b)⁻¹ := Real.rpow_neg (by norm_num) b
  have h4 : (0 : ℝ) < 2 ^ b := Real.rpow_pos_of_pos (by norm_num) b
  have h4' : (2 : ℝ) ^ b ≠ 0 := h4.ne'
  calc (2 : ℝ) ^ b * r ^ lam ≤ 2 ^ b * (2 ^ (-b) * cv * c0 ^ b) := mul_le_mul_of_nonneg_left h2 h4.le
    _ = cv * c0 ^ b := by rw [h3]; field_simp

end R0

/-- (N-bound, C1 and C3) with `s ≤ r/1000` and `s ≤ r^(1+ζ)`, the count `N = ⌊r/(100 s)⌋` satisfies
`r^(-ζ)/200 ≤ N`. -/
theorem N_lower_bound {r s ζ : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r / 1000)
    (hsζ : s ≤ r ^ (1 + ζ)) : r ^ (-ζ) / 200 ≤ (⌊r / (100 * s)⌋₊ : ℝ) := by
  have hrz : 0 < r ^ ζ := Real.rpow_pos_of_pos hr ζ
  have hpow : r ^ (1 + ζ) = r * r ^ ζ := by rw [Real.rpow_add hr, Real.rpow_one]
  have key : s ≤ r * r ^ ζ := by rw [← hpow]; exact hsζ
  have hneg : r ^ (-ζ) = (r ^ ζ)⁻¹ := Real.rpow_neg hr.le ζ
  have hx10 : 10 ≤ r / (100 * s) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hfl : r / (100 * s) - 1 < (⌊r / (100 * s)⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (r / (100 * s))
    linarith
  have e1 : r / (100 * s) / 2 = r / (200 * s) := by ring
  have e2 : r / (200 * s) = (r / s) / 200 := by ring
  have hy : (r ^ ζ)⁻¹ ≤ r / s := by
    rw [inv_eq_one_div, div_le_div_iff₀ hrz hs]
    nlinarith [key]
  have hA : (r ^ ζ)⁻¹ / 200 ≤ r / (100 * s) / 2 := by
    rw [e1, e2]
    linarith
  rw [hneg]
  linarith

/-- (D1, C17 and C16) For `0 ≤ q0 ≤ 1`, `r ∈ (0, 1]` and `N ≥ r^(-ζ)/200`:
`(1 - q(r))^N ≤ exp(-(q0/200) r^(-ζ)/(1+log(1/r))²)` with `q(r) = q0/(1+log(1/r))²`. -/
theorem D1_real {q0 r ζ : ℝ} {N : ℕ} (hq0 : 0 ≤ q0) (hq1 : q0 ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hN : r ^ (-ζ) / 200 ≤ (N : ℝ)) :
    (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N ≤
      Real.exp (-(q0 / 200 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2)) := by
  have hl : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have hden : 1 ≤ (1 + Real.log (1 / r)) ^ 2 := by nlinarith
  have hq0' : 0 ≤ q0 / (1 + Real.log (1 / r)) ^ 2 := div_nonneg hq0 (by positivity)
  have hqq0 : q0 / (1 + Real.log (1 / r)) ^ 2 ≤ q0 := div_le_self hq0 hden
  have hkey : q0 / 200 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2 =
      r ^ (-ζ) / 200 * (q0 / (1 + Real.log (1 / r)) ^ 2) := by ring
  have h1 : 1 - q0 / (1 + Real.log (1 / r)) ^ 2 ≤ Real.exp (-(q0 / (1 + Real.log (1 / r)) ^ 2)) := by
    linarith [Real.add_one_le_exp (-(q0 / (1 + Real.log (1 / r)) ^ 2))]
  have hA : 0 ≤ 1 - q0 / (1 + Real.log (1 / r)) ^ 2 := by linarith
  rw [hkey]
  calc (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N
      ≤ (Real.exp (-(q0 / (1 + Real.log (1 / r)) ^ 2))) ^ N := pow_le_pow_left₀ hA h1 N
    _ = Real.exp (N * (-(q0 / (1 + Real.log (1 / r)) ^ 2))) := (Real.exp_nat_mul _ N).symm
    _ ≤ Real.exp (-(r ^ (-ζ) / 200 * (q0 / (1 + Real.log (1 / r)) ^ 2))) := by
      apply Real.exp_le_exp.2
      nlinarith [mul_le_mul_of_nonneg_right hN hq0']

/-- (D1) Under the cutoffs of (D2)-(D3) the probability `(1 - q(r))^N` is at most `1/2`. -/
theorem D1_le_half {q0 ζ r : ℝ} {N : ℕ} (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2)
    (hr : 0 < r) (hrA : r ≤ rAmp q0 ζ) (hN : r ^ (-ζ) / 200 ≤ (N : ℝ)) :
    (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N ≤ 1 / 2 := by
  have hr1 : r ≤ 1 := hrA.trans (min_le_left _ _)
  have hrA' : r ≤ (q0 / 200 * ζ ^ 2 / (16 * Real.log 2)) ^ (2 / ζ) := hrA.trans (min_le_right _ _)
  exact (D1_real hq0.le hq1 hr hr1 hN).trans
    (AmplCutoff.amplification_cutoff (div_pos hq0 (by norm_num)) hζ hζ' hr hr1 hrA')

/-- (D1, with the cutoff `r0` of (D3)) For `0 < r ≤ r0` and `N ≥ r^(-ζ)/200`, `(1 - q(r))^N ≤ 1/2`. -/
theorem D1_le_half_of_le_r0 {ρ s₀ p b lam cv c0 q0 ζ r : ℝ} {N : ℕ} (hρ : 0 < ρ) (hs₀ : 0 < s₀)
    (hcv : 0 < cv) (hc0 : 0 < c0) (hq0 : 0 < q0) (hq1 : q0 ≤ 1) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2)
    (hr : 0 < r) (hrr0 : r ≤ r0 ρ s₀ p b lam cv c0 q0 ζ) (hN : r ^ (-ζ) / 200 ≤ (N : ℝ)) :
    (1 - q0 / (1 + Real.log (1 / r)) ^ 2) ^ N ≤ 1 / 2 := by
  have hrA : r ≤ rAmp q0 ζ :=
    hrr0.trans (((r0_le_r0Min hρ hs₀ hcv hc0 hq0 hζ).trans r0Min_le_rAmp))
  exact D1_le_half hq0 hq1 hζ hζ' hr hrA hN

/-- (D4) The boxed radius `δ = min {r0, (δ*/2)^(1/p), (t*/2)^(2/p)}` of (D4), with `δ*`, `t*` the positive
field-measurable defaults of the write-up. -/
noncomputable def ddBoxed {Ω : Type*} (r0' p : ℝ) (dStar tStar : Ω → ℝ) (ω : Ω) : ℝ :=
  min (min r0' ((dStar ω / 2) ^ (1 / p))) ((tStar ω / 2) ^ (2 / p))

theorem ddBoxed_pos {Ω : Type*} {r0' p : ℝ} {dStar tStar : Ω → ℝ} (hr0 : 0 < r0') (hd : ∀ ω, 0 < dStar ω)
    (ht : ∀ ω, 0 < tStar ω) (ω : Ω) : 0 < ddBoxed r0' p dStar tStar ω := by
  unfold ddBoxed
  exact lt_min (lt_min hr0 (Real.rpow_pos_of_pos (div_pos (hd ω) two_pos) _))
    (Real.rpow_pos_of_pos (div_pos (ht ω) two_pos) _)

theorem ddBoxed_le_r0 {Ω : Type*} {r0' p : ℝ} {dStar tStar : Ω → ℝ} (ω : Ω) :
    ddBoxed r0' p dStar tStar ω ≤ r0' := by
  unfold ddBoxed
  exact (min_le_left _ _).trans (min_le_left _ _)

theorem measurable_ddBoxed {Ω : Type*} {m : MeasurableSpace Ω} {r0' p : ℝ} {dStar tStar : Ω → ℝ}
    (hd : Measurable[m] dStar) (ht : Measurable[m] tStar) : Measurable[m] (ddBoxed r0' p dStar tStar) := by
  unfold ddBoxed
  exact Measurable.min (Measurable.min measurable_const ((hd.div_const 2).pow_const _))
    ((ht.div_const 2).pow_const _)

/-- (D4, consequences used on the preparation event) `r ≤ dd` gives `r^p ≤ δ*/2` and `r^(p/2) ≤ t*/2`. -/
theorem ddBoxed_pow_le {Ω : Type*} {r0' p : ℝ} {dStar tStar : Ω → ℝ} {ω : Ω} {r : ℝ} (hp : 0 < p)
    (hr : 0 ≤ r) (hd : 0 < dStar ω) (ht : 0 < tStar ω) (h : r ≤ ddBoxed r0' p dStar tStar ω) :
    r ^ p ≤ dStar ω / 2 ∧ r ^ (p / 2) ≤ tStar ω / 2 := by
  have hp0 : p ≠ 0 := hp.ne'
  have hA : r ≤ (dStar ω / 2) ^ (1 / p) := (le_min_iff.1 (le_min_iff.1 h).1).2
  have hB : r ≤ (tStar ω / 2) ^ (2 / p) := (le_min_iff.1 h).2
  have eA : ((dStar ω / 2) ^ (1 / p)) ^ p = dStar ω / 2 := by
    rw [← Real.rpow_mul (div_pos hd two_pos).le, one_div_mul_cancel hp0, Real.rpow_one]
  have eB : ((tStar ω / 2) ^ (2 / p)) ^ (p / 2) = tStar ω / 2 := by
    rw [← Real.rpow_mul (div_pos ht two_pos).le]
    have : 2 / p * (p / 2) = 1 := by field_simp
    rw [this, Real.rpow_one]
  exact ⟨(Real.rpow_le_rpow hr hA hp.le).trans eA.le, (Real.rpow_le_rpow hr hB (by positivity)).trans eB.le⟩

end Lemma68Cutoff

end MatedCRT
