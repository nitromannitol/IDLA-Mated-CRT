import Mathlib

/-!
# First pass, Lemma 6.8: numerical cutoffs of the trace bound (q2, fp-S4S6c-envscaling-6-7-6-8)

Pure real arithmetic behind the cutoffs of the write-up (`notes/fp-gaps/CHATGPT-lemma68-open-parts.md`, C1 and D1-D3)
and of the good radii (`notes/fp-gaps/LEMMA68.md`, eq. (9): `R_z ∈ [δ, √δ]`, `s = √δ`, `g_δ = δ/100`).

Notation: `ζ = p/2 - 1 ∈ (0, 1/2)`, so `r^p = (r * r^ζ)^2`; the field scale `δ` is dyadic in `(r^p/2, r^p]`
(`dyadicBelow`); the test step is `s = √δ`; the centre tolerance is `g = δ/100`; the cell tolerance `d` satisfies
`d ≤ min(δ/100, r/1000)`; the test count is `N = ⌊r/(100 s)⌋₊` (write-up D1).

Terminology: the scale `δ` is a dyadic radius of the Armitage-Gardiner / Gwynne-Miller annulus iteration; the
numerical facts here carry no probability.
-/

open Real

namespace MatedCRT
namespace Uniform68Params

/-- The dyadic scale `2^{⌊log₂ x⌋}` (write-up line 393: `δ` dyadic with `r^p/2 < δ ≤ r^p`). -/
noncomputable def dyadicBelow (x : ℝ) : ℝ := (2 : ℝ) ^ (⌊Real.logb 2 x⌋)

/-- `dyadicBelow x` lies in `(x/2, x]` for `x > 0`. -/
theorem dyadicBelow_bounds {x : ℝ} (hx : 0 < x) : x / 2 < dyadicBelow x ∧ dyadicBelow x ≤ x := by
  have hk1 : ((⌊Real.logb 2 x⌋ : ℤ) : ℝ) ≤ Real.logb 2 x := Int.floor_le _
  have hk2 : Real.logb 2 x < ((⌊Real.logb 2 x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hxe : (2 : ℝ) ^ (Real.logb 2 x) = x := Real.rpow_logb (by norm_num) (by norm_num) hx
  have hd : dyadicBelow x = (2 : ℝ) ^ ((⌊Real.logb 2 x⌋ : ℤ) : ℝ) := by
    unfold dyadicBelow
    rw [Real.rpow_intCast]
  rw [hd]
  constructor
  · have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hk2
    rw [hxe, Real.rpow_add (by norm_num), Real.rpow_one] at h
    linarith
  · calc (2 : ℝ) ^ ((⌊Real.logb 2 x⌋ : ℤ) : ℝ)
        ≤ (2 : ℝ) ^ (Real.logb 2 x) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hk1
      _ = x := hxe

/-- For `x ≥ 2`, `⌊x⌋₊ ≥ x/2`. -/
theorem half_le_floor {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one x
  linarith

/-- The numerical cutoffs of one test scale. Let `q = r * r^ζ` (so `q^2 = r^p`), `δ ∈ (0, q^2]`, `s = √δ`, and
`0 ≤ d ≤ min(δ/100, r/1000)`. Then: `s ≤ r/1000` (write-up C1), `s ≤ r^{p/2}`, `g + d < s` for `g = δ/100`
(write-up C1: `g_δ + d < s`), `d < r/2`, and the test count `N = ⌊r/(100 s)⌋₊` satisfies `N s ≤ r/100` and
`r^{-ζ}/200 ≤ N` (write-up D1). -/
theorem trace_numerics {r ζ δ d : ℝ} (hr : 0 < r) (hcut : r ^ ζ ≤ 1 / 1000) (hr1 : r ≤ 1)
    (hδ0 : 0 < δ) (hδle : δ ≤ (r * r ^ ζ) ^ 2) (hdδ : d ≤ δ / 100) :
    0 < √δ ∧ √δ ≤ r / 1000 ∧ √δ ≤ r * r ^ ζ ∧ δ / 100 + d < √δ ∧ d < r / 2 ∧
      ((⌊r / (100 * √δ)⌋₊ : ℝ) * √δ ≤ r / 100) ∧ r ^ (-ζ) / 200 ≤ (⌊r / (100 * √δ)⌋₊ : ℝ) := by
  have hs0 : 0 < √δ := Real.sqrt_pos.2 hδ0
  have hsne : √δ ≠ 0 := hs0.ne'
  have hrne : r ≠ 0 := hr.ne'
  have hsq : √δ ≤ r * r ^ ζ := by
    calc √δ ≤ √((r * r ^ ζ) ^ 2) := Real.sqrt_le_sqrt hδle
      _ = r * r ^ ζ := Real.sqrt_sq (by positivity)
  have htz0 : 0 < r ^ ζ := Real.rpow_pos_of_pos hr ζ
  have hs_r : √δ ≤ r / 1000 := by nlinarith
  have hsδ : √δ * √δ = δ := Real.mul_self_sqrt hδ0.le
  have hδs : δ < √δ := by
    have hs1 : √δ ≤ 1 := by nlinarith
    nlinarith
  have hg : δ / 100 + d < √δ := by
    have h1 : δ / 100 + d ≤ δ / 50 := by linarith
    have h2 : δ / 50 < √δ := by nlinarith
    linarith
  have hdr2 : d < r / 2 := by
    have : δ / 100 ≤ r ^ 2 / 100 := by nlinarith
    nlinarith
  -- the test count
  set x : ℝ := r / (100 * √δ) with hx
  have hx_eq : x * √δ = r / 100 := by
    rw [hx]; field_simp
  have hx2 : 2 ≤ x := by
    rw [hx, le_div_iff₀ (by positivity)]
    nlinarith
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  refine ⟨hs0, hs_r, hsq, hg, hdr2, ?_, ?_⟩
  · calc (⌊x⌋₊ : ℝ) * √δ ≤ x * √δ := mul_le_mul_of_nonneg_right hNx hs0.le
      _ = r / 100 := hx_eq
  · have hfl := half_le_floor hx2
    have hlow : r ^ (-ζ) / 200 ≤ x / 2 := by
      rw [Real.rpow_neg hr.le, hx]
      have hpos : 0 < r * r ^ ζ := by positivity
      calc (r ^ ζ)⁻¹ / 200 = r / (200 * (r * r ^ ζ)) := by field_simp
        _ ≤ r / (200 * √δ) := div_le_div_of_nonneg_left hr.le (by linarith) (by linarith)
        _ = r / (100 * √δ) / 2 := by rw [div_div, show (100 : ℝ) * √δ * 2 = 200 * √δ by ring]
    linarith

/-- The radius bounds of the good radii `R_z ∈ [δ, √δ]` (LEMMA68.md eq. (9)) against the cell tolerance `d ≤ δ/100`:
the inequalities required of `rad` in `BandInduction68` / `HcPrinted68.hc_band_var` (`hρ`, `hgeo`, `hlt`). -/
theorem radius_facts {δ R d g : ℝ} (hδ0 : 0 < δ) (hR1 : δ ≤ R)
    (hdδ : d ≤ δ / 100) (hg : g = δ / 100) :
    d < R / 4 ∧ 4 * R / 3 + d + R / 4 + d < 2 * R ∧ g + d < 4 * R / 3 := by
  have hR0 : 0 < R := lt_of_lt_of_le hδ0 hR1
  subst hg
  refine ⟨by linarith, by linarith, by linarith⟩

end Uniform68Params
end MatedCRT

#print axioms MatedCRT.Uniform68Params.dyadicBelow_bounds
#print axioms MatedCRT.Uniform68Params.trace_numerics
#print axioms MatedCRT.Uniform68Params.radius_facts
