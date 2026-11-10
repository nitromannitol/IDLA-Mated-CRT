import MatedCRT.FirstPass.S6r.Constants
import MatedCRT.FirstPass.S6r.Shells.Parameters
import MatedCRT.FirstPass.S6r.Amplification

/-!
# The count hypothesis (7.10) of the Lemma 6.8 amplification (fp-S6r-S6-test-count)

Discharges the count hypothesis `c_N r^{-ζ} ≤ N` of `shell_product_le_half` (`FirstPass/S6r/Amplification.lean`) for the
shell count `N = shellCount r s = ⌊r / (400 s)⌋₊` (`FirstPass/S6r/Shells/Parameters.lean`, `shell_parameters`), with
`s = d^a`, `a = shortExp ζ = (1 + ζ)/2` and `r² ≤ d < 2r²`.

Sources: `notes/fp-gaps/CHATGPT-idla-6-8-shells.md` l.58-138 (step 1: `N = ⌊r/(400 s)⌋`, (7.9), and (7.10) with
`c_N = 2^{-a}/800`); `notes/fp-gaps/CHATGPT-idla-6-8-redesign.md` l.362-393 (`S6_numberOfTests`, (S6.1)-(S6.2)).

The constant `c_N` depends only on `ζ = K.ζ`, which `Constants68 γ ρ` fixes from `(γ, ρ)` in S0. The threshold
`r₁ = (2^{-a}/4000)^{1/ζ}` is the largest radius with `s ≤ r/4000`, the side condition of `shell_parameters`.
-/

open Real

namespace MatedCRT
namespace Lemma68Window

/-- The count constant `c_N = 2^{-a}/800` of (7.10), with `a = shortExp ζ`. -/
noncomputable def countConst (ζ : ℝ) : ℝ := (2 : ℝ) ^ (-shortExp ζ) / 800

lemma countConst_pos (ζ : ℝ) : 0 < countConst ζ := by
  unfold countConst
  positivity

/-- The radius threshold `r₁ = (2^{-a}/4000)^{1/ζ}`: for `0 < r ≤ r₁`, `r^ζ ≤ 2^{-a}/4000`. -/
noncomputable def countThreshold (ζ : ℝ) : ℝ := ((2 : ℝ) ^ (-shortExp ζ) / 4000) ^ (1 / ζ)

lemma countThreshold_pos (ζ : ℝ) : 0 < countThreshold ζ := by
  unfold countThreshold
  apply Real.rpow_pos_of_pos
  positivity

lemma countThreshold_le_one {ζ : ℝ} (hζ : 0 < ζ) : countThreshold ζ ≤ 1 := by
  have h2 : (2 : ℝ) ^ (-shortExp ζ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith [shortExp_nonneg hζ.le])
  have hb : (2 : ℝ) ^ (-shortExp ζ) / 4000 ≤ 1 := by linarith
  unfold countThreshold
  exact Real.rpow_le_one (by positivity) hb (one_div_pos.mpr hζ).le

/-- Side condition of `shell_parameters`: for `0 < r ≤ r₁` and `0 < d < 2r²`, `s = d^a ≤ r/4000`, since
`d^a ≤ (2r²)^a = 2^a r^{1+ζ} = r · (2^a r^ζ)` and `r^ζ ≤ 2^{-a}/4000`. -/
lemma shell_size_le {ζ r d : ℝ} (hζ : 0 < ζ) (hr : 0 < r) (hrle : r ≤ countThreshold ζ)
    (hd : 0 < d) (hd2 : d < 2 * r ^ 2) : d ^ shortExp ζ ≤ r / 4000 := by
  have ha : 0 < shortExp ζ := by unfold shortExp; linarith
  have h1 : d ^ shortExp ζ ≤ (2 * r ^ 2) ^ shortExp ζ :=
    Real.rpow_le_rpow hd.le hd2.le ha.le
  have hpow : (r ^ 2) ^ shortExp ζ = r * r ^ ζ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le,
      show ((2 : ℕ) : ℝ) * shortExp ζ = 1 + ζ by push_cast; linarith [two_mul_shortExp ζ],
      Real.rpow_add hr, Real.rpow_one]
  have h2 : (2 * r ^ 2) ^ shortExp ζ = (2 : ℝ) ^ shortExp ζ * (r * r ^ ζ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ r ^ 2), hpow]
  have h3 : r ^ ζ ≤ (2 : ℝ) ^ (-shortExp ζ) / 4000 := by
    have h4 : r ^ ζ ≤ countThreshold ζ ^ ζ := Real.rpow_le_rpow hr.le hrle hζ.le
    have h5 : countThreshold ζ ^ ζ = (2 : ℝ) ^ (-shortExp ζ) / 4000 := by
      unfold countThreshold
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (-shortExp ζ) / 4000),
        one_div_mul_cancel hζ.ne', Real.rpow_one]
    rw [h5] at h4
    exact h4
  have h6 : (2 : ℝ) ^ shortExp ζ * (2 : ℝ) ^ (-shortExp ζ) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
  calc d ^ shortExp ζ ≤ (2 * r ^ 2) ^ shortExp ζ := h1
    _ = (2 : ℝ) ^ shortExp ζ * (r * r ^ ζ) := h2
    _ ≤ (2 : ℝ) ^ shortExp ζ * (r * ((2 : ℝ) ^ (-shortExp ζ) / 4000)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hr.le) (by positivity)
    _ = r / 4000 := by
        have e : (2 : ℝ) ^ shortExp ζ * (r * ((2 : ℝ) ^ (-shortExp ζ) / 4000))
            = r / 4000 * ((2 : ℝ) ^ shortExp ζ * (2 : ℝ) ^ (-shortExp ζ)) := by ring
        rw [e, h6, mul_one]

/-- **(7.10), fp-S6r-S6-test-count.** For `K : Constants68 γ ρ` there is `r₁ ∈ (0, 1]` such that for `0 < r ≤ r₁` and
`r² ≤ d < 2r²`, the shell count `N = shellCount r (d^a)` satisfies `c_N r^{-ζ} ≤ N` with `c_N = countConst K.ζ`
(depends only on `ζ`, which is fixed by `(γ, ρ)`). Proof: `shell_parameters` (last conjunct) with `s ≤ r/4000`
from `shell_size_le`. -/
theorem count_bound {γ ρ : ℝ} (K : Constants68 γ ρ) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r₁ → ∀ d : ℝ, 0 < d → r ^ 2 ≤ d → d < 2 * r ^ 2 →
      countConst K.ζ * r ^ (-K.ζ) ≤ (shellCount r (d ^ shortExp K.ζ) : ℝ) := by
  refine ⟨countThreshold K.ζ, countThreshold_pos K.ζ, countThreshold_le_one K.hζ0, ?_⟩
  intro r hr hrle d hd hrd hd2
  have hsr : d ^ shortExp K.ζ ≤ r / 4000 := shell_size_le K.hζ0 hr hrle hd hd2
  exact (shell_parameters (s := d ^ shortExp K.ζ) (ζ := K.ζ) hr hd K.hζ0.le rfl hrd hd2 hsr).2.2.2

/-- The (7.10) count hypothesis of `shell_product_le_half` (`cN * r ^ (-K.ζ) ≤ ((n + 1 : ℕ) : ℝ)`), supplied for
`n + 1 = shellCount r (d^a)`. -/
theorem count_hypothesis {γ ρ : ℝ} (K : Constants68 γ ρ) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r₁ → ∀ d : ℝ, 0 < d → r ^ 2 ≤ d → d < 2 * r ^ 2 →
      ∀ n : ℕ, shellCount r (d ^ shortExp K.ζ) = n + 1 →
        countConst K.ζ * r ^ (-K.ζ) ≤ ((n + 1 : ℕ) : ℝ) := by
  obtain ⟨r₁, h0, h1, hb⟩ := count_bound K
  refine ⟨r₁, h0, h1, fun r hr hrle d hd hrd hd2 n hn => ?_⟩
  have h := hb r hr hrle d hd hrd hd2
  rw [hn] at h
  exact h

/-- **Lemma 6.8, steps 13-14 with the count discharged (fp-S6r-S6-test-count).** `shell_product_le_half` for the
shell count `N = shellCount r (d^a)`: its count hypothesis is supplied by `count_hypothesis` (with `cN = countConst K.ζ`,
which depends only on `(γ, ρ)`), so only `0 < r ≤ r_amp`, `r² ≤ d < 2r²` and `N = n + 1` remain. -/
theorem shell_product_le_half_of_shells {γ ρ : ℝ} (K : Constants68 γ ρ) {q0 : ℝ} (hq0 : 0 < q0) :
    ∃ r_amp : ℝ, 0 < r_amp ∧ r_amp ≤ 1 ∧ ∀ r d : ℝ, 0 < r → r ≤ r_amp → 0 < d → r ^ 2 ≤ d → d < 2 * r ^ 2 →
      ∀ (n : ℕ) (q μB : ℝ), 0 ≤ q → q ≤ 1 → shellCount r (d ^ shortExp K.ζ) = n + 1 →
        q0 / (1 + Real.log (1 / r)) ^ 2 ≤ q → μB ≤ (1 - q) ^ (n + 1) → μB ≤ Constants68.s2 := by
  obtain ⟨r₁, h0, h1, hc⟩ := count_hypothesis K
  obtain ⟨r_amp, ha0, ha1, hbd⟩ := shell_product_le_half K (countConst_pos K.ζ) hq0
  refine ⟨min r_amp r₁, lt_min ha0 h0, (min_le_left _ _).trans ha1,
    fun r d hr hrle hd hrd hd2 n q μB hq0' hq1 hn hq hμB => ?_⟩
  have hN := hc r hr ((hrle.trans (min_le_right _ _))) d hd hrd hd2 n hn
  exact hbd r hr (hrle.trans (min_le_left _ _)) n q μB hq0' hq1 hN hq hμB

end Lemma68Window
end MatedCRT
