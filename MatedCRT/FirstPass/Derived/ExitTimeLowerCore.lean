import MatedCRT.FirstPass.Derived.ExitTimeLowerTail

/-!
# Lower tail of the exit time from a ball: the deterministic step of Berestycki-Gwynne, Lemma 6.7

Berestycki-Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*, proof of
Lemma 6.7, for one vertex `x` and the vertex set `A` of `B_r(η(x))`. Write `M_c = μ_h(B_{cr}(η(x)))` and
`M_2 = μ_h(B_{2r}(η(x)))`. Suppose:

* the expected exit time has the lower bound `ε⁻¹ M_c ≤ E_x[τ_A]` (Proposition 4.1);
* the `N`-th moment has the upper bound `E_x[τ_A^N] ≤ N! C^N ε^{-N} I^N` (Proposition 5.1), where `I` is
  the supremum of the log-kernel integrals, and `I ≤ s M_2` (estimate (6.17), `s = δ^{-ζ}`);
* the ratio bound `κ M_2 ≤ M_c` holds (estimate (6.18), Lemma A.2);
* the lower bound `2t ≤ M_c` holds (estimate (6.20), Lemma A.1).

Then the Paley-Zygmund inequality in the `L^N` form of Lemma 6.6 (`rpow_half_div_le_srwLaw`, with
Hölder conjugate exponents `p, q` and `q ≤ N`) gives
`(κ / (2 N! C s))^p ≤ P_x[τ_A > ε⁻¹ t]`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set
open scoped ENNReal

/-- **Deterministic step of Berestycki-Gwynne, Lemma 6.7**: the expected exit time lower bound
`ε⁻¹ M_c ≤ E_x[τ_A]`, the moment bound `E_x[τ_A^N] ≤ N! C^N ε^{-N} I^N` with `I ≤ s M_2`, the ratio
bound `κ M_2 ≤ M_c` and `2t ≤ M_c` give `(κ / (2 N! C s))^p ≤ P_x[τ_A > ε⁻¹ t]` for Hölder conjugate
`p, q` with `q ≤ N`. -/
theorem ofReal_rpow_le_srwLaw_exitTime_of_ratio (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) {p q : ℝ}
    (hpq : p.HolderConjugate q) {N : ℕ} (hN : 1 ≤ N) (hqN : q ≤ N)
    {Mc M2 I : ℝ≥0∞} {ε C s κ t : ℝ} (hε : 0 < ε) (hC : 0 < C) (hs : 0 < s) (hκ : 0 ≤ κ)
    (ht : 0 < t) (hMc : Mc ≠ ⊤)
    (hLE : ENNReal.ofReal ε⁻¹ * Mc ≤ expectedExitTime m A a)
    (hmom : exitTimeMoment m A a N ≤
      ENNReal.ofReal (N.factorial * C ^ N * ε ^ (-(N : ℝ))) * I ^ N)
    (hI : I ≤ ENNReal.ofReal s * M2) (hR : ENNReal.ofReal κ * M2 ≤ Mc)
    (hT : ENNReal.ofReal (2 * t) ≤ Mc) :
    ENNReal.ofReal (κ / (2 * (N.factorial * C * s))) ^ p ≤
      srwLaw m a {x | ENNReal.ofReal (ε⁻¹ * t) < (vExitTime A x : ℝ≥0∞)} := by
  have hF : (1 : ℝ) ≤ N.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hF0 : (N.factorial : ℝ) ≠ 0 := by positivity
  have hεi : 0 < ε⁻¹ := inv_pos.mpr hε
  have hK0 : 0 < (N.factorial : ℝ) * C * ε⁻¹ * s := by positivity
  have hL : ENNReal.ofReal ε⁻¹ * Mc ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMc
  -- the moment bound in the form `E[τ^N] ≤ U^N`
  have hU : exitTimeMoment m A a N ≤
      (ENNReal.ofReal ((N.factorial : ℝ) * C * ε⁻¹ * s) * M2) ^ N := by
    have hX : 0 ≤ (N.factorial : ℝ) * C ^ N * ε ^ (-(N : ℝ)) := by positivity
    have hreal : (N.factorial : ℝ) * C ^ N * ε ^ (-(N : ℝ)) * s ^ N ≤
        ((N.factorial : ℝ) * C * ε⁻¹ * s) ^ N := by
      rw [Real.rpow_neg hε.le, Real.rpow_natCast, ← inv_pow, mul_pow, mul_pow, mul_pow]
      have h1 : (N.factorial : ℝ) ≤ (N.factorial : ℝ) ^ N := le_self_pow₀ hF (by omega)
      have h2 : 0 ≤ C ^ N * ε⁻¹ ^ N * s ^ N := by positivity
      nlinarith
    refine hmom.trans ?_
    calc ENNReal.ofReal (N.factorial * C ^ N * ε ^ (-(N : ℝ))) * I ^ N
        ≤ ENNReal.ofReal (N.factorial * C ^ N * ε ^ (-(N : ℝ))) * (ENNReal.ofReal s * M2) ^ N := by
          gcongr
      _ = ENNReal.ofReal ((N.factorial : ℝ) * C ^ N * ε ^ (-(N : ℝ)) * s ^ N) * M2 ^ N := by
          rw [mul_pow, ← ENNReal.ofReal_pow hs.le, ← mul_assoc, ← ENNReal.ofReal_mul hX]
      _ ≤ ENNReal.ofReal (((N.factorial : ℝ) * C * ε⁻¹ * s) ^ N) * M2 ^ N := by
          gcongr
      _ = (ENNReal.ofReal ((N.factorial : ℝ) * C * ε⁻¹ * s) * M2) ^ N := by
          rw [ENNReal.ofReal_pow hK0.le, mul_pow]
  have hmain := MatedCRT.ExitTimeLowerTail.rpow_half_div_le_srwLaw m A a hpq hqN hL hLE hU
  -- `ε⁻¹ t ≤ L / 2`
  have hhalf : ENNReal.ofReal (ε⁻¹ * t) ≤ ENNReal.ofReal ε⁻¹ * Mc / 2 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    calc ENNReal.ofReal (ε⁻¹ * t) * 2 = ENNReal.ofReal ε⁻¹ * ENNReal.ofReal (2 * t) := by
          rw [ENNReal.ofReal_mul hεi.le, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_ofNat]
          ring
      _ ≤ ENNReal.ofReal ε⁻¹ * Mc := by gcongr
  -- `L / 2` is neither `0` nor `⊤`
  have hL0 : ENNReal.ofReal ε⁻¹ * Mc / 2 ≠ 0 := by
    have h2t : (0 : ℝ≥0∞) < ENNReal.ofReal (ε⁻¹ * t) := ENNReal.ofReal_pos.mpr (by positivity)
    exact (h2t.trans_le hhalf).ne'
  have hLt : ENNReal.ofReal ε⁻¹ * Mc / 2 ≠ ⊤ := ENNReal.div_ne_top hL two_ne_zero
  -- the key comparison `κ / (2 N! C s) ≤ (L / 2) / U`
  have hkey : ENNReal.ofReal (κ / (2 * (N.factorial * C * s))) ≤
      ENNReal.ofReal ε⁻¹ * Mc / 2 / (ENNReal.ofReal ((N.factorial : ℝ) * C * ε⁻¹ * s) * M2) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inr hL0) (Or.inr hLt),
      ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    have hY : 0 ≤ κ / (2 * (N.factorial * C * s)) := by positivity
    have hYK : 0 ≤ κ / (2 * (N.factorial * C * s)) * ((N.factorial : ℝ) * C * ε⁻¹ * s) := by
      positivity
    have hreal : κ / (2 * (N.factorial * C * s)) * ((N.factorial : ℝ) * C * ε⁻¹ * s) * 2 =
        ε⁻¹ * κ := by
      field_simp
    calc ENNReal.ofReal (κ / (2 * (N.factorial * C * s))) *
          (ENNReal.ofReal ((N.factorial : ℝ) * C * ε⁻¹ * s) * M2) * 2
        = ENNReal.ofReal (κ / (2 * (N.factorial * C * s)) * ((N.factorial : ℝ) * C * ε⁻¹ * s) * 2) *
            M2 := by
          rw [ENNReal.ofReal_mul hYK, ENNReal.ofReal_mul hY, ENNReal.ofReal_ofNat]
          ring
      _ = ENNReal.ofReal ε⁻¹ * (ENNReal.ofReal κ * M2) := by
          rw [hreal, ENNReal.ofReal_mul hεi.le, mul_assoc]
      _ ≤ ENNReal.ofReal ε⁻¹ * Mc := by gcongr
  refine le_trans (ENNReal.rpow_le_rpow hkey hpq.nonneg) (hmain.trans (measure_mono ?_))
  intro x hx
  exact lt_of_le_of_lt hhalf hx

end MatedCRT.FirstPass.Derived
