import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.AtAnnulus

/-!
# Lemma 6.8: the bound at a vertex `b ∈ V^ε(∂B_{(4/3)𝐫_z}(z)) ∩ A` (Steps 2-4, lines 2537-2620)

* `stay_le_at_vertex`: Step 3 (the count `|V^ε(B_{𝐜₀𝐫_z}(η(b))) \ A| ≥ ε⁻¹ μ_h(B_{𝐜₀𝐫_z}(η(b)))/2`, from Lemma 2.9 and
  the assumption on `A`) and Step 4 (`E[τ²] ≤ K ε⁻² μ_h(B_{𝐜₀𝐫_z}(η(b)))²`) give
  `P[the walk from b stays in A until it exits U] ≤ 1 - 1/(16 K)`.
* `exitTimeMoment_le_of_logLoss`: Step 4, route (b): `ExitTimeLogLossStep` with `N = 2` and
  `Q ≤ (1 + log (4/𝐫_z)) C μ_h(B_{𝐜₀𝐫_z}(η(b)))` give `K = 2 C₁² (1 + log (4/𝐫_z))² C²`.
* `half_le_greenFn`: Lemma 2.16 with eq:choice-of-constant-annulus (`𝐜₀ = e^{-3C/2}/12`) gives `G ≥ 1/2`.
* `one_add_log_le`: `1 + log (4/𝐫_z) ≤ 9 (1 + |log r|)` for `𝐫_z ≥ r²/128`.
-/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

namespace ConstantOrderDiv

/-- **Steps 2-4 at a vertex.** -/
theorem stay_le_at_vertex {m : ℤ → ℤ → ℕ} {ε : ℝ} (hε : 0 < ε) {U A W Vc Vr : Set ℤ} {b : ℤ}
    {M r s₁ βm α₉ K : ℝ} (hWU : W ⊆ U) (hVcW : Vc ⊆ W) (hVcVr : Vc ⊆ Vr) (hfin : Vr.Finite)
    (hG : ∀ b' ∈ Vc, (1 / 2 : ℝ) ≤ greenFn m W b b')
    (hcount : ε⁻¹ * M - ε ^ (-1 + α₉) ≤ (Vc.ncard : ℝ))
    (hA : ((A ∩ Vr).ncard : ℝ) < s₁ * r ^ (2 * βm) / ε)
    (hsmall : ε ^ α₉ + s₁ * r ^ (2 * βm) ≤ M / 2) (hM : 0 < M) (hK : 0 < K)
    (hY : exitTimeMoment m W b 2 ≤ ENNReal.ofReal (K * ε⁻¹ ^ 2) * ENNReal.ofReal M ^ 2) :
    srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime U x → x n ∈ A} ≤ ENNReal.ofReal (1 - 1 / (16 * K)) := by
  set E' := Vc \ A
  have hE'W : E' ⊆ W \ A := fun k hk => ⟨hVcW hk.1, hk.2⟩
  have hE'fin : E'.Finite := hfin.subset fun k hk => hVcVr hk.1
  have hcover : Vc ⊆ E' ∪ (A ∩ Vr) := by
    intro k hk
    by_cases hkA : k ∈ A
    · exact Or.inr ⟨hkA, hVcVr hk⟩
    · exact Or.inl ⟨hk, hkA⟩
  have hcard : (Vc.ncard : ℝ) ≤ E'.ncard + (A ∩ Vr).ncard := by
    have h1 := Set.ncard_le_ncard hcover (hE'fin.union (hfin.subset inter_subset_right))
    have h2 := Set.ncard_union_le E' (A ∩ Vr)
    exact_mod_cast h1.trans h2
  have hrpow : ε ^ (-1 + α₉) = ε⁻¹ * ε ^ α₉ := by
    rw [Real.rpow_add hε, Real.rpow_neg_one]
  have hE'ge : ε⁻¹ * M / 2 ≤ (E'.ncard : ℝ) := by
    have hdiv : s₁ * r ^ (2 * βm) / ε = ε⁻¹ * (s₁ * r ^ (2 * βm)) := by rw [div_eq_inv_mul]
    rw [hrpow] at hcount
    rw [hdiv] at hA
    have hinv : 0 < ε⁻¹ := inv_pos.2 hε
    have : ε⁻¹ * (ε ^ α₉ + s₁ * r ^ (2 * βm)) ≤ ε⁻¹ * (M / 2) := mul_le_mul_of_nonneg_left hsmall hinv.le
    nlinarith
  have hN : ENNReal.ofReal (ε⁻¹ / 4) * ENNReal.ofReal M ≤ ENNReal.ofReal ((E'.ncard : ℝ) / 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hhit := prob_hit_lower hE'W hE'fin (fun b' hb' => hG b' hb'.1) (by positivity : (0 : ℝ) ≤ ε⁻¹ / 4)
    (mul_pos hK (by positivity) : 0 < K * ε⁻¹ ^ 2) (ENNReal.ofReal_pos.2 hM).ne' ENNReal.ofReal_ne_top hN hY
  have hp : (ε⁻¹ / 4) ^ 2 / (K * ε⁻¹ ^ 2) = 1 / (16 * K) := by
    field_simp
    ring
  rw [hp] at hhit
  exact prob_stay_le hWU (by positivity) hhit

/-- `ofReal a * ofReal b ^ 2 = ofReal (a * b ^ 2)` for `a, b ≥ 0`. -/
theorem ofReal_mul_ofReal_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a * ENNReal.ofReal b ^ 2 = ENNReal.ofReal (a * b ^ 2) := by
  rw [← ENNReal.ofReal_pow hb, ← ENNReal.ofReal_mul ha]

/-- **Step 4, route (b)**: the exit-time bound of `ExitTimeLogLossStep` (`N = 2`) with `Q ≤ (1 + L) C M`. -/
theorem exitTimeMoment_le_of_logLoss {X Q : ℝ≥0∞} {ε C₁ L CE M : ℝ} (hε : 0 < ε) (hL : 0 ≤ L) (hCE : 0 ≤ CE)
    (hM : 0 ≤ M)
    (hlog : X ≤ ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * C₁ ^ (2 : ℕ) * ε ^ (-((2 : ℕ) : ℝ))) * Q ^ (2 : ℕ))
    (hQ : Q ≤ (1 + ENNReal.ofReal L) * (ENNReal.ofReal CE * ENNReal.ofReal M)) :
    X ≤ ENNReal.ofReal (2 * C₁ ^ 2 * (1 + L) ^ 2 * CE ^ 2 * ε⁻¹ ^ 2) * ENNReal.ofReal M ^ 2 := by
  have hQ' : Q ≤ ENNReal.ofReal ((1 + L) * CE * M) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add zero_le_one hL,
      ENNReal.ofReal_one, mul_assoc]
    exact hQ
  have hε2 : ε ^ (-((2 : ℕ) : ℝ)) = ε⁻¹ ^ 2 := by
    rw [Real.rpow_neg hε.le, Real.rpow_natCast, inv_pow]
  refine hlog.trans ?_
  rw [hε2, ofReal_mul_ofReal_sq (by positivity) hM]
  calc ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * C₁ ^ (2 : ℕ) * ε⁻¹ ^ 2) * Q ^ (2 : ℕ)
      ≤ ENNReal.ofReal (((2 : ℕ).factorial : ℝ) * C₁ ^ (2 : ℕ) * ε⁻¹ ^ 2) *
          ENNReal.ofReal ((1 + L) * CE * M) ^ 2 := by gcongr
    _ = ENNReal.ofReal (2 * C₁ ^ 2 * (1 + L) ^ 2 * CE ^ 2 * ε⁻¹ ^ 2 * M ^ 2) := by
        rw [ofReal_mul_ofReal_sq (by positivity) (by positivity)]
        congr 1
        simp only [Nat.factorial_two, Nat.cast_ofNat]
        ring

/-- **Lemma 2.16 with eq:choice-of-constant-annulus**: if `C⁻¹ log t - 1 ≤ g ≤ G` with `t ≥ e^{3C/2}`, then
`G ≥ 1/2`. -/
theorem half_le_greenFn {C t g G : ℝ} (hC : 0 < C) (ht : Real.exp (3 / 2 * C) ≤ t) (hlow : C⁻¹ * Real.log t - 1 ≤ g)
    (hgG : g ≤ G) : (1 / 2 : ℝ) ≤ G := by
  have hlog : 3 / 2 * C ≤ Real.log t := by
    rw [← Real.log_exp (3 / 2 * C)]
    exact Real.log_le_log (Real.exp_pos _) ht
  have : 3 / 2 ≤ C⁻¹ * Real.log t := by
    rw [le_inv_mul_iff₀ hC]
    linarith
  linarith

/-- `1 + log (4/R) ≤ 9 (1 + |log r|)` for `r²/128 ≤ R ≤ 4` and `0 < r ≤ 1`. -/
theorem one_add_log_le {r R : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hR : r ^ 2 / 128 ≤ R) :
    1 + Real.log (4 / R) ≤ 9 * (1 + |Real.log r|) := by
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
  have h1 : Real.log (4 / R) ≤ Real.log (512 / r ^ 2) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ hRpos (by positivity)]
    nlinarith
  have h2 : Real.log (512 / r ^ 2) = 9 * Real.log 2 - 2 * Real.log r := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_pow, show (512 : ℝ) = 2 ^ 9 by norm_num,
      Real.log_pow]
    push_cast
    ring
  have hlog2 : Real.log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlogr : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
  rw [abs_of_nonpos hlogr]
  linarith

end ConstantOrderDiv

end MatedCRT
