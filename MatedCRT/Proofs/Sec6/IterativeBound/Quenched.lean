import MatedCRT.Proofs.Sec6.IterativeBound.Core
import MatedCRT.Proofs.Sec6.IterativeBound.Bounds

/-!
# Lemma 6.10: the quenched iteration (`QuenchedIterationStep`)

Parameters (`ω₂ = ω ∧ κ`, `a = 1/(2β⁻)`): exponent `β = (a/4) ∧ (ω₂/8)`; round radius
`r_n = max((n ε/s₅)^a, 10 ε^{ω₂})` (with `10 ε^{ω₂} ≥ 10 ε^ω` in place of `10 ε^{ω₀}`);
Step 3 threshold `N = ε^{-ω₂/2}` (eq:iterate-stop-time2); radius budget `Ψ(n) = (n-1)ε^κ` for `n ≤ N` and
`A x_n^{1/2} + B log n + N ε^κ` otherwise; failure budget `G(n) = n e` with
`e = exp(-(s₃/64) r_min^{1/4} N)` (eqn:use-absorb). `core_induction` gives the failure probability `≤ G(j) ≤ M ε`
and the spread `≤ Ψ(j) ≤ δ₀^β`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace IterativeBound

/-- The walkers of a round number at most `J = ⌈δ₀/ε⌉`, so `n ε / s₅ ≤ (𝛅 ∧ 1)^{2β⁻}`. -/
theorem le_rpow_of_le_ceil {ε s₅ βm δ₀ dd τ : ℝ} {n : ℕ} (hε : 0 < ε) (hs₅ : 0 < s₅) (hβm : 1 ≤ βm)
    (hδ₀ : 0 < δ₀) (hτ : 0 < τ) (hτdd : τ ≤ dd) (hδdd : δ₀ < s₅ * min dd 1 ^ (2 * βm) / 2)
    (hεs : ε ≤ s₅ * min τ 1 ^ (2 * βm) / 2) (hn : n ≤ ⌈δ₀ / ε⌉₊) :
    (n : ℝ) * ε / s₅ ≤ min dd 1 ^ (2 * βm) := by
  have hJ : (⌈δ₀ / ε⌉₊ : ℝ) < δ₀ / ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hnJ : (n : ℝ) ≤ ⌈δ₀ / ε⌉₊ := by exact_mod_cast hn
  have hτ1 : min τ 1 ^ (2 * βm) ≤ min dd 1 ^ (2 * βm) :=
    Real.rpow_le_rpow (le_min hτ.le zero_le_one) (min_le_min_right 1 hτdd) (by linarith)
  have h1 : (n : ℝ) * ε < δ₀ + ε := by
    have := mul_lt_mul_of_pos_right (lt_of_le_of_lt hnJ hJ) hε
    rw [add_mul, div_mul_cancel₀ _ hε.ne', one_mul] at this
    exact this
  rw [div_le_iff₀ hs₅]
  have h2 := mul_le_mul_of_nonneg_left hτ1 hs₅.le
  linarith only [h1, h2, hδdd, hεs]

/-- **The quenched iteration for one environment** (the body of `QuenchedIterationStep`, all parameters fixed). -/
theorem quenched_env {ρ βm ω₀ κ ω₂ a β s₀ s₃ s₄ s₅ A K q D₀ τ C₁ M ε : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hβm : 1 ≤ βm) (hω₂0 : 0 < ω₂) (hω₂ω₀ : ω₂ ≤ ω₀) (hω₂κ : ω₂ ≤ κ)
    (ha_def : a = (2 * βm)⁻¹) (ha1 : a ≤ 1 / 2) (hβ0 : 0 < β) (hβa : β ≤ a / 4) (hβω : β ≤ ω₂ / 8)
    (hs₃ : 0 < s₃) (hs₄ : 0 < s₄) (hs₄1 : s₄ < 1) (hs₅ : 0 < s₅)
    (hA_def : A = 8 / (a * (s₄ / 64))) (hK_def : K = A * (2 / s₅) ^ (a / 2)) (hq_def : q = a / 2 - β)
    (hD1 : D₀ ≤ 1) (hDK : D₀ ≤ (1 / (2 * K)) ^ q⁻¹) (hDρ1 : D₀ ≤ ((1 - ρ) / 8) ^ β⁻¹)
    (hDρ2 : D₀ ≤ (ρ / 4) ^ β⁻¹) (hτ : 0 < τ) (hC₁ : C₁ = 80 * 2 ^ (ω₂ / 4) / (s₄ / 64 * ω₂))
    (hM : M = 2 * ((⌈8 / ω₂⌉₊).factorial : ℝ) / (s₃ / 64) ^ ⌈8 / ω₂⌉₊)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hC2 : ε ^ ω₂ ≤ min τ 1 / 10) (hC3 : ε ≤ s₅ * min τ 1 ^ (2 * βm) / 2)
    (hC4 : ε ^ (ω₂ / 2) ≤ 1 / 2) (hC5 : ε ^ (ω₂ / 2 - β) ≤ 1 / (4 * (C₁ + 1)))
    {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ} {dd : ℝ} (hτdd : τ ≤ dd) (hη : Continuous η) (hab : IsAbelianIDLA m)
    (hsrw : IsSrwPathLaw m) (h69 : AbsorptionBound m ε η ((1 + ρ) / 2) βm ω₀ s₀ s₃ s₄ s₅ dd)
    (hcell : ∀ a b : ℤ, a ∈ cellVertices ε η (ball 0 ((1 + ρ) / 2)) → m a b ≠ 0 →
      (cell ε η a ∩ cell ε η b).Nonempty)
    (hdiam : ∀ a ∈ cellVertices ε η (ball 0 ((1 + ρ) / 2)), diam (cell ε η a) ≤ ε ^ κ)
    {Θ : Set ℤ} (hΘ1 : closure (fillCells ε η Θ) ⊆ ball 0 (ρ / 2)) (hΘ2 : ball 0 s₀ ⊆ fillCells ε η Θ)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hδ₀D : δ₀ < D₀) (hδ₀dd : δ₀ < s₅ * min dd 1 ^ (2 * βm) / 2)
    {j : ℕ} (hj : j ≤ ⌈δ₀ / ε⌉₊) {a' : Fin j → ℤ} (ha' : ∀ i, a' i ∈ vClosure m Θ) :
    walkersLaw m a' {xs | ¬ (idlaAggregate Θ univ (List.ofFn xs) ⊆
        cellVertices ε η (outerNbhd (δ₀ ^ β) (fillCells ε η Θ)) ∧
      cellVertices ε η (outerNbhd (δ₀ ^ β) (fillCells ε η Θ)) ⊆ cellVertices ε η (ball 0 ρ))} ≤
      ENNReal.ofReal (M * ε) := by
  have h2βm : 0 < 2 * βm := by linarith only [hβm]
  have ha0 : 0 < a := by rw [ha_def]; exact inv_pos.2 h2βm
  have hc₄ : 0 < s₄ / 64 := by positivity
  have hc₃ : 0 < s₃ / 64 := by positivity
  have hA0 : 0 < A := by rw [hA_def]; exact div_pos (by norm_num) (mul_pos ha0 hc₄)
  have hK : 0 < K := by rw [hK_def]; exact mul_pos hA0 (Real.rpow_pos_of_pos (by positivity) _)
  have hq : 0 < q := by rw [hq_def]; linarith only [hβa, ha0]
  have h1ρ : 0 < (1 - ρ) / 8 := by linarith only [hρ1]
  have hρ4 : 0 < ρ / 4 := by linarith only [hρ]
  have hτ1 : 0 < min τ 1 := lt_min hτ one_pos
  have hC₁0 : 0 < C₁ := by rw [hC₁]; positivity
  -- the quantities of the iteration
  have hρ'0 : 0 < (1 + ρ) / 2 := by linarith only [hρ]
  set rmin := 10 * ε ^ ω₂ with hrmin_def
  set d := ε ^ κ with hd_def
  set N := ε ^ (-(ω₂ / 2)) with hN_def
  set E := Real.exp (-(s₃ / 64 * rmin ^ (1 / 4 : ℝ) * N)) with hE_def
  set B := 2 * rmin ^ (3 / 4 : ℝ) / (s₄ / 64) with hB_def
  set J := ⌈δ₀ / ε⌉₊ with hJ_def
  set X := fillCells ε η Θ with hX
  set Y := cthickening (δ₀ ^ β) X with hY
  have hεω : 0 < ε ^ ω₂ := Real.rpow_pos_of_pos hε _
  have hrmin : 0 < rmin := by rw [hrmin_def]; positivity
  have hrminτ : rmin ≤ min τ 1 := by rw [hrmin_def]; linarith only [hC2]
  have hrmin1 : rmin ≤ 1 := hrminτ.trans (min_le_right _ _)
  have hd : 0 ≤ d := by rw [hd_def]; positivity
  have hdr : d ≤ rmin := by
    have h1 := Real.rpow_le_rpow_of_exponent_ge hε hε1 hω₂κ
    rw [hd_def, hrmin_def]
    linarith only [h1, hεω]
  have hN2 : 2 ≤ N := by
    rw [hN_def, Real.rpow_neg hε.le]
    calc (2 : ℝ) = (1 / 2)⁻¹ := by norm_num
      _ ≤ (ε ^ (ω₂ / 2))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hε _) hC4
  have hN0 : 0 ≤ N := by linarith only [hN2]
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set x : ℕ → ℝ := fun n => ((n : ℝ) * ε / s₅) ^ a with hx_def
  set rr : ℕ → ℝ := fun n => max (x n) rmin with hrr_def
  set pp : ℕ → ℝ := fun n => s₄ / (1 + |Real.log (rr n)|) ^ 2 with hpp_def
  set Ψ : ℕ → ℝ := fun n => if (n : ℝ) ≤ N then max (((n : ℝ) - 1) * d) 0
    else A * x n ^ (1 / 2 : ℝ) + B * Real.log n + N * d with hΨ_def
  set G : ℕ → ℝ := fun n => if (n : ℝ) ≤ N then 0 else n * E with hG_def
  have hx0 : ∀ n, 0 ≤ x n := fun n => Real.rpow_nonneg (by positivity) _
  have hddpos : 0 < dd := lt_of_lt_of_le hτ hτdd
  have hxJ : ∀ n : ℕ, n ≤ J → x n ≤ min dd 1 := by
    intro n hn
    have h := le_rpow_of_le_ceil hε hs₅ hβm hδ₀ hτ hτdd hδ₀dd hC3 hn
    calc x n = ((n : ℝ) * ε / s₅) ^ a := rfl
      _ ≤ (min dd 1 ^ (2 * βm)) ^ a := Real.rpow_le_rpow (by positivity) h ha0.le
      _ = min dd 1 := by rw [ha_def]; exact Real.rpow_rpow_inv (le_min hddpos.le zero_le_one) h2βm.ne'
  have hrr_pos : ∀ n, 0 < rr n := fun n => lt_max_of_lt_right hrmin
  have hrr_le : ∀ n, n ≤ J → rr n ≤ min dd 1 := fun n hn =>
    max_le (hxJ n hn) (le_min (hrminτ.trans ((min_le_left _ _).trans hτdd)) hrmin1)
  have hpp0 : ∀ n, 0 ≤ pp n := fun n => div_nonneg hs₄.le (sq_nonneg _)
  have hpp1 : ∀ n, pp n < 1 := fun n =>
    lt_of_le_of_lt (div_le_self hs₄.le (one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _)))) hs₄1
  -- Lemma 6.9 for the rounds
  have habs : ∀ n : ℕ, N < n → n ≤ J → ∀ Θ' : Set ℤ,
      closure (fillCells ε η Θ') ⊆ ball 0 ((1 + ρ) / 2 / 2) →
      ball 0 s₀ ⊆ fillCells ε η Θ' → ∀ b : Fin n → ℤ, (∀ i, b i ∈ vClosure m Θ') →
        walkersLaw m b {xs | ((idlaAggregate Θ' (cellVertices ε η (thickening (rr n) (fillCells ε η Θ')))
          (List.ofFn xs) \ Θ').ncard : ℝ) ≤ pp n * n} ≤ ENNReal.ofReal E := by
    intro n hn hnJ Θ' h1 h2 b hb
    have hr1 : 10 * ε ^ ω₀ ≤ rr n := by
      have h := Real.rpow_le_rpow_of_exponent_ge hε hε1 hω₂ω₀
      refine le_trans ?_ (le_max_right (x n) rmin)
      rw [hrmin_def]
      linarith only [h]
    have hr2 : rr n ≤ dd := (hrr_le n hnJ).trans (min_le_left _ _)
    have hk : (n : ℝ) ≤ s₅ * rr n ^ (2 * βm) / ε := by
      have hxpow : x n ^ (2 * βm) = (n : ℝ) * ε / s₅ := by
        show (((n : ℝ) * ε / s₅) ^ a) ^ (2 * βm) = _
        rw [ha_def]
        exact Real.rpow_inv_rpow (by positivity) h2βm.ne'
      have hmono : x n ^ (2 * βm) ≤ rr n ^ (2 * βm) :=
        Real.rpow_le_rpow (hx0 n) (le_max_left _ _) h2βm.le
      rw [hxpow, div_le_iff₀ hs₅] at hmono
      rw [le_div_iff₀ hε]
      linarith only [hmono]
    refine (h69 (rr n) hr1 hr2 Θ' h1 h2 n b hk hb).trans (ENNReal.ofReal_le_ofReal ?_)
    apply Real.exp_le_exp.2
    have hr1' : rr n ≤ 1 := (hrr_le n hnJ).trans (min_le_right _ _)
    have hq3 := div_one_add_abs_log_sq_ge (hrr_pos n) hr1' hs₃.le
    have hrm : rmin ^ (1 / 4 : ℝ) ≤ rr n ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hrmin.le (le_max_right _ _) (by norm_num)
    have hkey : s₃ / 64 * rmin ^ (1 / 4 : ℝ) * N ≤ s₃ / (1 + |Real.log (rr n)|) ^ 2 * n :=
      mul_le_mul ((mul_le_mul_of_nonneg_left hrm hc₃.le).trans hq3) hn.le hN0 (by positivity)
    linarith only [hkey]
  -- the target region
  have hδβ : δ₀ ^ β < (1 - ρ) / 8 := by
    calc δ₀ ^ β < (((1 - ρ) / 8) ^ β⁻¹) ^ β := Real.rpow_lt_rpow hδ₀.le (hδ₀D.trans_le hDρ1) hβ0
      _ = (1 - ρ) / 8 := Real.rpow_inv_rpow h1ρ.le hβ0.ne'
  have hδβ' : δ₀ ^ β < ρ / 4 := by
    calc δ₀ ^ β < ((ρ / 4) ^ β⁻¹) ^ β := Real.rpow_lt_rpow hδ₀.le (hδ₀D.trans_le hDρ2) hβ0
      _ = ρ / 4 := Real.rpow_inv_rpow hρ4.le hβ0.ne'
  have hδβ0 : 0 ≤ δ₀ ^ β := (Real.rpow_pos_of_pos hδ₀ _).le
  have hYc : closure Y ⊆ ball 0 ((1 + ρ) / 2 / 2) :=
    closure_cthickening_subset_ball hΘ1 hδβ0 (by linarith only [hδβ, hρ1])
  have hYρ : Y ⊆ ball 0 ρ :=
    subset_closure.trans (closure_cthickening_subset_ball hΘ1 hδβ0 (by linarith only [hδβ', hρ]))
  -- the budgets
  have hB0 : 0 ≤ B := by rw [hB_def]; positivity
  have hΨ_hi : ∀ n : ℕ, Ψ n ≤ A * x n ^ (1 / 2 : ℝ) + B * Real.log n + N * d := by
    intro n
    have h1 : 0 ≤ A * x n ^ (1 / 2 : ℝ) := mul_nonneg hA0.le (Real.rpow_nonneg (hx0 n) _)
    have h2 : 0 ≤ B * Real.log n := mul_nonneg hB0 (Real.log_natCast_nonneg n)
    have h3 : 0 ≤ N * d := mul_nonneg hN0 hd
    by_cases h : (n : ℝ) ≤ N
    · have hΨe : Ψ n = max (((n : ℝ) - 1) * d) 0 := ite_eq_left h
      rw [hΨe]
      apply max_le
      · have h4 : ((n : ℝ) - 1) * d ≤ N * d := mul_le_mul_of_nonneg_right (by linarith only [h]) hd
        linarith only [h1, h2, h4]
      · linarith only [h1, h2, h3]
    · exact le_of_eq (ite_eq_right h)
  have hΨ0 : ∀ n, 0 ≤ Ψ n := by
    intro n
    by_cases h : (n : ℝ) ≤ N
    · have hΨe : Ψ n = max (((n : ℝ) - 1) * d) 0 := ite_eq_left h
      rw [hΨe]
      exact le_max_right _ _
    · have hΨe : Ψ n = A * x n ^ (1 / 2 : ℝ) + B * Real.log n + N * d := ite_eq_right h
      have h1 : 0 ≤ A * x n ^ (1 / 2 : ℝ) := mul_nonneg hA0.le (Real.rpow_nonneg (hx0 n) _)
      have h2 : 0 ≤ B * Real.log n := mul_nonneg hB0 (Real.log_natCast_nonneg n)
      have h3 : 0 ≤ N * d := mul_nonneg hN0 hd
      rw [hΨe]
      linarith only [h1, h2, h3]
  have hG0 : ∀ n, 0 ≤ G n := by
    intro n
    by_cases h : (n : ℝ) ≤ N
    · exact le_of_eq (ite_eq_left h).symm
    · have hGe : G n = n * E := ite_eq_right h
      rw [hGe]
      positivity
  have hΨ3 : ∀ n : ℕ, (n : ℝ) ≤ N → ((n : ℝ) - 1) * d ≤ Ψ n := by
    intro n hn
    have hΨe : Ψ n = max (((n : ℝ) - 1) * d) 0 := ite_eq_left hn
    rw [hΨe]
    exact le_max_left _ _
  have hΨr : ∀ n : ℕ, N < n → n ≤ J → ∀ n₁ : ℕ, (n₁ : ℝ) < (1 - pp n) * n →
      Ψ n₁ + rr n + d ≤ Ψ n := by
    intro n hn hnJ n₁ hn₁
    have hΨn : Ψ n = A * x n ^ (1 / 2 : ℝ) + B * Real.log n + N * d := ite_eq_right (not_le.2 hn)
    have hn3 : 3 ≤ n := by
      have h1 : (2 : ℝ) < n := lt_of_le_of_lt hN2 hn
      have h2 : 2 < n := by exact_mod_cast h1
      omega
    have hx1 : x n ≤ 1 := (hxJ n hnJ).trans (min_le_right _ _)
    have hp : s₄ / 64 * (max (x n) rmin) ^ (1 / 4 : ℝ) ≤ pp n :=
      div_one_add_abs_log_sq_ge (hrr_pos n) ((hrr_le n hnJ).trans (min_le_right _ _)) hs₄.le
    have hst : A * x n₁ ^ (1 / 2 : ℝ) + B * Real.log n₁ + (rr n + d) ≤
        A * x n ^ (1 / 2 : ℝ) + B * Real.log n := by
      rw [hA_def]
      exact budget_step hε hs₅ ha0 ha1 hc₄ (by linarith only [hs₄1]) hrmin hrmin1 hdr hn3 hx1 hp (hpp1 n) hn₁
    have h' := hΨ_hi n₁
    rw [hΨn]
    linarith only [hst, h']
  have hGr : ∀ n : ℕ, N < n → n ≤ J → ∀ n₁ : ℕ, (n₁ : ℝ) < (1 - pp n) * n → G n₁ + E ≤ G n := by
    intro n hn _ n₁ hn₁
    have hGn : G n = n * E := ite_eq_right (not_le.2 hn)
    have hG₁ : G n₁ ≤ n₁ * E := by
      by_cases h : (n₁ : ℝ) ≤ N
      · have hGe : G n₁ = 0 := ite_eq_left h
        rw [hGe]
        positivity
      · exact le_of_eq (ite_eq_right h)
    have hlt : (n₁ : ℝ) + 1 ≤ n := by
      have h0 := mul_nonneg (hpp0 n) (Nat.cast_nonneg n)
      have h1 : (n₁ : ℝ) < n := by linarith only [hn₁, h0]
      have h2 : n₁ < n := by exact_mod_cast h1
      exact_mod_cast h2
    have h3 := mul_le_mul_of_nonneg_right hlt hE0
    rw [hGn]
    linarith only [hG₁, h3]
  -- the number of walkers
  have hjJ : (j : ℝ) - 1 < δ₀ / ε := by
    have hJ : (J : ℝ) < δ₀ / ε + 1 := Nat.ceil_lt_add_one (by positivity)
    have h : (j : ℝ) ≤ J := by exact_mod_cast hj
    linarith only [hJ, h]
  have hδ₀1 : δ₀ ≤ 1 := hδ₀D.le.trans hD1
  have hj2 : (j : ℝ) ≤ 2 / ε := by
    have h1 : δ₀ / ε ≤ 1 / ε := div_le_div_of_nonneg_right hδ₀1 hε.le
    have h3 : 2 / ε = 1 / ε + 1 / ε := by ring
    have h2 : 1 ≤ 1 / ε := by
      rw [le_div_iff₀ hε]
      linarith only [hε1]
    linarith only [h1, h2, h3, hjJ]
  -- the spread budget at `j`
  have hΨj : Ψ j ≤ δ₀ ^ β := by
    by_cases hjN : (j : ℝ) ≤ N
    · have hΨe : Ψ j = max (((j : ℝ) - 1) * d) 0 := ite_eq_left hjN
      rw [hΨe]
      exact max_le (stage3_bound hε hε1 hδ₀ (by positivity : 0 < ω₂ / 2) hβ0
        (by linarith only [hβa, ha1]) (by linarith only [hβω, hω₂κ, hω₂0]) hjJ hjN) hδβ0
    · have hΨe : Ψ j = A * x j ^ (1 / 2 : ℝ) + B * Real.log j + N * d := ite_eq_right hjN
      push Not at hjN
      rw [hΨe]
      have hδε : ε ≤ δ₀ := by
        have h1 : (1 : ℝ) < δ₀ / ε := by linarith only [hjJ, hjN, hN2]
        rw [lt_div_iff₀ hε] at h1
        linarith only [h1]
      have hxj : x j ≤ (2 * δ₀ / s₅) ^ a := by
        apply Real.rpow_le_rpow (by positivity) _ ha0.le
        apply div_le_div_of_nonneg_right _ hs₅.le
        have h1 := mul_lt_mul_of_pos_right hjJ hε
        rw [sub_mul, one_mul, div_mul_cancel₀ _ hε.ne'] at h1
        linarith only [h1, hδε]
      have hmain : A * x j ^ (1 / 2 : ℝ) ≤ δ₀ ^ β / 2 := by
        have h1 : x j ^ (1 / 2 : ℝ) ≤ (2 / s₅) ^ (a / 2) * (δ₀ ^ β * δ₀ ^ q) := by
          calc x j ^ (1 / 2 : ℝ) ≤ ((2 * δ₀ / s₅) ^ a) ^ (1 / 2 : ℝ) :=
                Real.rpow_le_rpow (hx0 j) hxj (by norm_num)
            _ = (2 * δ₀ / s₅) ^ (a / 2) := by
                rw [← Real.rpow_mul (by positivity)]
                ring_nf
            _ = (2 / s₅) ^ (a / 2) * δ₀ ^ (a / 2) := by
                rw [show 2 * δ₀ / s₅ = 2 / s₅ * δ₀ by ring, Real.mul_rpow (by positivity) hδ₀.le]
            _ = (2 / s₅) ^ (a / 2) * (δ₀ ^ β * δ₀ ^ q) := by
                rw [← Real.rpow_add hδ₀, hq_def]
                ring_nf
        have hδq : δ₀ ^ q ≤ 1 / (2 * K) := by
          calc δ₀ ^ q ≤ ((1 / (2 * K)) ^ q⁻¹) ^ q := Real.rpow_le_rpow hδ₀.le (hδ₀D.le.trans hDK) hq.le
            _ = 1 / (2 * K) := Real.rpow_inv_rpow (by positivity) hq.ne'
        calc A * x j ^ (1 / 2 : ℝ) ≤ A * ((2 / s₅) ^ (a / 2) * (δ₀ ^ β * δ₀ ^ q)) :=
              mul_le_mul_of_nonneg_left h1 hA0.le
          _ = K * δ₀ ^ q * δ₀ ^ β := by
              rw [hK_def]
              ring
          _ ≤ K * (1 / (2 * K)) * δ₀ ^ β := by gcongr
          _ = δ₀ ^ β / 2 := by
              field_simp
      have hlogt : B * Real.log j ≤ C₁ * ε ^ (ω₂ / 2) := by
        rw [hC₁]
        exact log_term_bound hε hω₂0 hc₄ hj2
      have hNd : N * d ≤ ε ^ (ω₂ / 2) := by
        rw [hN_def, hd_def, ← Real.rpow_add hε]
        exact Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith only [hω₂κ])
      have hsmall : (C₁ + 1) * ε ^ (ω₂ / 2) ≤ ε ^ β / 4 := by
        have e1 : ε ^ (ω₂ / 2) = ε ^ (ω₂ / 2 - β) * ε ^ β := by
          rw [← Real.rpow_add hε]
          ring_nf
        have hC : C₁ + 1 ≠ 0 := by positivity
        have h' : (C₁ + 1) * ε ^ (ω₂ / 2 - β) ≤ 1 / 4 := by
          calc (C₁ + 1) * ε ^ (ω₂ / 2 - β) ≤ (C₁ + 1) * (1 / (4 * (C₁ + 1))) :=
                mul_le_mul_of_nonneg_left hC5 (by positivity)
            _ = 1 / 4 := by
                field_simp
        have h2 := mul_le_mul_of_nonneg_right h' (Real.rpow_pos_of_pos hε β).le
        calc (C₁ + 1) * ε ^ (ω₂ / 2) = (C₁ + 1) * ε ^ (ω₂ / 2 - β) * ε ^ β := by
              rw [e1]
              ring
          _ ≤ 1 / 4 * ε ^ β := h2
          _ = ε ^ β / 4 := by ring
      have hεδ : ε ^ β ≤ δ₀ ^ β := Real.rpow_le_rpow hε.le hδε hβ0.le
      linarith only [hmain, hlogt, hNd, hsmall, hεδ, hδβ0]
  -- the failure budget at `j`
  have hGj : G j ≤ M * ε := by
    by_cases hjN : (j : ℝ) ≤ N
    · have hGe : G j = 0 := ite_eq_left hjN
      rw [hGe, hM]
      positivity
    · have hGe : G j = j * E := ite_eq_right hjN
      rw [hGe, hM]
      exact failure_bound hε hε1 hω₂0 hc₃ hj2
  -- the iteration
  have hcore := core_induction (ρ' := (1 + ρ) / 2) (s₀ := s₀) hab hsrw hη hε.le hd hN0 hE0 hcell hdiam hΘ2
    hYc hρ'0 J rr pp Ψ G habs hrr_pos hpp0 hpp1 hΨ0 hG0 hΨ3 hΨr hGr j hj Θ subset_rfl a' ha'
    (cthickening_mono hΨj _)
  have hsecond : cellVertices ε η (outerNbhd (δ₀ ^ β) X) ⊆ cellVertices ε η (ball 0 ρ) :=
    cellVertices_mono' hYρ
  refine le_trans (measure_mono ?_) (hcore.trans (ENNReal.ofReal_le_ofReal hGj))
  intro xs hxs h
  exact hxs ⟨h, hsecond⟩

/-- **`QuenchedIterationStep` holds.** -/
theorem quenchedIterationStep : QuenchedIterationStep := by
  intro ρ βm ω₀ κ hρ hρ1 hβm hω₀ hκ
  have hω₂0 : 0 < min ω₀ κ := lt_min hω₀ hκ
  have h2βm : 0 < 2 * βm := by linarith only [hβm]
  have ha0 : 0 < (2 * βm)⁻¹ := inv_pos.2 h2βm
  have ha1 : (2 * βm)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by linarith only [hβm])
  have hβ0 : 0 < min ((2 * βm)⁻¹ / 4) (min ω₀ κ / 8) := lt_min (by positivity) (by positivity)
  refine ⟨min ((2 * βm)⁻¹ / 4) (min ω₀ κ / 8), hβ0,
    fun s₀ s₃ s₄ s₅ hs₀ hs₃ hs₄ hs₄1 hs₅ hs₅1 => ?_⟩
  have hc₄ : 0 < s₄ / 64 := by positivity
  set a := (2 * βm)⁻¹ with ha_def
  set β := min (a / 4) (min ω₀ κ / 8) with hβ_def
  set A := 8 / (a * (s₄ / 64)) with hA_def
  have hA0 : 0 < A := div_pos (by norm_num) (mul_pos ha0 hc₄)
  set K := A * (2 / s₅) ^ (a / 2) with hK_def
  have hK : 0 < K := mul_pos hA0 (Real.rpow_pos_of_pos (by positivity) _)
  set q := a / 2 - β with hq_def
  have hq : 0 < q := by
    have : β ≤ a / 4 := min_le_left _ _
    linarith only [this, ha0, hq_def]
  have h1ρ : 0 < (1 - ρ) / 8 := by linarith only [hρ1]
  have hρ4 : 0 < ρ / 4 := by linarith only [hρ]
  refine ⟨min (min 1 ((1 / (2 * K)) ^ q⁻¹)) (min (((1 - ρ) / 8) ^ β⁻¹) ((ρ / 4) ^ β⁻¹)),
    lt_min (lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _))
      (lt_min (Real.rpow_pos_of_pos h1ρ _) (Real.rpow_pos_of_pos hρ4 _)), fun τ hτ => ?_⟩
  have hτ1 : 0 < min τ 1 := lt_min hτ one_pos
  set M := 2 * ((⌈8 / min ω₀ κ⌉₊).factorial : ℝ) / (s₃ / 64) ^ ⌈8 / min ω₀ κ⌉₊ with hM
  refine ⟨fun ε => ENNReal.ofReal (M * ε), ?_, ?_⟩
  · have hc : Continuous fun ε : ℝ => M * ε := continuous_const.mul continuous_id
    have h : Tendsto (fun ε : ℝ => M * ε) (𝓝[>] 0) (𝓝 0) := by
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    simpa using ENNReal.tendsto_ofReal h
  set C₁ := 80 * 2 ^ (min ω₀ κ / 4) / (s₄ / 64 * min ω₀ κ) with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  have hβω : β ≤ min ω₀ κ / 8 := min_le_right _ _
  filter_upwards [self_mem_nhdsWithin, eventually_le_const (c := 1) one_pos,
    eventually_rpow_le (s := min ω₀ κ) hω₂0 (c := min τ 1 / 10) (div_pos hτ1 (by norm_num)),
    eventually_le_const (c := s₅ * min τ 1 ^ (2 * βm) / 2)
      (div_pos (mul_pos hs₅ (Real.rpow_pos_of_pos hτ1 _)) two_pos),
    eventually_rpow_le (s := min ω₀ κ / 2) (by positivity) (c := 1 / 2) (by norm_num),
    eventually_rpow_le (s := min ω₀ κ / 2 - β) (by linarith only [hβω, hω₂0])
      (c := 1 / (4 * (C₁ + 1))) (by positivity)]
    with ε hε0 hε1 hC2 hC3 hC4 hC5
  intro m η dd hτdd hη hab hsrw h69 hcell hdiam Θ hΘ1 hΘ2 δ₀ hδ₀ hδ₀D hδ₀dd j hj a' ha'
  exact quenched_env hρ hρ1 hβm hω₂0 (min_le_left _ _) (min_le_right _ _) rfl ha1 hβ0 (min_le_left _ _) hβω
    hs₃ hs₄ hs₄1 hs₅ rfl rfl rfl ((min_le_left _ _).trans (min_le_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _)) ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) hτ rfl rfl hε0 hε1 hC2 hC3 hC4 hC5 hτdd hη hab hsrw h69
    hcell hdiam hΘ1 hΘ2 hδ₀ hδ₀D hδ₀dd hj ha'

end IterativeBound

end MatedCRT
